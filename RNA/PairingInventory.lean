module

public import RNA.SequenceCertificate

@[expose] public section

set_option autoImplicit false

/-!
# Nucleotide inventory and maximum pair count

This file counts the four nucleotide classes in the sequence assigned by a
proper coloring.  It also gives the matching-theoretic injection which sends
every compatible pair to the unique `U` or `C` that it consumes.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-! ## Finite nucleotide and color classes -/

/-- Positions carrying one specified nucleotide. -/
abbrev NucleotidePosition (w : Sequence n) (x : Nucleotide) :=
  {i : Fin n // w i = x}

/-- Number of occurrences of a nucleotide in a complete sequence. -/
def nucleotideCount (w : Sequence n) (x : Nucleotide) : Nat :=
  Fintype.card (NucleotidePosition w x)

/-- The subtype of grey target pairs. -/
abbrev GreyPair (chi : Coloring T) :=
  {p : PairedNode T // chi p = Color.grey}

/-- The subtype of non-grey target pairs. -/
abbrev NonGreyPair (chi : Coloring T) :=
  {p : PairedNode T // chi p ≠ Color.grey}

/-- Number of grey target pairs. -/
def greyPairCount (chi : Coloring T) : Nat :=
  Fintype.card (GreyPair chi)

/-- Number of black or white target pairs. -/
def nonGreyPairCount (chi : Coloring T) : Nat :=
  Fintype.card (NonGreyPair chi)

/-- Number of target-unpaired positions. -/
def targetUnpairedCount (T : SecondaryStructure n) : Nat :=
  Fintype.card (UnpairedPosition T)

/-- Subtype counts agree with the usual filtered finite-position count. -/
theorem nucleotideCount_eq_filter_card (w : Sequence n) (x : Nucleotide) :
    nucleotideCount w x =
      ((Finset.univ : Finset (Fin n)).filter (fun i => w i = x)).card := by
  simpa only [nucleotideCount, NucleotidePosition] using
    Fintype.card_subtype (fun i : Fin n => w i = x)

/-- Every target pair is uniquely either grey or non-grey. -/
def pairColorPartitionEquiv (chi : Coloring T) :
    PairedNode T ≃ GreyPair chi ⊕ NonGreyPair chi where
  toFun p :=
    if h : chi p = Color.grey then Sum.inl ⟨p, h⟩ else Sum.inr ⟨p, h⟩
  invFun q := q.elim Subtype.val Subtype.val
  left_inv p := by simp only; split <;> rfl
  right_inv q := by
    cases q with
    | inl g => simp [g.property]
    | inr q => simp [q.property]

/-- Pair count is the sum of grey and non-grey pair counts. -/
theorem pairCount_eq_greyPairCount_add_nonGreyPairCount (chi : Coloring T) :
    pairCount T = greyPairCount chi + nonGreyPairCount chi := by
  calc
    pairCount T = Fintype.card (PairedNode T) := by
      simp [pairCount, PairedNode]
    _ = Fintype.card (GreyPair chi ⊕ NonGreyPair chi) :=
      Fintype.card_congr (pairColorPartitionEquiv chi)
    _ = greyPairCount chi + nonGreyPairCount chi := by
      simp [greyPairCount, nonGreyPairCount]

/-! ## Explicit nucleotide sources in the assigned sequence -/

private theorem grey_left_eq_U_of_ne_A
    (chi : Coloring T) (hProper : ProperColoring chi)
    (g : GreyPair chi)
    (hA : leftLetterOfProperColoring chi hProper g.val ≠ Nucleotide.A) :
    leftLetterOfProperColoring chi hProper g.val = Nucleotide.U :=
  (leftLetter_grey_mem_AU chi hProper g.val g.property).resolve_left hA

/-- The unique `U` endpoint contributed by a grey target pair. -/
noncomputable def uPositionOfGreyPair
    (chi : Coloring T) (hProper : ProperColoring chi) :
    GreyPair chi → NucleotidePosition
      (sequenceOfProperColoring chi hProper) Nucleotide.U :=
  fun g =>
    if hA : leftLetterOfProperColoring chi hProper g.val = Nucleotide.A then
      ⟨g.val.val.right, by simp [sequenceOfProperColoring_right, hA]⟩
    else
      ⟨g.val.val.left, by
        rw [sequenceOfProperColoring_left]
        exact grey_left_eq_U_of_ne_A chi hProper g hA⟩

/-- The selected `U` position is an actual endpoint of its grey pair. -/
theorem uPositionOfGreyPair_incident
    (chi : Coloring T) (hProper : ProperColoring chi) (g : GreyPair chi) :
    g.val.val.Incident (uPositionOfGreyPair chi hProper g).val := by
  unfold uPositionOfGreyPair
  split <;> simp [Arc.Incident]

/-- The unique `A` endpoint contributed by a grey target pair. -/
noncomputable def aPositionOfGreyPair
    (chi : Coloring T) (hProper : ProperColoring chi) :
    GreyPair chi → NucleotidePosition
      (sequenceOfProperColoring chi hProper) Nucleotide.A :=
  fun g =>
    if hA : leftLetterOfProperColoring chi hProper g.val = Nucleotide.A then
      ⟨g.val.val.left, by simp [sequenceOfProperColoring_left, hA]⟩
    else
      ⟨g.val.val.right, by
        have hU := grey_left_eq_U_of_ne_A chi hProper g hA
        simp [sequenceOfProperColoring_right, hU]⟩

/-- The selected grey-pair `A` position is an actual endpoint. -/
theorem aPositionOfGreyPair_incident
    (chi : Coloring T) (hProper : ProperColoring chi) (g : GreyPair chi) :
    g.val.val.Incident (aPositionOfGreyPair chi hProper g).val := by
  unfold aPositionOfGreyPair
  split <;> simp [Arc.Incident]

/-- The `G` endpoint contributed by a non-grey target pair. -/
noncomputable def gPositionOfNonGreyPair
    (chi : Coloring T) (hProper : ProperColoring chi) :
    NonGreyPair chi → NucleotidePosition
      (sequenceOfProperColoring chi hProper) Nucleotide.G :=
  fun p =>
    match h : chi p.val with
    | Color.black =>
        ⟨p.val.val.left,
          sequenceOfProperColoring_black_left chi hProper p.val h⟩
    | Color.white =>
        ⟨p.val.val.right,
          sequenceOfProperColoring_white_right chi hProper p.val h⟩
    | Color.grey => False.elim (p.property h)

/-- The selected non-grey-pair `G` position is an actual endpoint. -/
theorem gPositionOfNonGreyPair_incident
    (chi : Coloring T) (hProper : ProperColoring chi) (p : NonGreyPair chi) :
    p.val.val.Incident (gPositionOfNonGreyPair chi hProper p).val := by
  unfold gPositionOfNonGreyPair
  split
  · exact p.val.val.incident_left
  · exact p.val.val.incident_right
  · rename_i hgrey
    exact False.elim (p.property hgrey)

/-- The `C` endpoint contributed by a non-grey target pair. -/
noncomputable def cPositionOfNonGreyPair
    (chi : Coloring T) (hProper : ProperColoring chi) :
    NonGreyPair chi → NucleotidePosition
      (sequenceOfProperColoring chi hProper) Nucleotide.C :=
  fun p =>
    match h : chi p.val with
    | Color.black =>
        ⟨p.val.val.right,
          sequenceOfProperColoring_black_right chi hProper p.val h⟩
    | Color.white =>
        ⟨p.val.val.left,
          sequenceOfProperColoring_white_left chi hProper p.val h⟩
    | Color.grey => False.elim (p.property h)

/-- The selected non-grey-pair `C` position is an actual endpoint. -/
theorem cPositionOfNonGreyPair_incident
    (chi : Coloring T) (hProper : ProperColoring chi) (p : NonGreyPair chi) :
    p.val.val.Incident (cPositionOfNonGreyPair chi hProper p).val := by
  unfold cPositionOfNonGreyPair
  split
  · exact p.val.val.incident_right
  · exact p.val.val.incident_left
  · rename_i hgrey
    exact False.elim (p.property hgrey)

private theorem greyPair_source_injective
    (chi : Coloring T) {w : Sequence n}
    (f : GreyPair chi → {i : Fin n // w i = Nucleotide.U})
    (hincident : ∀ g : GreyPair chi, g.val.val.Incident (f g).val) :
    Function.Injective f := by
  intro g q hgq
  apply Subtype.ext
  apply Subtype.ext
  apply T.eq_of_mem_of_incident g.val.property q.val.property (hincident g)
  have hpos := congrArg Subtype.val hgq
  rw [hpos]
  exact hincident q

theorem uPositionOfGreyPair_injective
    (chi : Coloring T) (hProper : ProperColoring chi) :
    Function.Injective (uPositionOfGreyPair chi hProper) :=
  greyPair_source_injective chi (uPositionOfGreyPair chi hProper)
    (uPositionOfGreyPair_incident chi hProper)

private theorem nonGreyPair_source_injective
    (chi : Coloring T) {x : Nucleotide} {w : Sequence n}
    (f : NonGreyPair chi → {i : Fin n // w i = x})
    (hincident : ∀ p : NonGreyPair chi, p.val.val.Incident (f p).val) :
    Function.Injective f := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  apply T.eq_of_mem_of_incident p.val.property q.val.property (hincident p)
  have hpos := congrArg Subtype.val hpq
  rw [hpos]
  exact hincident q

theorem gPositionOfNonGreyPair_injective
    (chi : Coloring T) (hProper : ProperColoring chi) :
    Function.Injective (gPositionOfNonGreyPair chi hProper) :=
  nonGreyPair_source_injective chi (gPositionOfNonGreyPair chi hProper)
    (gPositionOfNonGreyPair_incident chi hProper)

theorem cPositionOfNonGreyPair_injective
    (chi : Coloring T) (hProper : ProperColoring chi) :
    Function.Injective (cPositionOfNonGreyPair chi hProper) :=
  nonGreyPair_source_injective chi (cPositionOfNonGreyPair chi hProper)
    (cPositionOfNonGreyPair_incident chi hProper)

theorem uPositionOfGreyPair_surjective
    (chi : Coloring T) (hProper : ProperColoring chi) :
    Function.Surjective (uPositionOfGreyPair chi hProper) := by
  intro u
  let w := sequenceOfProperColoring chi hProper
  generalize hr : positionRoleAt T u.val = r
  have hpos := positionOfRole_positionRoleAt T u.val
  rw [hr] at hpos
  cases r with
  | inl a =>
      exfalso
      have ha := sequenceOfProperColoring_unpaired chi hProper a
      have hwu := congrArg w hpos
      change sequenceOfProperColoring chi hProper a.val =
        sequenceOfProperColoring chi hProper u.val at hwu
      rw [ha, u.property] at hwu
      cases hwu
  | inr ps =>
      rcases ps with ⟨p, side⟩
      cases side with
      | left =>
          change p.val.left = u.val at hpos
          cases hp : chi p with
          | black =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_black_left chi hProper p hp
              rw [hpos, u.property] at hletter
              cases hletter
          | white =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_white_left chi hProper p hp
              rw [hpos, u.property] at hletter
              cases hletter
          | grey =>
              have hleftU :
                  sequenceOfProperColoring chi hProper p.val.left =
                    Nucleotide.U := by
                rw [hpos]
                exact u.property
              have hnotA :
                  leftLetterOfProperColoring chi hProper p ≠ Nucleotide.A := by
                intro hA
                rw [sequenceOfProperColoring_left, hA] at hleftU
                cases hleftU
              refine ⟨⟨p, hp⟩, ?_⟩
              apply Subtype.ext
              simp [uPositionOfGreyPair, hnotA, hpos]
      | right =>
          change p.val.right = u.val at hpos
          cases hp : chi p with
          | black =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_black_right chi hProper p hp
              rw [hpos, u.property] at hletter
              cases hletter
          | white =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_white_right chi hProper p hp
              rw [hpos, u.property] at hletter
              cases hletter
          | grey =>
              have hrightU :
                  sequenceOfProperColoring chi hProper p.val.right =
                    Nucleotide.U := by
                rw [hpos]
                exact u.property
              have hleftA :
                  leftLetterOfProperColoring chi hProper p = Nucleotide.A := by
                rcases leftLetter_grey_mem_AU chi hProper p hp with hA | hU
                · exact hA
                · exfalso
                  simp [sequenceOfProperColoring_right, hU] at hrightU
              refine ⟨⟨p, hp⟩, ?_⟩
              apply Subtype.ext
              simp [uPositionOfGreyPair, hleftA, hpos]

/-- Grey target pairs are in explicit bijection with all and only `U`
positions of the assigned sequence. -/
noncomputable def greyPairEquivUPosition
    (chi : Coloring T) (hProper : ProperColoring chi) :
    GreyPair chi ≃ NucleotidePosition
      (sequenceOfProperColoring chi hProper) Nucleotide.U :=
  Equiv.ofBijective (uPositionOfGreyPair chi hProper)
    ⟨uPositionOfGreyPair_injective chi hProper,
      uPositionOfGreyPair_surjective chi hProper⟩

/-- Exact `U` count of the assigned sequence. -/
theorem nucleotideCount_U_sequenceOfProperColoring
    (chi : Coloring T) (hProper : ProperColoring chi) :
    nucleotideCount (sequenceOfProperColoring chi hProper) Nucleotide.U =
      greyPairCount chi := by
  exact (Fintype.card_congr (greyPairEquivUPosition chi hProper)).symm

/-- Every `U` position of the assigned sequence belongs to one unique grey
target pair. -/
theorem U_position_has_unique_grey_source
    (chi : Coloring T) (hProper : ProperColoring chi) (j : Fin n)
    (hj : sequenceOfProperColoring chi hProper j = Nucleotide.U) :
    ∃! g : PairedNode T, chi g = Color.grey ∧ g.val.Incident j := by
  let u : NucleotidePosition
      (sequenceOfProperColoring chi hProper) Nucleotide.U := ⟨j, hj⟩
  let g : GreyPair chi := (greyPairEquivUPosition chi hProper).symm u
  have hmap : uPositionOfGreyPair chi hProper g = u :=
    (greyPairEquivUPosition chi hProper).apply_symm_apply u
  have hincident := uPositionOfGreyPair_incident chi hProper g
  rw [hmap] at hincident
  refine ⟨g.val, ⟨g.property, hincident⟩, ?_⟩
  intro q hq
  apply Subtype.ext
  exact T.eq_of_mem_of_incident q.property g.val.property hq.2 hincident

@[simp] theorem gPositionOfNonGreyPair_val_of_black
    (chi : Coloring T) (hProper : ProperColoring chi) (p : NonGreyPair chi)
    (hp : chi p.val = Color.black) :
    (gPositionOfNonGreyPair chi hProper p).val = p.val.val.left := by
  unfold gPositionOfNonGreyPair
  split <;> simp_all

@[simp] theorem gPositionOfNonGreyPair_val_of_white
    (chi : Coloring T) (hProper : ProperColoring chi) (p : NonGreyPair chi)
    (hp : chi p.val = Color.white) :
    (gPositionOfNonGreyPair chi hProper p).val = p.val.val.right := by
  unfold gPositionOfNonGreyPair
  split <;> simp_all

@[simp] theorem cPositionOfNonGreyPair_val_of_black
    (chi : Coloring T) (hProper : ProperColoring chi) (p : NonGreyPair chi)
    (hp : chi p.val = Color.black) :
    (cPositionOfNonGreyPair chi hProper p).val = p.val.val.right := by
  unfold cPositionOfNonGreyPair
  split <;> simp_all

@[simp] theorem cPositionOfNonGreyPair_val_of_white
    (chi : Coloring T) (hProper : ProperColoring chi) (p : NonGreyPair chi)
    (hp : chi p.val = Color.white) :
    (cPositionOfNonGreyPair chi hProper p).val = p.val.val.left := by
  unfold cPositionOfNonGreyPair
  split <;> simp_all

theorem gPositionOfNonGreyPair_surjective
    (chi : Coloring T) (hProper : ProperColoring chi) :
    Function.Surjective (gPositionOfNonGreyPair chi hProper) := by
  intro g
  let w := sequenceOfProperColoring chi hProper
  generalize hr : positionRoleAt T g.val = r
  have hpos := positionOfRole_positionRoleAt T g.val
  rw [hr] at hpos
  cases r with
  | inl a =>
      exfalso
      have ha := sequenceOfProperColoring_unpaired chi hProper a
      have hw := congrArg w hpos
      change sequenceOfProperColoring chi hProper a.val =
        sequenceOfProperColoring chi hProper g.val at hw
      rw [ha, g.property] at hw
      cases hw
  | inr ps =>
      rcases ps with ⟨p, side⟩
      cases side with
      | left =>
          change p.val.left = g.val at hpos
          cases hp : chi p with
          | black =>
              let q : NonGreyPair chi := ⟨p, by simp [hp]⟩
              refine ⟨q, ?_⟩
              apply Subtype.ext
              exact (gPositionOfNonGreyPair_val_of_black chi hProper q hp).trans
                hpos
          | white =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_white_left chi hProper p hp
              rw [hpos, g.property] at hletter
              cases hletter
          | grey =>
              exfalso
              have hleftG :
                  sequenceOfProperColoring chi hProper p.val.left =
                    Nucleotide.G := by
                rw [hpos]
                exact g.property
              rcases sequenceOfProperColoring_grey_left chi hProper p hp with
                hA | hU <;> simp_all
      | right =>
          change p.val.right = g.val at hpos
          cases hp : chi p with
          | black =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_black_right chi hProper p hp
              rw [hpos, g.property] at hletter
              cases hletter
          | white =>
              let q : NonGreyPair chi := ⟨p, by simp [hp]⟩
              refine ⟨q, ?_⟩
              apply Subtype.ext
              exact (gPositionOfNonGreyPair_val_of_white chi hProper q hp).trans
                hpos
          | grey =>
              exfalso
              have hrightG :
                  sequenceOfProperColoring chi hProper p.val.right =
                    Nucleotide.G := by
                rw [hpos]
                exact g.property
              rcases sequenceOfProperColoring_grey_left chi hProper p hp with
                hA | hU
              · rw [sequenceOfProperColoring_right_eq_comp_left, hA] at hrightG
                cases hrightG
              · rw [sequenceOfProperColoring_right_eq_comp_left, hU] at hrightG
                cases hrightG

theorem cPositionOfNonGreyPair_surjective
    (chi : Coloring T) (hProper : ProperColoring chi) :
    Function.Surjective (cPositionOfNonGreyPair chi hProper) := by
  intro c
  let w := sequenceOfProperColoring chi hProper
  generalize hr : positionRoleAt T c.val = r
  have hpos := positionOfRole_positionRoleAt T c.val
  rw [hr] at hpos
  cases r with
  | inl a =>
      exfalso
      have ha := sequenceOfProperColoring_unpaired chi hProper a
      have hw := congrArg w hpos
      change sequenceOfProperColoring chi hProper a.val =
        sequenceOfProperColoring chi hProper c.val at hw
      rw [ha, c.property] at hw
      cases hw
  | inr ps =>
      rcases ps with ⟨p, side⟩
      cases side with
      | left =>
          change p.val.left = c.val at hpos
          cases hp : chi p with
          | black =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_black_left chi hProper p hp
              rw [hpos, c.property] at hletter
              cases hletter
          | white =>
              let q : NonGreyPair chi := ⟨p, by simp [hp]⟩
              refine ⟨q, ?_⟩
              apply Subtype.ext
              exact (cPositionOfNonGreyPair_val_of_white chi hProper q hp).trans
                hpos
          | grey =>
              exfalso
              have hleftC :
                  sequenceOfProperColoring chi hProper p.val.left =
                    Nucleotide.C := by
                rw [hpos]
                exact c.property
              rcases sequenceOfProperColoring_grey_left chi hProper p hp with
                hA | hU <;> simp_all
      | right =>
          change p.val.right = c.val at hpos
          cases hp : chi p with
          | black =>
              let q : NonGreyPair chi := ⟨p, by simp [hp]⟩
              refine ⟨q, ?_⟩
              apply Subtype.ext
              exact (cPositionOfNonGreyPair_val_of_black chi hProper q hp).trans
                hpos
          | white =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_white_right chi hProper p hp
              rw [hpos, c.property] at hletter
              cases hletter
          | grey =>
              exfalso
              have hrightC :
                  sequenceOfProperColoring chi hProper p.val.right =
                    Nucleotide.C := by
                rw [hpos]
                exact c.property
              rcases sequenceOfProperColoring_grey_left chi hProper p hp with
                hA | hU
              · rw [sequenceOfProperColoring_right_eq_comp_left, hA] at hrightC
                cases hrightC
              · rw [sequenceOfProperColoring_right_eq_comp_left, hU] at hrightC
                cases hrightC

/-- Non-grey target pairs are in explicit bijection with `G` positions. -/
noncomputable def nonGreyPairEquivGPosition
    (chi : Coloring T) (hProper : ProperColoring chi) :
    NonGreyPair chi ≃ NucleotidePosition
      (sequenceOfProperColoring chi hProper) Nucleotide.G :=
  Equiv.ofBijective (gPositionOfNonGreyPair chi hProper)
    ⟨gPositionOfNonGreyPair_injective chi hProper,
      gPositionOfNonGreyPair_surjective chi hProper⟩

/-- Non-grey target pairs are in explicit bijection with `C` positions. -/
noncomputable def nonGreyPairEquivCPosition
    (chi : Coloring T) (hProper : ProperColoring chi) :
    NonGreyPair chi ≃ NucleotidePosition
      (sequenceOfProperColoring chi hProper) Nucleotide.C :=
  Equiv.ofBijective (cPositionOfNonGreyPair chi hProper)
    ⟨cPositionOfNonGreyPair_injective chi hProper,
      cPositionOfNonGreyPair_surjective chi hProper⟩

/-- Exact `G` count of the assigned sequence. -/
theorem nucleotideCount_G_sequenceOfProperColoring
    (chi : Coloring T) (hProper : ProperColoring chi) :
    nucleotideCount (sequenceOfProperColoring chi hProper) Nucleotide.G =
      nonGreyPairCount chi := by
  exact (Fintype.card_congr (nonGreyPairEquivGPosition chi hProper)).symm

/-- Exact `C` count of the assigned sequence. -/
theorem nucleotideCount_C_sequenceOfProperColoring
    (chi : Coloring T) (hProper : ProperColoring chi) :
    nucleotideCount (sequenceOfProperColoring chi hProper) Nucleotide.C =
      nonGreyPairCount chi := by
  exact (Fintype.card_congr (nonGreyPairEquivCPosition chi hProper)).symm

/-- The `A` positions supplied either by a grey pair or by a target-unpaired
position. -/
noncomputable def aPositionSource
    (chi : Coloring T) (hProper : ProperColoring chi) :
    GreyPair chi ⊕ UnpairedPosition T →
      NucleotidePosition
        (sequenceOfProperColoring chi hProper) Nucleotide.A
  | Sum.inl g => aPositionOfGreyPair chi hProper g
  | Sum.inr u =>
      ⟨u.val, sequenceOfProperColoring_unpaired chi hProper u⟩

@[simp] theorem aPositionOfGreyPair_val_of_left_A
    (chi : Coloring T) (hProper : ProperColoring chi) (g : GreyPair chi)
    (hA : leftLetterOfProperColoring chi hProper g.val = Nucleotide.A) :
    (aPositionOfGreyPair chi hProper g).val = g.val.val.left := by
  simp [aPositionOfGreyPair, hA]

@[simp] theorem aPositionOfGreyPair_val_of_left_ne_A
    (chi : Coloring T) (hProper : ProperColoring chi) (g : GreyPair chi)
    (hA : leftLetterOfProperColoring chi hProper g.val ≠ Nucleotide.A) :
    (aPositionOfGreyPair chi hProper g).val = g.val.val.right := by
  simp [aPositionOfGreyPair, hA]

theorem aPositionSource_injective
    (chi : Coloring T) (hProper : ProperColoring chi) :
    Function.Injective (aPositionSource chi hProper) := by
  intro r s hrs
  cases r with
  | inl g =>
      cases s with
      | inl q =>
          apply congrArg Sum.inl
          apply Subtype.ext
          apply Subtype.ext
          apply T.eq_of_mem_of_incident g.val.property q.val.property
            (aPositionOfGreyPair_incident chi hProper g)
          have hpos := congrArg Subtype.val hrs
          change (aPositionOfGreyPair chi hProper g).val =
            (aPositionOfGreyPair chi hProper q).val at hpos
          rw [hpos]
          exact aPositionOfGreyPair_incident chi hProper q
      | inr u =>
          exfalso
          apply u.property
          refine ⟨g.val.val, g.val.property, ?_⟩
          have hinc := aPositionOfGreyPair_incident chi hProper g
          have hpos := congrArg Subtype.val hrs
          change (aPositionOfGreyPair chi hProper g).val = u.val at hpos
          rw [hpos] at hinc
          exact hinc
  | inr u =>
      cases s with
      | inl g =>
          exfalso
          apply u.property
          refine ⟨g.val.val, g.val.property, ?_⟩
          have hinc := aPositionOfGreyPair_incident chi hProper g
          have hpos := congrArg Subtype.val hrs
          change u.val = (aPositionOfGreyPair chi hProper g).val at hpos
          rw [← hpos] at hinc
          exact hinc
      | inr v =>
          apply congrArg Sum.inr
          apply Subtype.ext
          have hpos := congrArg Subtype.val hrs
          change u.val = v.val at hpos
          exact hpos

theorem aPositionSource_surjective
    (chi : Coloring T) (hProper : ProperColoring chi) :
    Function.Surjective (aPositionSource chi hProper) := by
  intro aPos
  let w := sequenceOfProperColoring chi hProper
  generalize hr : positionRoleAt T aPos.val = r
  have hpos := positionOfRole_positionRoleAt T aPos.val
  rw [hr] at hpos
  cases r with
  | inl u =>
      refine ⟨Sum.inr u, ?_⟩
      apply Subtype.ext
      exact hpos
  | inr ps =>
      rcases ps with ⟨p, side⟩
      cases side with
      | left =>
          change p.val.left = aPos.val at hpos
          cases hp : chi p with
          | black =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_black_left chi hProper p hp
              rw [hpos, aPos.property] at hletter
              cases hletter
          | white =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_white_left chi hProper p hp
              rw [hpos, aPos.property] at hletter
              cases hletter
          | grey =>
              have hleftA :
                  leftLetterOfProperColoring chi hProper p = Nucleotide.A := by
                have hletter :
                    sequenceOfProperColoring chi hProper p.val.left =
                      Nucleotide.A := by
                  rw [hpos]
                  exact aPos.property
                simpa only [sequenceOfProperColoring_left] using hletter
              let g : GreyPair chi := ⟨p, hp⟩
              refine ⟨Sum.inl g, ?_⟩
              apply Subtype.ext
              exact (aPositionOfGreyPair_val_of_left_A chi hProper g hleftA).trans
                hpos
      | right =>
          change p.val.right = aPos.val at hpos
          cases hp : chi p with
          | black =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_black_right chi hProper p hp
              rw [hpos, aPos.property] at hletter
              cases hletter
          | white =>
              exfalso
              have hletter :=
                sequenceOfProperColoring_white_right chi hProper p hp
              rw [hpos, aPos.property] at hletter
              cases hletter
          | grey =>
              have hrightA :
                  sequenceOfProperColoring chi hProper p.val.right =
                    Nucleotide.A := by
                rw [hpos]
                exact aPos.property
              have hleftU :
                  leftLetterOfProperColoring chi hProper p = Nucleotide.U := by
                rcases leftLetter_grey_mem_AU chi hProper p hp with hA | hU
                · exfalso
                  rw [sequenceOfProperColoring_right, hA] at hrightA
                  cases hrightA
                · exact hU
              have hnotA :
                  leftLetterOfProperColoring chi hProper p ≠ Nucleotide.A := by
                rw [hleftU]
                decide
              let g : GreyPair chi := ⟨p, hp⟩
              refine ⟨Sum.inl g, ?_⟩
              apply Subtype.ext
              exact (aPositionOfGreyPair_val_of_left_ne_A chi hProper g hnotA).trans
                hpos

/-- Grey pairs plus target-unpaired positions are in explicit bijection with
all `A` positions. -/
noncomputable def greyOrUnpairedEquivAPosition
    (chi : Coloring T) (hProper : ProperColoring chi) :
    GreyPair chi ⊕ UnpairedPosition T ≃ NucleotidePosition
      (sequenceOfProperColoring chi hProper) Nucleotide.A :=
  Equiv.ofBijective (aPositionSource chi hProper)
    ⟨aPositionSource_injective chi hProper,
      aPositionSource_surjective chi hProper⟩

/-- Exact `A` count of the assigned sequence. -/
theorem nucleotideCount_A_sequenceOfProperColoring
    (chi : Coloring T) (hProper : ProperColoring chi) :
    nucleotideCount (sequenceOfProperColoring chi hProper) Nucleotide.A =
      greyPairCount chi + targetUnpairedCount T := by
  calc
    nucleotideCount (sequenceOfProperColoring chi hProper) Nucleotide.A =
        Fintype.card (GreyPair chi ⊕ UnpairedPosition T) :=
      (Fintype.card_congr (greyOrUnpairedEquivAPosition chi hProper)).symm
    _ = greyPairCount chi + targetUnpairedCount T := by
      simp [greyPairCount, targetUnpairedCount]

/-! ## Limiting-position injection for an arbitrary competitor -/

variable {S : SecondaryStructure n} {w : Sequence n}

/-- Explicit four-way classification of an arbitrary compatible pair. -/
theorem compatiblePair_four_cases
    (hS : StructureCompatible w S) (a : PairedNode S) :
    (w a.val.left = Nucleotide.A ∧ w a.val.right = Nucleotide.U) ∨
      (w a.val.left = Nucleotide.U ∧ w a.val.right = Nucleotide.A) ∨
      (w a.val.left = Nucleotide.C ∧ w a.val.right = Nucleotide.G) ∨
      (w a.val.left = Nucleotide.G ∧ w a.val.right = Nucleotide.C) :=
  (compatible_iff_four_pairs _ _).1 (hS a.val a.property)

/-- Forget the `U`/`C` tag of a limiting position. -/
def limitingPositionValue :
    NucleotidePosition w Nucleotide.U ⊕
      NucleotidePosition w Nucleotide.C → Fin n :=
  Sum.elim Subtype.val Subtype.val

/-- Every compatible pair is assigned the unique `U` or `C` endpoint that it
consumes. -/
def limitingPositionOfCompatibleArc
    (w : Sequence n) (S : SecondaryStructure n)
    (hS : StructureCompatible w S) (a : PairedNode S) :
    NucleotidePosition w Nucleotide.U ⊕
      NucleotidePosition w Nucleotide.C :=
  match h : w a.val.left with
  | Nucleotide.A =>
      Sum.inl ⟨a.val.right, by
        have hc := hS a.val a.property
        simpa [Compatible, h] using hc⟩
  | Nucleotide.U => Sum.inl ⟨a.val.left, h⟩
  | Nucleotide.C => Sum.inr ⟨a.val.left, h⟩
  | Nucleotide.G =>
      Sum.inr ⟨a.val.right, by
        have hc := hS a.val a.property
        simpa [Compatible, h] using hc⟩

/-- The selected limiting position is an endpoint of the source arc. -/
theorem limitingPositionOfCompatibleArc_incident
    (w : Sequence n) (S : SecondaryStructure n)
    (hS : StructureCompatible w S) (a : PairedNode S) :
    a.val.Incident
      (limitingPositionValue (limitingPositionOfCompatibleArc w S hS a)) := by
  simp only [limitingPositionOfCompatibleArc]
  split <;> simp [limitingPositionValue, Arc.Incident]

/-- Different compatible pairs consume different limiting positions, solely by
the partial-matching property. -/
theorem limitingPositionOfCompatibleArc_injective
    (w : Sequence n) (S : SecondaryStructure n)
    (hS : StructureCompatible w S) :
    Function.Injective (limitingPositionOfCompatibleArc w S hS) := by
  intro a b hab
  apply Subtype.ext
  apply S.eq_of_mem_of_incident a.property b.property
    (limitingPositionOfCompatibleArc_incident w S hS a)
  rw [hab]
  exact limitingPositionOfCompatibleArc_incident w S hS b

/-- Pairing-inventory upper bound for every compatible secondary structure. -/
theorem pairCount_le_nucleotideCount_U_add_C
    (hS : StructureCompatible w S) :
    pairCount S ≤
      nucleotideCount w Nucleotide.U + nucleotideCount w Nucleotide.C := by
  change pairCount S ≤
    Fintype.card (NucleotidePosition w Nucleotide.U) +
      Fintype.card (NucleotidePosition w Nucleotide.C)
  rw [← Fintype.card_sum]
  simpa [pairCount, PairedNode] using
    Fintype.card_le_of_injective
      (limitingPositionOfCompatibleArc w S hS)
      (limitingPositionOfCompatibleArc_injective w S hS)

/-- No compatible alternative can contain more pairs than the target of the
assigned proper coloring. -/
theorem pairCount_le_sequenceOfProperColoring
    (chi : Coloring T) (hProper : ProperColoring chi)
    (S : SecondaryStructure n)
    (hS : StructureCompatible (sequenceOfProperColoring chi hProper) S) :
    pairCount S ≤ pairCount T := by
  calc
    pairCount S ≤
        nucleotideCount (sequenceOfProperColoring chi hProper) Nucleotide.U +
          nucleotideCount (sequenceOfProperColoring chi hProper) Nucleotide.C :=
      pairCount_le_nucleotideCount_U_add_C hS
    _ = greyPairCount chi + nonGreyPairCount chi := by
      rw [nucleotideCount_U_sequenceOfProperColoring,
        nucleotideCount_C_sequenceOfProperColoring]
    _ = pairCount T :=
      (pairCount_eq_greyPairCount_add_nonGreyPairCount chi).symm

/-- The assigned sequence makes its target maximum by pair count. -/
theorem sequenceOfProperColoring_isMaximumCompatible
    (chi : Coloring T) (hProper : ProperColoring chi) :
    IsMaximumCompatible (sequenceOfProperColoring chi hProper) T := by
  intro S hS
  exact pairCount_le_sequenceOfProperColoring chi hProper S hS

/-! ## Equality case -/

/-- At a tight limiting-inventory bound, every `U` and every `C` position is
paired. -/
theorem equality_uses_all_U_and_C
    (hS : StructureCompatible w S)
    (heq : pairCount S =
      nucleotideCount w Nucleotide.U + nucleotideCount w Nucleotide.C) :
    (∀ i : Fin n, w i = Nucleotide.U → S.positionPaired i) ∧
      (∀ i : Fin n, w i = Nucleotide.C → S.positionPaired i) := by
  have hcard :
      Fintype.card (PairedNode S) =
        Fintype.card
          (NucleotidePosition w Nucleotide.U ⊕
            NucleotidePosition w Nucleotide.C) := by
    simpa [pairCount, PairedNode, nucleotideCount] using heq
  have hsurj : Function.Surjective
      (limitingPositionOfCompatibleArc w S hS) :=
    ((Fintype.bijective_iff_injective_and_card
      (limitingPositionOfCompatibleArc w S hS)).2
        ⟨limitingPositionOfCompatibleArc_injective w S hS, hcard⟩).2
  constructor
  · intro i hi
    let u : NucleotidePosition w Nucleotide.U := ⟨i, hi⟩
    obtain ⟨a, ha⟩ := hsurj (Sum.inl u)
    refine ⟨a.val, a.property, ?_⟩
    have hinc := limitingPositionOfCompatibleArc_incident w S hS a
    rw [ha] at hinc
    exact hinc
  · intro i hi
    let c : NucleotidePosition w Nucleotide.C := ⟨i, hi⟩
    obtain ⟨a, ha⟩ := hsurj (Sum.inr c)
    refine ⟨a.val, a.property, ?_⟩
    have hinc := limitingPositionOfCompatibleArc_incident w S hS a
    rw [ha] at hinc
    exact hinc

/-- Choose the unique arc incident to a position already known to be paired. -/
noncomputable def pairedArcOfPosition
    (S : SecondaryStructure n) (i : Fin n) (hi : S.positionPaired i) :
    PairedNode S :=
  ⟨Classical.choose hi, (Classical.choose_spec hi).1⟩

theorem pairedArcOfPosition_incident
    (S : SecondaryStructure n) (i : Fin n) (hi : S.positionPaired i) :
    (pairedArcOfPosition S i hi).val.Incident i :=
  (Classical.choose_spec hi).2

theorem compatibleArc_exists_G_of_C
    (hS : StructureCompatible w S) (a : PairedNode S)
    (c : NucleotidePosition w Nucleotide.C)
    (hc : a.val.Incident c.val) :
    ∃ g : NucleotidePosition w Nucleotide.G, a.val.Incident g.val := by
  rcases hc with hc | hc
  · have hcomp := hS a.val a.property
    have hright : w a.val.right = Nucleotide.G := by
      simpa [Compatible, ← hc, c.property] using hcomp
    exact ⟨⟨a.val.right, hright⟩, a.val.incident_right⟩
  · have hcomp := compatible_symm (hS a.val a.property)
    have hleft : w a.val.left = Nucleotide.G := by
      simpa [Compatible, ← hc, c.property] using hcomp
    exact ⟨⟨a.val.left, hleft⟩, a.val.incident_left⟩

theorem compatibleArc_C_endpoint_unique
    (hS : StructureCompatible w S) (a : PairedNode S)
    (c d : NucleotidePosition w Nucleotide.C)
    (hc : a.val.Incident c.val) (hd : a.val.Incident d.val) : c = d := by
  apply Subtype.ext
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · exact hc.trans hd.symm
  · exfalso
    have hcomp := hS a.val a.property
    have : Compatible Nucleotide.C Nucleotide.C := by
      simpa [← hc, ← hd, c.property, d.property] using hcomp
    exact compatible_same_iff Nucleotide.C this
  · exfalso
    have hcomp := compatible_symm (hS a.val a.property)
    have : Compatible Nucleotide.C Nucleotide.C := by
      simpa [← hc, ← hd, c.property, d.property] using hcomp
    exact compatible_same_iff Nucleotide.C this
  · exact hc.trans hd.symm

/-- For each paired `C`, choose the `G` endpoint of its unique compatible
incident arc. -/
noncomputable def gPartnerOfC
    (w : Sequence n) (S : SecondaryStructure n)
    (hS : StructureCompatible w S)
    (hC : ∀ c : NucleotidePosition w Nucleotide.C,
      S.positionPaired c.val) :
    NucleotidePosition w Nucleotide.C →
      NucleotidePosition w Nucleotide.G :=
  fun c => Classical.choose
    (compatibleArc_exists_G_of_C hS
      (pairedArcOfPosition S c.val (hC c)) c
      (pairedArcOfPosition_incident S c.val (hC c)))

theorem gPartnerOfC_incident
    (hS : StructureCompatible w S)
    (hC : ∀ c : NucleotidePosition w Nucleotide.C,
      S.positionPaired c.val) (c : NucleotidePosition w Nucleotide.C) :
    (pairedArcOfPosition S c.val (hC c)).val.Incident
      (gPartnerOfC w S hS hC c).val :=
  Classical.choose_spec
    (compatibleArc_exists_G_of_C hS
      (pairedArcOfPosition S c.val (hC c)) c
      (pairedArcOfPosition_incident S c.val (hC c)))

theorem gPartnerOfC_injective
    (hS : StructureCompatible w S)
    (hC : ∀ c : NucleotidePosition w Nucleotide.C,
      S.positionPaired c.val) :
    Function.Injective (gPartnerOfC w S hS hC) := by
  intro c d hgd
  let ac := pairedArcOfPosition S c.val (hC c)
  let ad := pairedArcOfPosition S d.val (hC d)
  have harc : ac = ad := by
    apply Subtype.ext
    apply S.eq_of_mem_of_incident ac.property ad.property
      (gPartnerOfC_incident hS hC c)
    rw [hgd]
    exact gPartnerOfC_incident hS hC d
  apply compatibleArc_C_endpoint_unique hS ac c d
  · exact pairedArcOfPosition_incident S c.val (hC c)
  · rw [harc]
    exact pairedArcOfPosition_incident S d.val (hC d)

/-- If all `C` positions are paired and `#C = #G`, every `G` position is paired
as well. -/
theorem all_G_paired_of_all_C_paired_of_count_eq
    (hS : StructureCompatible w S)
    (hC : ∀ c : NucleotidePosition w Nucleotide.C,
      S.positionPaired c.val)
    (hcard : nucleotideCount w Nucleotide.C =
      nucleotideCount w Nucleotide.G) :
    ∀ g : NucleotidePosition w Nucleotide.G, S.positionPaired g.val := by
  have hbij : Function.Bijective (gPartnerOfC w S hS hC) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨gPartnerOfC_injective hS hC, hcard⟩
  intro g
  obtain ⟨c, hc⟩ := hbij.2 g
  let a := pairedArcOfPosition S c.val (hC c)
  refine ⟨a.val, a.property, ?_⟩
  rw [← hc]
  exact gPartnerOfC_incident hS hC c

/-- If a compatible competitor ties the target pair count, it pairs every
limiting `U`, `C`, and `G` position. -/
theorem equality_uses_all_limiting_nucleotides
    (chi : Coloring T) (hProper : ProperColoring chi)
    (S : SecondaryStructure n)
    (hS : StructureCompatible (sequenceOfProperColoring chi hProper) S)
    (hEq : pairCount S = pairCount T) :
    (∀ i : Fin n,
      sequenceOfProperColoring chi hProper i = Nucleotide.U →
        S.positionPaired i) ∧
      (∀ i : Fin n,
        sequenceOfProperColoring chi hProper i = Nucleotide.C →
          S.positionPaired i) ∧
      (∀ i : Fin n,
        sequenceOfProperColoring chi hProper i = Nucleotide.G →
          S.positionPaired i) := by
  let assigned := sequenceOfProperColoring chi hProper
  have htight : pairCount S =
      nucleotideCount assigned Nucleotide.U +
        nucleotideCount assigned Nucleotide.C := by
    calc
      pairCount S = pairCount T := hEq
      _ = greyPairCount chi + nonGreyPairCount chi :=
        pairCount_eq_greyPairCount_add_nonGreyPairCount chi
      _ = nucleotideCount assigned Nucleotide.U +
          nucleotideCount assigned Nucleotide.C := by
        rw [nucleotideCount_U_sequenceOfProperColoring,
          nucleotideCount_C_sequenceOfProperColoring]
  have hUC := equality_uses_all_U_and_C hS htight
  have hCsub : ∀ c : NucleotidePosition assigned Nucleotide.C,
      S.positionPaired c.val := by
    intro c
    exact hUC.2 c.val c.property
  have hcountCG : nucleotideCount assigned Nucleotide.C =
      nucleotideCount assigned Nucleotide.G := by
    exact (nucleotideCount_C_sequenceOfProperColoring chi hProper).trans
      (nucleotideCount_G_sequenceOfProperColoring chi hProper).symm
  have hGsub :=
    all_G_paired_of_all_C_paired_of_count_eq hS hCsub hcountCG
  refine ⟨hUC.1, hUC.2, ?_⟩
  intro i hi
  exact hGsub ⟨i, hi⟩

/-! ## Class-K maximum theorem -/

/-- Every class-K target has one explicit complete sequence for which it is a
compatible maximum-pair fold.  Ties are intentionally still allowed here. -/
theorem targetClass_has_maximumPairSequence
    (hK : InTargetClassK T) :
    ∃ w : Sequence n,
      StructureCompatible w T ∧
        ∀ S : SecondaryStructure n,
          StructureCompatible w S → pairCount S ≤ pairCount T := by
  let C := globalColoringCertificate hK
  let w := sequenceOfProperColoring C.coloring C.proper
  refine ⟨w, structureCompatible_sequenceOfProperColoring C.coloring C.proper, ?_⟩
  intro S hS
  exact pairCount_le_sequenceOfProperColoring C.coloring C.proper S hS

end RNA
