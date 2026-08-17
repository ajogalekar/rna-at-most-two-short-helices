module

public import RNA.Coloring
public import RNA.PositionRole

@[expose] public section

set_option autoImplicit false

/-!
# Deterministic sequence assignment from a proper coloring

Grey orientations are assigned top-down.  A grey child of a grey parent copies
the parent's left letter; every other grey child receives `A` or `U` from its
rank in the actual ordered grey-sibling list.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Actual paired children of one specified color. -/
def childrenOfColor (χ : Coloring T) (p : PairedOrRootNode T)
    (c : Color) : Finset (PairedNode T) :=
  (pairedChildren T p).filter (fun v => χ v = c)

@[simp]
theorem mem_childrenOfColor_iff (χ : Coloring T)
    (p : PairedOrRootNode T) (c : Color) (v : PairedNode T) :
    v ∈ childrenOfColor χ p c ↔ v ∈ pairedChildren T p ∧ χ v = c := by
  simp [childrenOfColor]

/-- Child-color multiplicity is the corresponding actual multiset count. -/
private theorem card_filter_eq_count_map {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (c : β) :
    (s.filter (fun a => f a = c)).card = (s.val.map f).count c := by
  rw [Multiset.count_map]
  rw [← Finset.filter_val]
  congr 2
  funext a
  exact propext (eq_comm (a := f a) (b := c))

theorem childrenOfColor_card_eq_count (χ : Coloring T)
    (p : PairedOrRootNode T) (c : Color) :
    (childrenOfColor χ p c).card = (childColorMultiset χ p).count c := by
  exact card_filter_eq_count_map (pairedChildren T p) χ c

/-- The child multiset is literally a submultiset of the exposure. -/
theorem childColorMultiset_le_exposedMultiset (χ : Coloring T)
    (p : PairedOrRootNode T) :
    childColorMultiset χ p ≤ exposedMultiset χ p := by
  cases p with
  | none => exact le_rfl
  | some q =>
      exact Multiset.le_add_left _ _

/-- Properness of the actual exposure restricts its actual child multiset. -/
theorem proper_childColorMultiset (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedOrRootNode T) :
    ProperExposure (childColorMultiset χ p) :=
  ProperExposure.mono (childColorMultiset_le_exposedMultiset χ p) (hProper p)

/-- Properness permits at most one black child at any interface. -/
theorem black_children_card_le_one (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedOrRootNode T) :
    (childrenOfColor χ p Color.black).card ≤ 1 := by
  rw [childrenOfColor_card_eq_count]
  exact (proper_childColorMultiset χ hProper p).1

/-- Properness permits at most one white child at any interface. -/
theorem white_children_card_le_one (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedOrRootNode T) :
    (childrenOfColor χ p Color.white).card ≤ 1 := by
  rw [childrenOfColor_card_eq_count]
  exact (proper_childColorMultiset χ hProper p).2.1

/-- Properness permits at most two grey children at any interface. -/
theorem grey_children_card_le_two (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedOrRootNode T) :
    (childrenOfColor χ p Color.grey).card ≤ 2 := by
  rw [childrenOfColor_card_eq_count]
  exact (proper_childColorMultiset χ hProper p).2.2

/-- A grey parent's closing grey incidence leaves room for at most one grey
child. -/
theorem grey_children_card_le_one_of_parent_grey (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedNode T)
    (hpGrey : χ p = Color.grey) :
    (childrenOfColor χ (some p) Color.grey).card ≤ 1 := by
  rw [childrenOfColor_card_eq_count]
  have hp := (hProper (some p)).2.2
  simp [exposedMultiset, hpGrey] at hp
  omega

/-- A black parent's closing white incidence rules out white children. -/
theorem white_children_card_eq_zero_of_parent_black (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedNode T)
    (hpBlack : χ p = Color.black) :
    (childrenOfColor χ (some p) Color.white).card = 0 := by
  rw [childrenOfColor_card_eq_count]
  have hp := (hProper (some p)).2.1
  have hsum :
      1 + (childColorMultiset χ (some p)).count Color.white ≤ 1 := by
    simpa [exposedMultiset, hpBlack] using hp
  omega

/-- A white parent's closing black incidence rules out black children. -/
theorem black_children_card_eq_zero_of_parent_white (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedNode T)
    (hpWhite : χ p = Color.white) :
    (childrenOfColor χ (some p) Color.black).card = 0 := by
  rw [childrenOfColor_card_eq_count]
  have hp := (hProper (some p)).1
  have hsum :
      1 + (childColorMultiset χ (some p)).count Color.black ≤ 1 := by
    simpa [exposedMultiset, hpWhite] using hp
  omega

/-- Grey children in deterministic backbone order. -/
def orderedGreyChildren (χ : Coloring T)
    (p : PairedOrRootNode T) : List (PairedNode T) :=
  (childrenOfColor χ p Color.grey).sort

@[simp]
theorem orderedGreyChildren_length (χ : Coloring T)
    (p : PairedOrRootNode T) :
    (orderedGreyChildren χ p).length =
      (childrenOfColor χ p Color.grey).card := by
  simp [orderedGreyChildren]

theorem mem_orderedGreyChildren_iff (χ : Coloring T)
    (p : PairedOrRootNode T) (v : PairedNode T) :
    v ∈ orderedGreyChildren χ p ↔
      v ∈ pairedChildren T p ∧ χ v = Color.grey := by
  simp [orderedGreyChildren, childrenOfColor]

/-- Zero-based rank in the exact ordered grey-child list. -/
def greySiblingRank (χ : Coloring T) (p : PairedOrRootNode T)
    (v : PairedNode T) : Nat :=
  (orderedGreyChildren χ p).idxOf v

/-- Every actual grey child at an anchor interface has rank zero or one. -/
theorem greySiblingRank_lt_two (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedOrRootNode T)
    (v : PairedNode T) (hv : v ∈ pairedChildren T p)
    (hvGrey : χ v = Color.grey) :
    greySiblingRank χ p v < 2 := by
  have hmem : v ∈ orderedGreyChildren χ p :=
    (mem_orderedGreyChildren_iff χ p v).2 ⟨hv, hvGrey⟩
  have hrank := List.idxOf_lt_length_of_mem hmem
  have hcard := grey_children_card_le_two χ hProper p
  simp only [orderedGreyChildren_length] at hrank
  change (orderedGreyChildren χ p).idxOf v < 2
  omega

/-- The first grey sibling gets `A`; the second gets `U`. -/
def greyRankLetter (r : Nat) : Nucleotide :=
  if r = 0 then Nucleotide.A else Nucleotide.U

theorem greyRankLetter_mem_AU (r : Nat) :
    greyRankLetter r = Nucleotide.A ∨
      greyRankLetter r = Nucleotide.U := by
  unfold greyRankLetter
  split <;> simp_all

theorem greyRankLetter_injective_below_two {r s : Nat}
    (hr : r < 2) (hs : s < 2)
    (h : greyRankLetter r = greyRankLetter s) : r = s := by
  unfold greyRankLetter at h
  split at h <;> split at h <;> simp_all <;> omega

/-- Distinct actual grey children have distinct rank letters whenever
properness bounds the interface to two grey slots. -/
theorem greyRankLetter_ne_of_distinct_children (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedOrRootNode T)
    {v q : PairedNode T}
    (hv : v ∈ pairedChildren T p) (hvGrey : χ v = Color.grey)
    (hq : q ∈ pairedChildren T p) (hqGrey : χ q = Color.grey)
    (hvq : v ≠ q) :
    greyRankLetter (greySiblingRank χ p v) ≠
      greyRankLetter (greySiblingRank χ p q) := by
  intro hletters
  apply hvq
  have hvmem : v ∈ orderedGreyChildren χ p :=
    (mem_orderedGreyChildren_iff χ p v).2 ⟨hv, hvGrey⟩
  have hqmem : q ∈ orderedGreyChildren χ p :=
    (mem_orderedGreyChildren_iff χ p q).2 ⟨hq, hqGrey⟩
  apply (List.idxOf_inj hvmem).mp
  apply greyRankLetter_injective_below_two
    (greySiblingRank_lt_two χ hProper p v hv hvGrey)
    (greySiblingRank_lt_two χ hProper p q hq hqGrey)
    hletters

/-- Raw recursive left-letter assignment.  Properness is not computational
input: it is used only to prove that the selected ranks are valid. -/
noncomputable def leftLetterOfColoring (χ : Coloring T)
    (v : PairedNode T) : Nucleotide :=
  match χ v with
  | Color.black => Nucleotide.G
  | Color.white => Nucleotide.C
  | Color.grey =>
      match hp : parent T (Sum.inl v) with
      | none => greyRankLetter (greySiblingRank χ none v)
      | some p =>
          if χ p = Color.grey then
            leftLetterOfColoring χ p
          else
            greyRankLetter (greySiblingRank χ (some p) v)
termination_by v.val.left.val
decreasing_by
  have hcontains := parent_pair_contains T hp
  simp only [PairedNode.StrictlyContains] at hcontains
  exact hcontains.1

/-- Public proof-bearing name for the deterministic left-letter assignment. -/
noncomputable def leftLetterOfProperColoring (χ : Coloring T)
    (_hProper : ProperColoring χ) (v : PairedNode T) : Nucleotide :=
  leftLetterOfColoring χ v

@[simp]
theorem leftLetter_black (χ : Coloring T) (hProper : ProperColoring χ)
    (v : PairedNode T) (hv : χ v = Color.black) :
    leftLetterOfProperColoring χ hProper v = Nucleotide.G := by
  change leftLetterOfColoring χ v = Nucleotide.G
  conv_lhs => rw [leftLetterOfColoring]
  simp only [hv]

@[simp]
theorem leftLetter_white (χ : Coloring T) (hProper : ProperColoring χ)
    (v : PairedNode T) (hv : χ v = Color.white) :
    leftLetterOfProperColoring χ hProper v = Nucleotide.C := by
  change leftLetterOfColoring χ v = Nucleotide.C
  conv_lhs => rw [leftLetterOfColoring]
  simp only [hv]

/-- A grey child of a grey parent copies the parent's left letter. -/
theorem leftLetter_grey_child_of_grey_parent (χ : Coloring T)
    (hProper : ProperColoring χ) (p v : PairedNode T)
    (hv : χ v = Color.grey)
    (hp : parent T (Sum.inl v) = some p)
    (hpGrey : χ p = Color.grey) :
    leftLetterOfProperColoring χ hProper v =
      leftLetterOfProperColoring χ hProper p := by
  change leftLetterOfColoring χ v = leftLetterOfColoring χ p
  conv_lhs => rw [leftLetterOfColoring]
  simp only [hv]
  split
  · rename_i hroot
    rw [hroot] at hp
    simp at hp
  · rename_i q hparent
    have hqp : q = p := Option.some.inj (hparent.symm.trans hp)
    subst q
    simp [hpGrey]

/-- At a root/non-grey anchor, a grey node receives its exact rank letter. -/
theorem leftLetter_grey_at_anchor (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T)
    (hv : χ v = Color.grey)
    (p : PairedOrRootNode T)
    (hp : parent T (Sum.inl v) = p)
    (hanchor : ∀ q, p = some q → χ q ≠ Color.grey) :
    leftLetterOfProperColoring χ hProper v =
      greyRankLetter (greySiblingRank χ p v) := by
  cases p with
  | none =>
      change leftLetterOfColoring χ v =
        greyRankLetter (greySiblingRank χ none v)
      conv_lhs => rw [leftLetterOfColoring]
      simp only [hv]
      split
      · rfl
      · rename_i q hparent
        rw [hparent] at hp
        simp at hp
  | some q =>
      have hq := hanchor q rfl
      change leftLetterOfColoring χ v =
        greyRankLetter (greySiblingRank χ (some q) v)
      conv_lhs => rw [leftLetterOfColoring]
      simp only [hv]
      split
      · rename_i hroot
        rw [hroot] at hp
        simp at hp
      · rename_i r hparent
        have hrq : r = q := Option.some.inj (hparent.symm.trans hp)
        subst r
        simp [hq]

/-- Every grey pair receives `A` or `U` on its left endpoint. -/
theorem leftLetter_grey_mem_AU (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T)
    (hv : χ v = Color.grey) :
    leftLetterOfProperColoring χ hProper v = Nucleotide.A ∨
      leftLetterOfProperColoring χ hProper v = Nucleotide.U := by
  -- Follow grey-parent links to the first anchor.
  generalize hm : v.val.left.val = m
  induction m using Nat.strong_induction_on generalizing v with
  | h m ih =>
      cases hp : parent T (Sum.inl v) with
      | none =>
          rw [leftLetter_grey_at_anchor χ hProper v hv none hp]
          · exact greyRankLetter_mem_AU _
          · intro q hnone
            cases hnone
      | some p =>
          by_cases hpGrey : χ p = Color.grey
          · rw [leftLetter_grey_child_of_grey_parent χ hProper p v hv hp hpGrey]
            have hcontains := parent_pair_contains T hp
            simp only [PairedNode.StrictlyContains] at hcontains
            exact ih p.val.left.val (by omega) p hpGrey rfl
          · rw [leftLetter_grey_at_anchor χ hProper v hv (some p) hp]
            · exact greyRankLetter_mem_AU _
            · intro q hq
              have hpq : p = q := Option.some.inj hq
              simpa [← hpq] using hpGrey

/-- Distinct grey children at the root or below a non-grey parent receive
distinct left letters. -/
theorem leftLetter_ne_of_distinct_grey_anchor_children (χ : Coloring T)
    (hProper : ProperColoring χ) (p : PairedOrRootNode T)
    {v q : PairedNode T}
    (hv : v ∈ pairedChildren T p) (hvGrey : χ v = Color.grey)
    (hq : q ∈ pairedChildren T p) (hqGrey : χ q = Color.grey)
    (hanchor : ∀ r, p = some r → χ r ≠ Color.grey)
    (hvq : v ≠ q) :
    leftLetterOfProperColoring χ hProper v ≠
      leftLetterOfProperColoring χ hProper q := by
  have hvParent : parent T (Sum.inl v) = p := by
    simpa [pairedChildren] using hv
  have hqParent : parent T (Sum.inl q) = p := by
    simpa [pairedChildren] using hq
  rw [leftLetter_grey_at_anchor χ hProper v hvGrey p hvParent hanchor,
    leftLetter_grey_at_anchor χ hProper q hqGrey p hqParent hanchor]
  exact greyRankLetter_ne_of_distinct_children χ hProper p
    hv hvGrey hq hqGrey hvq

/-- Assemble the complete sequence from the unique role at every position. -/
noncomputable def sequenceOfProperColoring (χ : Coloring T)
    (hProper : ProperColoring χ) : Sequence n :=
  fun i =>
    match positionRoleAt T i with
    | Sum.inl _ => Nucleotide.A
    | Sum.inr (v, EndpointSide.left) =>
        leftLetterOfProperColoring χ hProper v
    | Sum.inr (v, EndpointSide.right) =>
        (leftLetterOfProperColoring χ hProper v).comp

@[simp]
theorem sequenceOfProperColoring_unpaired (χ : Coloring T)
    (hProper : ProperColoring χ) (u : UnpairedPosition T) :
    sequenceOfProperColoring χ hProper u.val = Nucleotide.A := by
  simp [sequenceOfProperColoring]

@[simp]
theorem sequenceOfProperColoring_left (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T) :
    sequenceOfProperColoring χ hProper v.val.left =
      leftLetterOfProperColoring χ hProper v := by
  simp [sequenceOfProperColoring]

@[simp]
theorem sequenceOfProperColoring_right (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T) :
    sequenceOfProperColoring χ hProper v.val.right =
      (leftLetterOfProperColoring χ hProper v).comp := by
  simp [sequenceOfProperColoring]

@[simp]
theorem sequenceOfProperColoring_black_left (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T)
    (hv : χ v = Color.black) :
    sequenceOfProperColoring χ hProper v.val.left = Nucleotide.G := by
  simp [hv]

@[simp]
theorem sequenceOfProperColoring_black_right (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T)
    (hv : χ v = Color.black) :
    sequenceOfProperColoring χ hProper v.val.right = Nucleotide.C := by
  simp [hv]

@[simp]
theorem sequenceOfProperColoring_white_left (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T)
    (hv : χ v = Color.white) :
    sequenceOfProperColoring χ hProper v.val.left = Nucleotide.C := by
  simp [hv]

@[simp]
theorem sequenceOfProperColoring_white_right (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T)
    (hv : χ v = Color.white) :
    sequenceOfProperColoring χ hProper v.val.right = Nucleotide.G := by
  simp [hv]

theorem sequenceOfProperColoring_grey_left (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T)
    (hv : χ v = Color.grey) :
    sequenceOfProperColoring χ hProper v.val.left = Nucleotide.A ∨
      sequenceOfProperColoring χ hProper v.val.left = Nucleotide.U := by
  rw [sequenceOfProperColoring_left]
  exact leftLetter_grey_mem_AU χ hProper v hv

@[simp]
theorem sequenceOfProperColoring_right_eq_comp_left (χ : Coloring T)
    (hProper : ProperColoring χ) (v : PairedNode T) :
    sequenceOfProperColoring χ hProper v.val.right =
      (sequenceOfProperColoring χ hProper v.val.left).comp := by
  simp

end RNA
