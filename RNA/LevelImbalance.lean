module

public import RNA.PairingInventory
public import RNA.PrefixBalance
public import RNA.MatchingPartner

@[expose] public section

set_option autoImplicit false

/-!
# Noncrossing interior closure and the level-imbalance obstruction
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Strict geometric membership in the interior of an ordered arc. -/
def StrictlyInside (a : Arc n) (i : Fin n) : Prop :=
  a.left < i ∧ i < a.right

instance (a : Arc n) (i : Fin n) : Decidable (StrictlyInside a i) := by
  unfold StrictlyInside
  infer_instance

/-- Nucleotide positions strictly inside an arc. -/
abbrev InteriorNucleotidePosition (w : Sequence n) (a : Arc n)
    (x : Nucleotide) :=
  {i : Fin n // StrictlyInside a i ∧ w i = x}

/-- Noncrossing interior closure: a partner of a strict interior position of
an enclosing arc is itself strictly interior. -/
theorem positionPartner_strictlyInside_of_enclosing_arc
    {S : SecondaryStructure n} {outer : Arc n}
    (hOuter : outer ∈ S.arcs) {i j : Fin n}
    (hi : StrictlyInside outer i) (hij : PositionPartner S i j) :
    StrictlyInside outer j := by
  obtain ⟨inner, hInner, horder⟩ := hij
  have hne : outer ≠ inner := by
    intro heq
    subst inner
    rcases horder with ⟨hileft, _⟩ | ⟨hiright, _⟩
    · rw [hileft] at hi
      exact (lt_irrefl outer.left) hi.1
    · rw [hiright] at hi
      exact (lt_irrefl outer.right) hi.2
  have hnoShare : ¬ outer.ShareEndpoint inner := by
    intro hshare
    exact hne (S.eq_of_mem_of_shareEndpoint hOuter hInner hshare)
  have hnc := S.not_crossing hOuter hInner
  rcases horder with ⟨hileft, hjright⟩ | ⟨hiright, hjleft⟩
  · subst i
    subst j
    have hrightNe : inner.right ≠ outer.right := by
      intro hright
      apply hnoShare
      exact ⟨outer.right, outer.incident_right, Or.inr hright.symm⟩
    have hnotOut : ¬ outer.right < inner.right := by
      intro hout
      apply hnc
      exact Or.inl ⟨hi.1, hi.2, hout⟩
    exact ⟨hi.1.trans inner.ordered,
      lt_of_le_of_ne (le_of_not_gt hnotOut) hrightNe⟩
  · subst i
    subst j
    have hleftNe : outer.left ≠ inner.left := by
      intro hleft
      apply hnoShare
      exact ⟨outer.left, outer.incident_left, Or.inl hleft⟩
    have hnotOut : ¬ inner.left < outer.left := by
      intro hout
      apply hnc
      exact Or.inr ⟨hout, hi.1, hi.2⟩
    exact ⟨lt_of_le_of_ne (le_of_not_gt hnotOut) hleftNe,
      inner.ordered.trans hi.2⟩

theorem partner_of_G_is_C {w : Sequence n}
    {S : SecondaryStructure n} (hS : StructureCompatible w S)
    {i j : Fin n} (hi : w i = Nucleotide.G)
    (hij : PositionPartner S i j) : w j = Nucleotide.C := by
  have hc := positionPartner_compatible hS hij
  rw [compatible_iff_eq_comp, hi] at hc
  exact hc

theorem partner_of_C_is_G {w : Sequence n}
    {S : SecondaryStructure n} (hS : StructureCompatible w S)
    {i j : Fin n} (hi : w i = Nucleotide.C)
    (hij : PositionPartner S i j) : w j = Nucleotide.G := by
  have hc := positionPartner_compatible hS hij
  rw [compatible_iff_eq_comp, hi] at hc
  exact hc

/-- Select the interior `C` partner of an interior `G`. -/
noncomputable def interiorCPartnerOfG {w : Sequence n}
    {S : SecondaryStructure n} (hS : StructureCompatible w S)
    {outer : Arc n} (hOuter : outer ∈ S.arcs)
    (hAll : ∀ i, StrictlyInside outer i →
      (w i = Nucleotide.G ∨ w i = Nucleotide.C) → S.positionPaired i) :
    InteriorNucleotidePosition w outer Nucleotide.G →
      InteriorNucleotidePosition w outer Nucleotide.C :=
  fun g =>
    let hgPaired := hAll g.val g.property.1 (Or.inl g.property.2)
    let j := partnerOf S g.val hgPaired
    ⟨j,
      positionPartner_strictlyInside_of_enclosing_arc hOuter g.property.1
        (partnerOf_spec S g.val hgPaired),
      partner_of_G_is_C hS g.property.2
        (partnerOf_spec S g.val hgPaired)⟩

/-- Select the interior `G` partner of an interior `C`. -/
noncomputable def interiorGPartnerOfC {w : Sequence n}
    {S : SecondaryStructure n} (hS : StructureCompatible w S)
    {outer : Arc n} (hOuter : outer ∈ S.arcs)
    (hAll : ∀ i, StrictlyInside outer i →
      (w i = Nucleotide.G ∨ w i = Nucleotide.C) → S.positionPaired i) :
    InteriorNucleotidePosition w outer Nucleotide.C →
      InteriorNucleotidePosition w outer Nucleotide.G :=
  fun c =>
    let hcPaired := hAll c.val c.property.1 (Or.inr c.property.2)
    let j := partnerOf S c.val hcPaired
    ⟨j,
      positionPartner_strictlyInside_of_enclosing_arc hOuter c.property.1
        (partnerOf_spec S c.val hcPaired),
      partner_of_C_is_G hS c.property.2
        (partnerOf_spec S c.val hcPaired)⟩

theorem interiorCPartnerOfG_injective {w : Sequence n}
    {S : SecondaryStructure n} (hS : StructureCompatible w S)
    {outer : Arc n} (hOuter : outer ∈ S.arcs)
    (hAll : ∀ i, StrictlyInside outer i →
      (w i = Nucleotide.G ∨ w i = Nucleotide.C) → S.positionPaired i) :
    Function.Injective (interiorCPartnerOfG hS hOuter hAll) := by
  intro g q hgq
  apply Subtype.ext
  let hgPaired := hAll g.val g.property.1 (Or.inl g.property.2)
  let hqPaired := hAll q.val q.property.1 (Or.inl q.property.2)
  have hpartnerG := partnerOf_spec S g.val hgPaired
  have hpartnerQ := partnerOf_spec S q.val hqPaired
  have hvalues := congrArg Subtype.val hgq
  change partnerOf S g.val hgPaired = partnerOf S q.val hqPaired at hvalues
  apply positionPartner_unique (positionPartner_symm hpartnerG)
  rw [hvalues]
  exact positionPartner_symm hpartnerQ

theorem interiorGPartnerOfC_injective {w : Sequence n}
    {S : SecondaryStructure n} (hS : StructureCompatible w S)
    {outer : Arc n} (hOuter : outer ∈ S.arcs)
    (hAll : ∀ i, StrictlyInside outer i →
      (w i = Nucleotide.G ∨ w i = Nucleotide.C) → S.positionPaired i) :
    Function.Injective (interiorGPartnerOfC hS hOuter hAll) := by
  intro c d hcd
  apply Subtype.ext
  let hcPaired := hAll c.val c.property.1 (Or.inr c.property.2)
  let hdPaired := hAll d.val d.property.1 (Or.inr d.property.2)
  have hpartnerC := partnerOf_spec S c.val hcPaired
  have hpartnerD := partnerOf_spec S d.val hdPaired
  have hvalues := congrArg Subtype.val hcd
  change partnerOf S c.val hcPaired = partnerOf S d.val hdPaired at hvalues
  apply positionPartner_unique (positionPartner_symm hpartnerC)
  rw [hvalues]
  exact positionPartner_symm hpartnerD

/-- If all interior G/C positions are paired, noncrossing compatibility gives
equal interior G and C inventories. -/
theorem interior_G_count_eq_C_count_of_all_paired {w : Sequence n}
    {S : SecondaryStructure n} (hS : StructureCompatible w S)
    {outer : Arc n} (hOuter : outer ∈ S.arcs)
    (hAll : ∀ i, StrictlyInside outer i →
      (w i = Nucleotide.G ∨ w i = Nucleotide.C) → S.positionPaired i) :
    Fintype.card (InteriorNucleotidePosition w outer Nucleotide.G) =
      Fintype.card (InteriorNucleotidePosition w outer Nucleotide.C) := by
  apply Nat.le_antisymm
  · exact Fintype.card_le_of_injective
      (interiorCPartnerOfG hS hOuter hAll)
      (interiorCPartnerOfG_injective hS hOuter hAll)
  · exact Fintype.card_le_of_injective
      (interiorGPartnerOfC hS hOuter hAll)
      (interiorGPartnerOfC_injective hS hOuter hAll)

/-- The open-interval filtered count is the cardinality of the corresponding
interior-position subtype. -/
theorem nucleotideCountIn_openInterval_eq_card_interior
    (w : Sequence n) (a : Arc n) (x : Nucleotide) :
    nucleotideCountIn w (openIntervalPositions a.left a.right) x =
      Fintype.card (InteriorNucleotidePosition w a x) := by
  rw [nucleotideCountIn]
  have hset :
      (openIntervalPositions a.left a.right).filter (fun i => w i = x) =
        Finset.univ.filter (fun i : Fin n => StrictlyInside a i ∧ w i = x) := by
    ext i
    constructor
    · intro hi
      obtain ⟨hiOpen, hix⟩ := Finset.mem_filter.mp hi
      obtain ⟨_hiUniv, hiInside⟩ := Finset.mem_filter.mp hiOpen
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, ⟨hiInside, hix⟩⟩
    · intro hi
      obtain ⟨_hiUniv, hiInside, hix⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiInside⟩, hix⟩
  rw [hset]
  exact (Fintype.card_subtype
    (fun i : Fin n => StrictlyInside a i ∧ w i = x)).symm

/-- **Manuscript Lemma 21.** A compatible A--U arc whose endpoint prefix
balances differ forces an explicit unpaired `G` or `C` position. -/
theorem levelImbalance_obstruction
    (χ : Coloring T) (hProper : ProperColoring χ)
    (S : SecondaryStructure n)
    (hS : StructureCompatible (sequenceOfProperColoring χ hProper) S)
    (a : Arc n) (ha : a ∈ S.arcs)
    (hAU :
      (sequenceOfProperColoring χ hProper a.left = Nucleotide.A ∧
        sequenceOfProperColoring χ hProper a.right = Nucleotide.U) ∨
      (sequenceOfProperColoring χ hProper a.left = Nucleotide.U ∧
        sequenceOfProperColoring χ hProper a.right = Nucleotide.A))
    (hBalance :
      prefixBalanceAt (sequenceOfProperColoring χ hProper) a.left ≠
        prefixBalanceAt (sequenceOfProperColoring χ hProper) a.right) :
    ∃ k : Fin n,
      (sequenceOfProperColoring χ hProper k = Nucleotide.G ∨
        sequenceOfProperColoring χ hProper k = Nucleotide.C) ∧
      ¬ S.positionPaired k := by
  let w := sequenceOfProperColoring χ hProper
  have hleftZero : nucleotideWeight (w a.left) = 0 := by
    rcases hAU with h | h <;> simp [w, h.1]
  have hrightZero : nucleotideWeight (w a.right) = 0 := by
    rcases hAU with h | h <;> simp [w, h.2]
  have hOpenNe : openIntervalBalance w a.left a.right ≠ 0 := by
    have hdiff := prefixBalanceAt_sub_eq_openIntervalBalance_of_endpoint_weights_zero
      w a.ordered hleftZero hrightZero
    intro hzero
    apply hBalance
    change prefixBalanceAt w a.left = prefixBalanceAt w a.right
    have : prefixBalanceAt w a.right - prefixBalanceAt w a.left = 0 := by
      rw [hdiff, hzero]
    omega
  by_contra hnone
  have hAll : ∀ i, StrictlyInside a i →
      (w i = Nucleotide.G ∨ w i = Nucleotide.C) → S.positionPaired i := by
    intro i _hi hGC
    by_contra hnot
    exact hnone ⟨i, hGC, hnot⟩
  have hcounts := interior_G_count_eq_C_count_of_all_paired hS ha hAll
  have hcountOpen :
      nucleotideCountIn w (openIntervalPositions a.left a.right) Nucleotide.G =
        nucleotideCountIn w (openIntervalPositions a.left a.right) Nucleotide.C := by
    rw [nucleotideCountIn_openInterval_eq_card_interior,
      nucleotideCountIn_openInterval_eq_card_interior]
    exact hcounts
  apply hOpenNe
  rw [openIntervalBalance_eq_count_G_sub_C, hcountOpen]
  omega

/-- Pairing a target-unpaired `A` forces an A--U competitor arc whose endpoint
balances are separated, and hence an unpaired `G` or `C`. -/
theorem targetUnpaired_pairing_obstruction
    (χ : Coloring T) (hProper : ProperColoring χ)
    (hSeparated : Separated χ)
    (S : SecondaryStructure n)
    (hS : StructureCompatible (sequenceOfProperColoring χ hProper) S)
    (u : UnpairedPosition T) (j : Fin n)
    (hPartner : PositionPartner S u.val j) :
    ∃ k : Fin n,
      (sequenceOfProperColoring χ hProper k = Nucleotide.G ∨
        sequenceOfProperColoring χ hProper k = Nucleotide.C) ∧
      ¬ S.positionPaired k := by
  let w := sequenceOfProperColoring χ hProper
  have huA : w u.val = Nucleotide.A := by
    simp [w]
  have hjU : w j = Nucleotide.U := by
    have hcompat := positionPartner_compatible hS hPartner
    change Compatible (w u.val) (w j) at hcompat
    rw [compatible_iff_eq_comp, huA] at hcompat
    exact hcompat
  obtain ⟨v, hvSource, _hvUnique⟩ :=
    U_position_has_unique_grey_source χ hProper j hjU
  have huBalance : prefixBalanceAt w u.val = unpairedLevel χ u := by
    exact prefixBalanceAt_unpaired_eq_unpairedLevel χ hProper u
  have hjBalance : prefixBalanceAt w j = pairedLevel χ v := by
    rcases hvSource.2 with hjLeft | hjRight
    · rw [hjLeft]
      exact prefixBalanceAt_pairedLeft_eq_pairedLevel χ hProper v
    · rw [hjRight]
      have hgrey := prefixBalanceAt_greyRight_eq χ hProper v hvSource.1
      exact hgrey.1.trans hgrey.2
  have hEndpointBalance : prefixBalanceAt w u.val ≠ prefixBalanceAt w j := by
    rw [huBalance, hjBalance]
    exact (hSeparated v hvSource.1 u).symm
  obtain ⟨a, ha, hleft, hright⟩ :=
    positionPartner_has_ordered_arc hPartner
  by_cases hij : u.val < j
  · have hle : u.val ≤ j := le_of_lt hij
    have hmin : min u.val j = u.val := min_eq_left hle
    have hmax : max u.val j = j := max_eq_right hle
    rw [hmin] at hleft
    rw [hmax] at hright
    apply levelImbalance_obstruction χ hProper S hS a ha
    · left
      constructor
      · rw [hleft]
        exact huA
      · rw [hright]
        exact hjU
    · rw [hleft, hright]
      exact hEndpointBalance
  · have hju : j < u.val := by
      have hne := positionPartner_ne hPartner
      omega
    have hle : j ≤ u.val := le_of_lt hju
    have hmin : min u.val j = j := min_eq_right hle
    have hmax : max u.val j = u.val := max_eq_left hle
    rw [hmin] at hleft
    rw [hmax] at hright
    apply levelImbalance_obstruction χ hProper S hS a ha
    · right
      constructor
      · rw [hleft]
        exact hjU
      · rw [hright]
        exact huA
    · rw [hleft, hright]
      exact hEndpointBalance.symm

end RNA
