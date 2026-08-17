module

public import RNA.AtomicDesign
public import RNA.SequenceCertificate

@[expose] public section

set_option autoImplicit false

/-!
# Uniqueness of saturated locally distinct targets

This file proves manuscript Theorem 19 over the actual interval tree of an
arbitrary saturated `SecondaryStructure`.  The public theorem remains stated
for the fixed-length `Sequence` and `SecondaryStructure` model.
-/

namespace RNA

variable {n : Nat}

/-- Saturation rules out every unpaired interval-tree singleton. -/
theorem unpairedPosition_false_of_saturated
    {R : SecondaryStructure n} (hSat : SaturatedStructure R)
    (u : UnpairedPosition R) : False :=
  u.property (hSat u.val)

/-- Accordingly, a saturated interval-tree interface has no unpaired
children. -/
theorem unpairedChildren_eq_empty_of_saturated
    {R : SecondaryStructure n} (hSat : SaturatedStructure R)
    (p : PairedOrRootNode R) :
    unpairedChildren R p = ∅ := by
  ext u
  exact False.elim (unpairedPosition_false_of_saturated hSat u)

private theorem pairedChild_not_strictlyContains_sibling
    {R : SecondaryStructure n} {p : PairedOrRootNode R}
    {q r : PairedNode R}
    (hq : q ∈ pairedChildren R p) (hr : r ∈ pairedChildren R p) :
    ¬ PairedNode.StrictlyContains R q (Sum.inl r) := by
  have hqParent : parent R (Sum.inl q) = p := by
    simpa [pairedChildren] using hq
  have hrParent : parent R (Sum.inl r) = p := by
    simpa [pairedChildren] using hr
  intro hqr
  cases p with
  | none =>
      exact ((parent_eq_root_iff R (Sum.inl r)).mp hrParent q) hqr
  | some a =>
      have haContainsQ := parent_pair_contains R hqParent
      rcases (parent_pair_smallest R hrParent).2 q hqr with hqa | hqContainsA
      · subst q
        simp only [PairedNode.StrictlyContains] at haContainsQ
        omega
      · simp only [PairedNode.StrictlyContains] at haContainsQ hqContainsA
        omega

/-- Distinct paired children of one interval-tree interface have disjoint,
strictly ordered closed intervals. -/
theorem pairedChildren_disjoint
    {R : SecondaryStructure n} {p : PairedOrRootNode R}
    {q r : PairedNode R}
    (hq : q ∈ pairedChildren R p) (hr : r ∈ pairedChildren R p)
    (hne : q ≠ r) :
    q.val.right < r.val.left ∨ r.val.right < q.val.left := by
  rcases pairedNode_laminar R q r with heq | hqr | hrq | hqContains | hrContains
  · exact False.elim (hne heq)
  · exact Or.inl hqr
  · exact Or.inr hrq
  · exact False.elim (pairedChild_not_strictlyContains_sibling hq hr hqContains)
  · exact False.elim (pairedChild_not_strictlyContains_sibling hr hq hrContains)

theorem pairedChildren_right_lt_left_of_left_lt
    {R : SecondaryStructure n} {p : PairedOrRootNode R}
    {q r : PairedNode R}
    (hq : q ∈ pairedChildren R p) (hr : r ∈ pairedChildren R p)
    (hlr : q.val.left < r.val.left) :
    q.val.right < r.val.left := by
  have hne : q ≠ r := by
    intro h
    subst r
    exact (lt_irrefl _ hlr)
  rcases pairedChildren_disjoint hq hr hne with hqr | hrq
  · exact hqr
  · have hqOrder := q.val.ordered
    have hrOrder := r.val.ordered
    omega

/-- The existing ordered-child enumeration strictly reflects slot order. -/
theorem orderedPairedChild_lt_of_lt
    (R : SecondaryStructure n) (p : PairedOrRootNode R)
    (i j : Fin (pairedChildCount R p)) (hij : i < j) :
    orderedPairedChild R p i < orderedPairedChild R p j := by
  have hsorted : (orderedPairedChildren R p).SortedLT :=
    Finset.sortedLT_sort (pairedChildren R p)
  unfold orderedPairedChild
  apply hsorted.strictMono_get
  change i.val < j.val
  exact hij

@[simp]
theorem pairedChildIndex_orderedPairedChild
    (R : SecondaryStructure n) (p : PairedOrRootNode R)
    (i : Fin (pairedChildCount R p)) :
    pairedChildIndex R p (orderedPairedChild R p i)
        (orderedPairedChild_mem R p i) = i := by
  apply orderedPairedChild_injective R p
  rw [orderedPairedChild_pairedChildIndex]

theorem pairedChildIndex_lt_of_left_lt
    (R : SecondaryStructure n) (p : PairedOrRootNode R)
    (q r : PairedNode R)
    (hq : q ∈ pairedChildren R p) (hr : r ∈ pairedChildren R p)
    (hlr : q.val.left < r.val.left) :
    pairedChildIndex R p q hq < pairedChildIndex R p r hr := by
  let iq := pairedChildIndex R p q hq
  let ir := pairedChildIndex R p r hr
  have hiq : orderedPairedChild R p iq = q := by
    exact orderedPairedChild_pairedChildIndex R p q hq
  have hir : orderedPairedChild R p ir = r := by
    exact orderedPairedChild_pairedChildIndex R p r hr
  have hne : iq ≠ ir := by
    intro heq
    have hqr := congrArg (orderedPairedChild R p) heq
    rw [hiq, hir] at hqr
    exact (ne_of_lt hlr) (congrArg (fun s : PairedNode R => s.val.left) hqr)
  change iq < ir
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt
  · have hrq := orderedPairedChild_lt_of_lt R p ir iq hgt
    rw [hiq, hir] at hrq
    change r.val.left < q.val.left at hrq
    exact False.elim ((not_lt_of_ge hlr.le) hrq)

/-- There is only one secondary structure on the empty backbone. -/
theorem secondaryStructure_eq_empty_zero (S : SecondaryStructure 0) :
    S = SecondaryStructure.empty 0 := by
  apply SecondaryStructure.ext
  ext a
  exact Fin.elim0 a.left

/-- Uniqueness of saturated compatible structures is immediate on the empty
backbone. -/
theorem saturated_unique_zero
    (R P : SecondaryStructure 0) : P = R := by
  rw [secondaryStructure_eq_empty_zero P,
    secondaryStructure_eq_empty_zero R]

/-- Select the unique target pair incident to a position in a saturated
structure. -/
noncomputable def saturatedPairedNodeAt
    (R : SecondaryStructure n) (hSat : SaturatedStructure R) (i : Fin n) :
    PairedNode R :=
  ⟨Classical.choose (hSat i), (Classical.choose_spec (hSat i)).1⟩

theorem saturatedPairedNodeAt_incident
    (R : SecondaryStructure n) (hSat : SaturatedStructure R) (i : Fin n) :
    (saturatedPairedNodeAt R hSat i).val.Incident i :=
  (Classical.choose_spec (hSat i)).2

/-! ## Saturated child-interval coverage -/

/-- Target pairs whose closed intervals contain a specified position. -/
def coveringPairsAt (R : SecondaryStructure n) (i : Fin n) :
    Finset (PairedNode R) :=
  Finset.univ.filter (fun q => q.val.left ≤ i ∧ i ≤ q.val.right)

theorem saturatedPairedNodeAt_mem_coveringPairsAt
    (R : SecondaryStructure n) (hSat : SaturatedStructure R) (i : Fin n) :
    saturatedPairedNodeAt R hSat i ∈ coveringPairsAt R i := by
  simp only [coveringPairsAt, Finset.mem_filter, Finset.mem_univ, true_and]
  have hinc := saturatedPairedNodeAt_incident R hSat i
  rcases hinc with hleft | hright
  · exact ⟨hleft.symm.le,
      hleft.le.trans (saturatedPairedNodeAt R hSat i).val.ordered.le⟩
  · exact ⟨(saturatedPairedNodeAt R hSat i).val.ordered.le.trans
        hright.symm.le,
      hright.le⟩

/-- Saturation makes the finite set of target pairs covering a position
nonempty. -/
theorem coveringPairsAt_nonempty_of_saturated
    (R : SecondaryStructure n) (hSat : SaturatedStructure R) (i : Fin n) :
    (coveringPairsAt R i).Nonempty :=
  ⟨saturatedPairedNodeAt R hSat i,
    saturatedPairedNodeAt_mem_coveringPairsAt R hSat i⟩

/-- The outermost target pair covering a position, chosen by its least left
endpoint. -/
noncomputable def outermostCoveringPair
    (R : SecondaryStructure n) (hSat : SaturatedStructure R) (i : Fin n) :
    PairedNode R :=
  (coveringPairsAt R i).min' (coveringPairsAt_nonempty_of_saturated R hSat i)

theorem outermostCoveringPair_covers
    (R : SecondaryStructure n) (hSat : SaturatedStructure R) (i : Fin n) :
    (outermostCoveringPair R hSat i).val.left ≤ i ∧
      i ≤ (outermostCoveringPair R hSat i).val.right := by
  have hmem := Finset.min'_mem (coveringPairsAt R i)
    (coveringPairsAt_nonempty_of_saturated R hSat i)
  simpa only [outermostCoveringPair, coveringPairsAt, Finset.mem_filter,
    Finset.mem_univ, true_and] using hmem

/-- The outermost pair covering any position of a saturated structure is a
direct child of the virtual root. -/
theorem outermostCoveringPair_mem_rootChildren
    (R : SecondaryStructure n) (hSat : SaturatedStructure R) (i : Fin n) :
    outermostCoveringPair R hSat i ∈ pairedChildren R none := by
  let c := outermostCoveringPair R hSat i
  have hcCover := outermostCoveringPair_covers R hSat i
  have hparent : parent R (Sum.inl c) = none := by
    apply (parent_eq_root_iff R _).mpr
    intro q hq
    have hqCover : q.val.left ≤ i ∧ i ≤ q.val.right := by
      simp only [PairedNode.StrictlyContains] at hcCover hq ⊢
      exact ⟨hq.1.le.trans hcCover.1, hcCover.2.trans hq.2.le⟩
    have hqMem : q ∈ coveringPairsAt R i := by
      simp [coveringPairsAt, hqCover]
    have hmin := Finset.min'_le (coveringPairsAt R i) q hqMem
    change c.val.left ≤ q.val.left at hmin
    simp only [PairedNode.StrictlyContains] at hq
    exact (not_lt_of_ge hmin) hq.1
  simpa [pairedChildren] using hparent

/-- The pair incident to the first backbone position starts at that position. -/
theorem saturatedPairedNodeAt_zero_left
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (hn : 0 < n) :
    (saturatedPairedNodeAt R hSat ⟨0, hn⟩).val.left = ⟨0, hn⟩ := by
  have hinc := saturatedPairedNodeAt_incident R hSat ⟨0, hn⟩
  rcases hinc with hleft | hright
  · exact hleft.symm
  · have hord := (saturatedPairedNodeAt R hSat ⟨0, hn⟩).val.ordered
    have hrightVal := congrArg Fin.val hright
    simp only at hrightVal
    omega

/-- The pair at the first backbone position is a root paired child. -/
theorem saturatedPairedNodeAt_zero_mem_rootChildren
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (hn : 0 < n) :
    saturatedPairedNodeAt R hSat ⟨0, hn⟩ ∈ pairedChildren R none := by
  have hleft := saturatedPairedNodeAt_zero_left R hSat hn
  have hparent : parent R
      (Sum.inl (saturatedPairedNodeAt R hSat ⟨0, hn⟩)) = none := by
    apply (parent_eq_root_iff R _).mpr
    intro q hq
    simp only [PairedNode.StrictlyContains] at hq
    have hleftVal := congrArg Fin.val hleft
    simp only at hleftVal
    omega
  simpa [pairedChildren] using hparent

/-- First strict interior position of a non-leaf target pair. -/
def firstInteriorPosition {R : SecondaryStructure n} (p : PairedNode R)
    (hInterior : p.val.left.val + 1 < p.val.right.val) : Fin n :=
  ⟨p.val.left.val + 1, by
    have := p.val.right.isLt
    omega⟩

theorem firstInteriorPosition_strictlyInside
    {R : SecondaryStructure n} (p : PairedNode R)
    (hInterior : p.val.left.val + 1 < p.val.right.val) :
    p.val.left < firstInteriorPosition p hInterior ∧
      firstInteriorPosition p hInterior < p.val.right := by
  change p.val.left.val < p.val.left.val + 1 ∧
    p.val.left.val + 1 < p.val.right.val
  omega

private theorem incident_pair_inside_of_inside_pair
    {R : SecondaryStructure n} (p q : PairedNode R) (i : Fin n)
    (hi : p.val.left < i ∧ i < p.val.right)
    (hqi : q.val.Incident i) :
    PairedNode.StrictlyContains R p (Sum.inl q) := by
  have hiLeft : p.val.left.val < i.val := hi.1
  have hiRight : i.val < p.val.right.val := hi.2
  have hqOrdered := q.val.ordered
  have hpq := pairedNode_laminar R p q
  rcases hpq with hpq | hpq | hpq | hpq | hpq
  · subst q
    rcases hqi with hqi | hqi
    · have hqiVal := congrArg Fin.val hqi
      omega
    · have hqiVal := congrArg Fin.val hqi
      omega
  · rcases hqi with hqi | hqi
    · have hqiVal := congrArg Fin.val hqi
      omega
    · have hqiVal := congrArg Fin.val hqi
      omega
  · rcases hqi with hqi | hqi
    · have hqiVal := congrArg Fin.val hqi
      omega
    · have hqiVal := congrArg Fin.val hqi
      omega
  · exact hpq
  · rcases hqi with hqi | hqi
    · have hqiVal := congrArg Fin.val hqi
      omega
    · have hqiVal := congrArg Fin.val hqi
      omega

/-- Pairs strictly inside `p` whose closed intervals contain `i`. -/
def coveringPairsInsideAt (R : SecondaryStructure n) (p : PairedNode R)
    (i : Fin n) : Finset (PairedNode R) :=
  Finset.univ.filter (fun q =>
    PairedNode.StrictlyContains R p (Sum.inl q) ∧
      q.val.left ≤ i ∧ i ≤ q.val.right)

theorem coveringPairsInsideAt_nonempty_of_saturated
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (p : PairedNode R) (i : Fin n)
    (hi : p.val.left < i ∧ i < p.val.right) :
    (coveringPairsInsideAt R p i).Nonempty := by
  let q := saturatedPairedNodeAt R hSat i
  have hqi := saturatedPairedNodeAt_incident R hSat i
  have hpq : PairedNode.StrictlyContains R p (Sum.inl q) :=
    incident_pair_inside_of_inside_pair p q i hi hqi
  refine ⟨q, ?_⟩
  simp only [coveringPairsInsideAt, Finset.mem_filter, Finset.mem_univ,
    true_and]
  refine ⟨hpq, ?_⟩
  rcases hqi with hleft | hright
  · exact ⟨hleft.symm.le, hleft.le.trans q.val.ordered.le⟩
  · exact ⟨q.val.ordered.le.trans hright.symm.le, hright.le⟩

/-- The outermost target pair strictly inside `p` and covering `i`. -/
noncomputable def outermostCoveringPairInside
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (p : PairedNode R) (i : Fin n)
    (hi : p.val.left < i ∧ i < p.val.right) : PairedNode R :=
  (coveringPairsInsideAt R p i).min'
    (coveringPairsInsideAt_nonempty_of_saturated R hSat p i hi)

theorem outermostCoveringPairInside_spec
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (p : PairedNode R) (i : Fin n)
    (hi : p.val.left < i ∧ i < p.val.right) :
    PairedNode.StrictlyContains R p
        (Sum.inl (outermostCoveringPairInside R hSat p i hi)) ∧
      (outermostCoveringPairInside R hSat p i hi).val.left ≤ i ∧
      i ≤ (outermostCoveringPairInside R hSat p i hi).val.right := by
  have hmem := Finset.min'_mem (coveringPairsInsideAt R p i)
    (coveringPairsInsideAt_nonempty_of_saturated R hSat p i hi)
  simpa only [outermostCoveringPairInside, coveringPairsInsideAt,
    Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/-- Every strict interior position of a target pair in a saturated structure
is covered by the closed interval of an actual paired child. -/
theorem outermostCoveringPairInside_mem_pairedChildren
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (p : PairedNode R) (i : Fin n)
    (hi : p.val.left < i ∧ i < p.val.right) :
    outermostCoveringPairInside R hSat p i hi ∈
      pairedChildren R (some p) := by
  let c := outermostCoveringPairInside R hSat p i hi
  have hcSpec := outermostCoveringPairInside_spec R hSat p i hi
  have hparent : parent R (Sum.inl c) = some p := by
    apply (parent_eq_iff_isParent R (Sum.inl c) (some p)).mpr
    refine ⟨hcSpec.1, ?_⟩
    intro q hqc
    rcases enclosingPairs_nested R (Sum.inl c) q p hqc hcSpec.1 with
      hqp | hqp | hpq
    · exact Or.inl hqp
    · exact Or.inr hqp
    · exfalso
      have hqCover : q.val.left ≤ i ∧ i ≤ q.val.right := by
        simp only [PairedNode.StrictlyContains] at hqc hcSpec hpq ⊢
        exact ⟨hqc.1.le.trans hcSpec.2.1,
          hcSpec.2.2.trans hqc.2.le⟩
      have hqMem : q ∈ coveringPairsInsideAt R p i := by
        simp [coveringPairsInsideAt, hpq, hqCover]
      have hmin := Finset.min'_le (coveringPairsInsideAt R p i) q hqMem
      change c.val.left ≤ q.val.left at hmin
      simp only [PairedNode.StrictlyContains] at hqc
      exact (not_lt_of_ge hmin) hqc.1
  simpa [pairedChildren] using hparent

/-- Consecutive paired children leave no backbone gap in a saturated
structure.  The `hNoBetween` premise is the order-theoretic notion of
consecutiveness used by the sorted child list. -/
theorem pairedChildren_adjacent_of_no_child_between
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (p : PairedOrRootNode R) (q r : PairedNode R)
    (hq : q ∈ pairedChildren R p) (hr : r ∈ pairedChildren R p)
    (hleft : q.val.left < r.val.left)
    (hNoBetween : ∀ c : PairedNode R,
      c ∈ pairedChildren R p →
      q.val.left < c.val.left → c.val.left < r.val.left → False) :
    q.val.right.val + 1 = r.val.left.val := by
  have hqr := pairedChildren_right_lt_left_of_left_lt hq hr hleft
  have hle : q.val.right.val + 1 ≤ r.val.left.val := by omega
  by_contra hne
  have hgap : q.val.right.val + 1 < r.val.left.val := by omega
  have hiBound : q.val.right.val + 1 < n := by
    exact lt_trans hgap r.val.left.isLt
  let i : Fin n := ⟨q.val.right.val + 1, hiBound⟩
  have hcData : ∃ c : PairedNode R,
      c ∈ pairedChildren R p ∧ c.val.left ≤ i ∧ i ≤ c.val.right := by
    cases p with
    | none =>
        let c := outermostCoveringPair R hSat i
        exact ⟨c, outermostCoveringPair_mem_rootChildren R hSat i,
          outermostCoveringPair_covers R hSat i⟩
    | some a =>
        have hqParent : parent R (Sum.inl q) = some a := by
          simpa [pairedChildren] using hq
        have hrParent : parent R (Sum.inl r) = some a := by
          simpa [pairedChildren] using hr
        have haq := parent_pair_contains R hqParent
        have har := parent_pair_contains R hrParent
        have hiInside : a.val.left < i ∧ i < a.val.right := by
          simp only [PairedNode.StrictlyContains] at haq har
          have haqLeftVal : a.val.left.val < q.val.left.val := haq.1
          have harRightVal : r.val.right.val < a.val.right.val := har.2
          have hqOrderVal : q.val.left.val < q.val.right.val := q.val.ordered
          have hrOrderVal : r.val.left.val < r.val.right.val := r.val.ordered
          change a.val.left.val < q.val.right.val + 1 ∧
            q.val.right.val + 1 < a.val.right.val
          omega
        let c := outermostCoveringPairInside R hSat a i hiInside
        exact ⟨c,
          outermostCoveringPairInside_mem_pairedChildren R hSat a i hiInside,
          (outermostCoveringPairInside_spec R hSat a i hiInside).2⟩
  obtain ⟨c, hc, hcLeft, hcRight⟩ := hcData
  have hcNeQ : c ≠ q := by
    intro heq
    subst c
    have hcRightVal : i.val ≤ q.val.right.val := hcRight
    change q.val.right.val + 1 ≤ q.val.right.val at hcRightVal
    omega
  have hcNeR : c ≠ r := by
    intro heq
    subst c
    have hcLeftVal : r.val.left.val ≤ i.val := hcLeft
    change r.val.left.val ≤ q.val.right.val + 1 at hcLeftVal
    omega
  have hqBeforeC : q.val.right < c.val.left := by
    rcases pairedChildren_disjoint hq hc hcNeQ.symm with hqc | hcq
    · exact hqc
    · have hcRightVal : i.val ≤ c.val.right.val := hcRight
      change q.val.right.val + 1 ≤ c.val.right.val at hcRightVal
      have hqOrder := q.val.ordered
      omega
  have hcBeforeR : c.val.right < r.val.left := by
    rcases pairedChildren_disjoint hc hr hcNeR with hcr | hrc
    · exact hcr
    · have hcLeftVal : c.val.left.val ≤ i.val := hcLeft
      change c.val.left.val ≤ q.val.right.val + 1 at hcLeftVal
      have hrOrder := r.val.ordered
      omega
  exact hNoBetween c hc
    (lt_trans q.val.ordered hqBeforeC)
    (lt_trans c.val.ordered hcBeforeR)

/-- Successive slots in the ordered child enumeration have adjacent closed
intervals. -/
theorem orderedPairedChild_succ_adjacent
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (p : PairedOrRootNode R) (i : Fin (pairedChildCount R p))
    (hi : i.val + 1 < pairedChildCount R p) :
    let j : Fin (pairedChildCount R p) := ⟨i.val + 1, hi⟩
    (orderedPairedChild R p i).val.right.val + 1 =
      (orderedPairedChild R p j).val.left.val := by
  let j : Fin (pairedChildCount R p) := ⟨i.val + 1, hi⟩
  let q := orderedPairedChild R p i
  let r := orderedPairedChild R p j
  have hq : q ∈ pairedChildren R p := orderedPairedChild_mem R p i
  have hr : r ∈ pairedChildren R p := orderedPairedChild_mem R p j
  have hij : i < j := by
    change i.val < i.val + 1
    omega
  have hleftOrder := orderedPairedChild_lt_of_lt R p i j hij
  have hleft : q.val.left < r.val.left := by
    exact hleftOrder
  apply pairedChildren_adjacent_of_no_child_between R hSat p q r hq hr hleft
  intro c hc hqc hcr
  have hik := pairedChildIndex_lt_of_left_lt R p q c hq hc hqc
  have hkr := pairedChildIndex_lt_of_left_lt R p c r hc hr hcr
  have hiq : pairedChildIndex R p q hq = i := by
    apply orderedPairedChild_injective R p
    rw [orderedPairedChild_pairedChildIndex]
  have hir : pairedChildIndex R p r hr = j := by
    apply orderedPairedChild_injective R p
    rw [orderedPairedChild_pairedChildIndex]
  rw [hiq] at hik
  rw [hir] at hkr
  change i.val < (pairedChildIndex R p c hc).val at hik
  change (pairedChildIndex R p c hc).val < i.val + 1 at hkr
  omega

/-- The first ordered root child starts at backbone position zero. -/
theorem orderedPairedChild_zero_left_root
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (hChildren : 0 < pairedChildCount R none) :
    (orderedPairedChild R none ⟨0, hChildren⟩).val.left.val = 0 := by
  let q := orderedPairedChild R none ⟨0, hChildren⟩
  have hn : 0 < n := by
    exact Nat.zero_lt_of_lt q.val.left.isLt
  let i : Fin n := ⟨0, hn⟩
  let c := outermostCoveringPair R hSat i
  have hc : c ∈ pairedChildren R none :=
    outermostCoveringPair_mem_rootChildren R hSat i
  have hcCover := outermostCoveringPair_covers R hSat i
  have hcLeft : c.val.left.val = 0 := by
    have hle : c.val.left.val ≤ i.val := hcCover.1
    change c.val.left.val ≤ 0 at hle
    omega
  have hcIndexZero : (pairedChildIndex R none c hc).val = 0 := by
    by_contra hne
    have hzeroLt : (⟨0, hChildren⟩ : Fin (pairedChildCount R none)) <
        pairedChildIndex R none c hc := by
      change 0 < (pairedChildIndex R none c hc).val
      omega
    have hqc := orderedPairedChild_lt_of_lt R none
      ⟨0, hChildren⟩ (pairedChildIndex R none c hc) hzeroLt
    rw [orderedPairedChild_pairedChildIndex] at hqc
    change q.val.left < c.val.left at hqc
    have hqcVal : q.val.left.val < c.val.left.val := hqc
    omega
  have hcIndex : pairedChildIndex R none c hc = ⟨0, hChildren⟩ := by
    apply Fin.ext
    exact hcIndexZero
  have hqc := congrArg (orderedPairedChild R none) hcIndex
  rw [orderedPairedChild_pairedChildIndex] at hqc
  have hleft := congrArg (fun s : PairedNode R => s.val.left.val) hqc
  simpa [q, hcLeft] using hleft.symm

/-- The first ordered child of a paired node starts immediately after the
parent's left endpoint. -/
theorem orderedPairedChild_zero_left_nonroot
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (p : PairedNode R) (hChildren : 0 < pairedChildCount R (some p)) :
    (orderedPairedChild R (some p) ⟨0, hChildren⟩).val.left.val =
      p.val.left.val + 1 := by
  let q := orderedPairedChild R (some p) ⟨0, hChildren⟩
  have hqMem : q ∈ pairedChildren R (some p) :=
    orderedPairedChild_mem R (some p) ⟨0, hChildren⟩
  have hqParent : parent R (Sum.inl q) = some p := by
    simpa [pairedChildren] using hqMem
  have hpq := parent_pair_contains R hqParent
  have hiBound : p.val.left.val + 1 < n := by
    simp only [PairedNode.StrictlyContains] at hpq
    exact lt_of_le_of_lt (by omega) q.val.left.isLt
  let i : Fin n := ⟨p.val.left.val + 1, hiBound⟩
  have hiInside : p.val.left < i ∧ i < p.val.right := by
    simp only [PairedNode.StrictlyContains] at hpq
    change p.val.left.val < p.val.left.val + 1 ∧
      p.val.left.val + 1 < p.val.right.val
    have hqOrder := q.val.ordered
    omega
  let c := outermostCoveringPairInside R hSat p i hiInside
  have hc : c ∈ pairedChildren R (some p) :=
    outermostCoveringPairInside_mem_pairedChildren R hSat p i hiInside
  have hcSpec := outermostCoveringPairInside_spec R hSat p i hiInside
  have hcLeft : c.val.left.val = p.val.left.val + 1 := by
    have hgt : p.val.left.val < c.val.left.val := by
      exact hcSpec.1.1
    have hle : c.val.left.val ≤ i.val := hcSpec.2.1
    change c.val.left.val ≤ p.val.left.val + 1 at hle
    omega
  have hcIndexZero : (pairedChildIndex R (some p) c hc).val = 0 := by
    by_contra hne
    have hzeroLt : (⟨0, hChildren⟩ : Fin (pairedChildCount R (some p))) <
        pairedChildIndex R (some p) c hc := by
      change 0 < (pairedChildIndex R (some p) c hc).val
      omega
    have hqc := orderedPairedChild_lt_of_lt R (some p)
      ⟨0, hChildren⟩ (pairedChildIndex R (some p) c hc) hzeroLt
    rw [orderedPairedChild_pairedChildIndex] at hqc
    change q.val.left < c.val.left at hqc
    have hqcVal : q.val.left.val < c.val.left.val := hqc
    simp only [PairedNode.StrictlyContains] at hpq
    omega
  have hcIndex : pairedChildIndex R (some p) c hc = ⟨0, hChildren⟩ := by
    apply Fin.ext
    exact hcIndexZero
  have hqc := congrArg (orderedPairedChild R (some p)) hcIndex
  rw [orderedPairedChild_pairedChildIndex] at hqc
  have hleft := congrArg (fun s : PairedNode R => s.val.left.val) hqc
  simpa [q, hcLeft] using hleft.symm

/-- The last ordered root child ends at the final backbone position. -/
theorem orderedPairedChild_last_right_root
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (hChildren : 0 < pairedChildCount R none) :
    let last : Fin (pairedChildCount R none) :=
      ⟨pairedChildCount R none - 1, by omega⟩
    (orderedPairedChild R none last).val.right.val + 1 = n := by
  let last : Fin (pairedChildCount R none) :=
    ⟨pairedChildCount R none - 1, by omega⟩
  let q := orderedPairedChild R none last
  have hq : q ∈ pairedChildren R none := orderedPairedChild_mem R none last
  have hn : 0 < n := Nat.zero_lt_of_lt q.val.right.isLt
  let i : Fin n := ⟨n - 1, by omega⟩
  let c := outermostCoveringPair R hSat i
  have hc : c ∈ pairedChildren R none :=
    outermostCoveringPair_mem_rootChildren R hSat i
  have hcCover := outermostCoveringPair_covers R hSat i
  have hcRight : c.val.right.val + 1 = n := by
    have hle : i.val ≤ c.val.right.val := hcCover.2
    change n - 1 ≤ c.val.right.val at hle
    have hcBound := c.val.right.isLt
    omega
  have hcIndexLast : pairedChildIndex R none c hc = last := by
    apply Fin.ext
    change (pairedChildIndex R none c hc).val =
      pairedChildCount R none - 1
    by_contra hne
    have hkBound := (pairedChildIndex R none c hc).isLt
    have hklt : pairedChildIndex R none c hc < last := by
      change (pairedChildIndex R none c hc).val <
        pairedChildCount R none - 1
      omega
    have hcq := orderedPairedChild_lt_of_lt R none
      (pairedChildIndex R none c hc) last hklt
    rw [orderedPairedChild_pairedChildIndex] at hcq
    change c.val.left < q.val.left at hcq
    have hcBeforeQ := pairedChildren_right_lt_left_of_left_lt hc hq hcq
    have hcBeforeQVal : c.val.right.val < q.val.left.val := hcBeforeQ
    have hqBound := q.val.left.isLt
    omega
  have hcq := congrArg (orderedPairedChild R none) hcIndexLast
  rw [orderedPairedChild_pairedChildIndex] at hcq
  have hright := congrArg (fun s : PairedNode R => s.val.right.val + 1) hcq
  simpa [q, hcRight] using hright.symm

/-- The last ordered child of a paired node ends immediately before the
parent's right endpoint. -/
theorem orderedPairedChild_last_right_nonroot
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (p : PairedNode R) (hChildren : 0 < pairedChildCount R (some p)) :
    let last : Fin (pairedChildCount R (some p)) :=
      ⟨pairedChildCount R (some p) - 1, by omega⟩
    (orderedPairedChild R (some p) last).val.right.val + 1 =
      p.val.right.val := by
  let last : Fin (pairedChildCount R (some p)) :=
    ⟨pairedChildCount R (some p) - 1, by omega⟩
  let q := orderedPairedChild R (some p) last
  have hq : q ∈ pairedChildren R (some p) :=
    orderedPairedChild_mem R (some p) last
  have hqParent : parent R (Sum.inl q) = some p := by
    simpa [pairedChildren] using hq
  have hpq := parent_pair_contains R hqParent
  have hiBound : p.val.right.val - 1 < n := by
    have hpBound := p.val.right.isLt
    omega
  let i : Fin n := ⟨p.val.right.val - 1, hiBound⟩
  have hiInside : p.val.left < i ∧ i < p.val.right := by
    simp only [PairedNode.StrictlyContains] at hpq
    change p.val.left.val < p.val.right.val - 1 ∧
      p.val.right.val - 1 < p.val.right.val
    have hqOrder := q.val.ordered
    omega
  let c := outermostCoveringPairInside R hSat p i hiInside
  have hc : c ∈ pairedChildren R (some p) :=
    outermostCoveringPairInside_mem_pairedChildren R hSat p i hiInside
  have hcSpec := outermostCoveringPairInside_spec R hSat p i hiInside
  change PairedNode.StrictlyContains R p (Sum.inl c) ∧
    c.val.left ≤ i ∧ i ≤ c.val.right at hcSpec
  have hcRight : c.val.right.val + 1 = p.val.right.val := by
    have hle : i.val ≤ c.val.right.val := hcSpec.2.2
    change p.val.right.val - 1 ≤ c.val.right.val at hle
    have hlt : c.val.right.val < p.val.right.val := hcSpec.1.2
    omega
  have hcIndexLast : pairedChildIndex R (some p) c hc = last := by
    apply Fin.ext
    change (pairedChildIndex R (some p) c hc).val =
      pairedChildCount R (some p) - 1
    by_contra hne
    have hkBound := (pairedChildIndex R (some p) c hc).isLt
    have hklt : pairedChildIndex R (some p) c hc < last := by
      change (pairedChildIndex R (some p) c hc).val <
        pairedChildCount R (some p) - 1
      omega
    have hcq := orderedPairedChild_lt_of_lt R (some p)
      (pairedChildIndex R (some p) c hc) last hklt
    rw [orderedPairedChild_pairedChildIndex] at hcq
    change c.val.left < q.val.left at hcq
    have hcBeforeQ := pairedChildren_right_lt_left_of_left_lt hc hq hcq
    have hcBeforeQVal : c.val.right.val < q.val.left.val := hcBeforeQ
    simp only [PairedNode.StrictlyContains] at hpq
    have hqOrderVal : q.val.left.val < q.val.right.val := q.val.ordered
    have hpqRightVal : q.val.right.val < p.val.right.val := hpq.2
    omega
  have hcq := congrArg (orderedPairedChild R (some p)) hcIndexLast
  rw [orderedPairedChild_pairedChildIndex] at hcq
  have hright := congrArg (fun s : PairedNode R => s.val.right.val + 1) hcq
  simpa [q, hcRight] using hright.symm

/-! ## Closed target-pair blocks -/

/-- The complete sequence slice from the left through the right endpoint of
a target pair. -/
def pairedNodeWord (z : Sequence n) {R : SecondaryStructure n}
    (q : PairedNode R) : Word :=
  ((Sequence.toWord z).drop q.val.left.val).take q.val.closedLength

/-- The strict-interior sequence slice of a target pair. -/
def pairedNodeOpenWord (z : Sequence n) {R : SecondaryStructure n}
    (q : PairedNode R) : Word :=
  ((Sequence.toWord z).drop (q.val.left.val + 1)).take q.val.openLength

/-- A closed target-pair word is its strict interior wrapped by its actual
endpoint nucleotides. -/
theorem pairedNodeWord_eq_wrap_openWord
    (z : Sequence n) {R : SecondaryStructure n} (p : PairedNode R) :
    pairedNodeWord z p =
      Word.wrap (z p.val.left) (z p.val.right) (pairedNodeOpenWord z p) := by
  let w := Sequence.toWord z
  have hl : p.val.left.val < w.length := by
    simp [w]
  have hr : p.val.right.val < w.length := by
    simp [w]
  have hord : p.val.left.val < p.val.right.val := p.val.ordered
  have hclosed : p.val.closedLength = p.val.openLength + 2 := by
    unfold Arc.closedLength Arc.openLength
    omega
  have hopenLt :
      p.val.openLength < (w.drop (p.val.left.val + 1)).length := by
    simp [w, Arc.openLength]
    omega
  unfold pairedNodeWord pairedNodeOpenWord Word.wrap
  change (w.drop p.val.left.val).take p.val.closedLength = _
  rw [← List.cons_getElem_drop_succ (l := w) (n := p.val.left.val) (h := hl)]
  rw [hclosed]
  simp only [List.take_succ_cons]
  rw [← List.take_concat_get' _ _ hopenLt]
  congr 1
  · simp [w, Sequence.toWord]
  · rw [List.getElem_drop]
    simp only [w, Sequence.toWord, List.getElem_ofFn]
    congr
    unfold Arc.openLength
    change p.val.left.val + 1 +
        (p.val.right.val - p.val.left.val - 1) = p.val.right.val
    omega

@[simp]
theorem pairedNodeWord_length (z : Sequence n) {R : SecondaryStructure n}
    (q : PairedNode R) :
    (pairedNodeWord z q).length = q.val.closedLength := by
  simp only [pairedNodeWord, List.length_take, List.length_drop,
    Sequence.length_toWord]
  rw [min_eq_left]
  unfold Arc.closedLength
  have hright := q.val.right.isLt
  have horder := q.val.ordered
  change q.val.left.val < q.val.right.val at horder
  omega

@[simp]
theorem pairedNodeWord_toSequence_apply
    (z : Sequence n) {R : SecondaryStructure n} (q : PairedNode R)
    (i : Fin (pairedNodeWord z q).length) :
    (pairedNodeWord z q).toSequence i =
      z (q.val.closedIntervalOrderEmbedding
        (Fin.cast (pairedNodeWord_length z q) i)) := by
  change
    (((Sequence.toWord z).drop q.val.left.val).take q.val.closedLength)[i.val] = _
  rw [List.getElem_take, List.getElem_drop]
  simp [Sequence.toWord, Arc.closedIntervalOrderEmbedding,
    Fin.intervalOrderEmbedding]

/-- The target restricted to a paired closed interval, indexed by the exact
list length of `pairedNodeWord`. -/
def pairedNodeTarget (z : Sequence n) {R : SecondaryStructure n}
    (q : PairedNode R) : SecondaryStructure (pairedNodeWord z q).length :=
  (R.restrictClosedArc q.val).reindexOrderIso
    (Fin.castOrderIso (pairedNodeWord_length z q).symm)

theorem saturated_pairedNodeTarget
    (z : Sequence n) {R : SecondaryStructure n}
    (hSat : SaturatedStructure R) (q : PairedNode R) :
    SaturatedStructure (pairedNodeTarget z q) := by
  rw [pairedNodeTarget, SecondaryStructure.saturated_reindexOrderIso_iff]
  exact SecondaryStructure.saturated_restrictClosedArc R q.val q.property hSat

theorem compatible_pairedNodeTarget
    (z : Sequence n) {R : SecondaryStructure n}
    (hCompat : StructureCompatible z R) (q : PairedNode R) :
    StructureCompatible (pairedNodeWord z q).toSequence
      (pairedNodeTarget z q) := by
  rw [pairedNodeTarget,
    SecondaryStructure.structureCompatible_reindexOrderIso_iff]
  have hRestricted :=
    SecondaryStructure.structureCompatible_restrictClosedArc R z q.val hCompat
  have hseq :
      (fun i : Fin q.val.closedLength =>
        (pairedNodeWord z q).toSequence
          ((Fin.castOrderIso (pairedNodeWord_length z q).symm) i)) =
        (fun i => z (q.val.closedIntervalOrderEmbedding i)) := by
    funext i
    rw [pairedNodeWord_toSequence_apply]
    congr 2
  rw [hseq]
  exact hRestricted

/-- Package one proved target-pair block for the atomic lemmas. -/
def pairedNodeAtomicBlock
    (z : Sequence n) {R : SecondaryStructure n} (q : PairedNode R)
    (hDesign : AtomicDesign (pairedNodeWord z q) (pairedNodeTarget z q)) :
    AtomicDesignBlock where
  word := pairedNodeWord z q
  target := pairedNodeTarget z q
  design := hDesign

@[simp]
theorem pairedNodeAtomicBlock_firstLetter
    (z : Sequence n) {R : SecondaryStructure n} (q : PairedNode R)
    (hDesign : AtomicDesign (pairedNodeWord z q) (pairedNodeTarget z q)) :
    (pairedNodeAtomicBlock z q hDesign).firstLetter = z q.val.left := by
  rw [AtomicDesignBlock.firstLetter]
  simp [pairedNodeAtomicBlock, pairedNodeWord_eq_wrap_openWord, Word.wrap]

/-- Ordered atomic-design packages for every paired child of an interface. -/
def pairedChildAtomicBlocks
    (z : Sequence n) (R : SecondaryStructure n) (p : PairedOrRootNode R)
    (hDesign : ∀ i : Fin (pairedChildCount R p),
      AtomicDesign (pairedNodeWord z (orderedPairedChild R p i))
        (pairedNodeTarget z (orderedPairedChild R p i))) :
    List AtomicDesignBlock :=
  List.ofFn (fun i => pairedNodeAtomicBlock z
    (orderedPairedChild R p i) (hDesign i))

/-! ## Ordered child-word concatenation -/

/-- Concatenation of the first `k` ordered paired-child blocks. -/
def pairedChildWordPrefix (z : Sequence n) (R : SecondaryStructure n)
    (p : PairedOrRootNode R) (k : Nat)
    (hk : k ≤ pairedChildCount R p) : Word :=
  (List.ofFn (fun i : Fin k =>
    pairedNodeWord z (orderedPairedChild R p (Fin.castLE hk i)))).flatten

/-- Concatenation of all ordered paired-child blocks. -/
def pairedChildConcatWord (z : Sequence n) (R : SecondaryStructure n)
    (p : PairedOrRootNode R) : Word :=
  pairedChildWordPrefix z R p (pairedChildCount R p) le_rfl

theorem concatWord_pairedChildAtomicBlocks
    (z : Sequence n) (R : SecondaryStructure n) (p : PairedOrRootNode R)
    (hDesign : ∀ i : Fin (pairedChildCount R p),
      AtomicDesign (pairedNodeWord z (orderedPairedChild R p i))
        (pairedNodeTarget z (orderedPairedChild R p i))) :
    AtomicDesignBlock.concatWord (pairedChildAtomicBlocks z R p hDesign) =
      pairedChildConcatWord z R p := by
  simp [AtomicDesignBlock.concatWord, pairedChildAtomicBlocks,
    pairedNodeAtomicBlock, pairedChildConcatWord, pairedChildWordPrefix, List.map_ofFn,
    Function.comp_def]

theorem firstLetters_pairedChildAtomicBlocks
    (z : Sequence n) (R : SecondaryStructure n) (p : PairedOrRootNode R)
    (hDesign : ∀ i : Fin (pairedChildCount R p),
      AtomicDesign (pairedNodeWord z (orderedPairedChild R p i))
        (pairedNodeTarget z (orderedPairedChild R p i))) :
    (pairedChildAtomicBlocks z R p hDesign).map
        AtomicDesignBlock.firstLetter =
      List.ofFn (fun i : Fin (pairedChildCount R p) =>
        z (orderedPairedChild R p i).val.left) := by
  simp [pairedChildAtomicBlocks, List.map_ofFn, Function.comp_def]

theorem firstLettersPairwiseDistinct_pairedChildAtomicBlocks
    (z : Sequence n) (R : SecondaryStructure n) (p : PairedOrRootNode R)
    (hDistinct : ChildLeftLettersDistinct R z p)
    (hDesign : ∀ i : Fin (pairedChildCount R p),
      AtomicDesign (pairedNodeWord z (orderedPairedChild R p i))
        (pairedNodeTarget z (orderedPairedChild R p i))) :
    AtomicDesignBlock.FirstLettersPairwiseDistinct
      (pairedChildAtomicBlocks z R p hDesign) := by
  unfold AtomicDesignBlock.FirstLettersPairwiseDistinct
  rw [firstLetters_pairedChildAtomicBlocks]
  rw [List.pairwise_ofFn]
  intro i j hij hletters
  have hnodes := hDistinct
    (orderedPairedChild_mem R p i)
    (orderedPairedChild_mem R p j) hletters
  have hindices := orderedPairedChild_injective R p hnodes
  exact (ne_of_lt hij) hindices

theorem firstLettersAvoid_pairedChildAtomicBlocks
    (z : Sequence n) (R : SecondaryStructure n) (p : PairedOrRootNode R)
    (b : Nucleotide)
    (hAvoid : ∀ i : Fin (pairedChildCount R p),
      z (orderedPairedChild R p i).val.left ≠ b)
    (hDesign : ∀ i : Fin (pairedChildCount R p),
      AtomicDesign (pairedNodeWord z (orderedPairedChild R p i))
        (pairedNodeTarget z (orderedPairedChild R p i))) :
    AtomicDesignBlock.FirstLettersAvoid
      (pairedChildAtomicBlocks z R p hDesign) b := by
  intro B hB
  simp only [pairedChildAtomicBlocks, List.mem_ofFn] at hB
  obtain ⟨i, rfl⟩ := hB
  simpa only [pairedNodeAtomicBlock_firstLetter] using hAvoid i

@[simp]
theorem pairedChildWordPrefix_zero
    (z : Sequence n) (R : SecondaryStructure n)
    (p : PairedOrRootNode R) :
    pairedChildWordPrefix z R p 0 (Nat.zero_le _) = [] := by
  simp [pairedChildWordPrefix]

theorem pairedChildWordPrefix_succ
    (z : Sequence n) (R : SecondaryStructure n)
    (p : PairedOrRootNode R) (k : Nat)
    (hk : k + 1 ≤ pairedChildCount R p) :
    pairedChildWordPrefix z R p (k + 1) hk =
      pairedChildWordPrefix z R p k (by omega) ++
        pairedNodeWord z
          (orderedPairedChild R p ⟨k, by omega⟩) := by
  unfold pairedChildWordPrefix
  rw [List.ofFn_succ']
  rw [List.concat_eq_append, List.flatten_append]
  simp only [List.flatten_singleton]
  congr 1

/-- First backbone position belonging to the children of an interface. -/
def pairedChildInterfaceStart {R : SecondaryStructure n} :
    PairedOrRootNode R → Nat
  | none => 0
  | some p => p.val.left.val + 1

/-- The ordered child-word prefix is exactly the corresponding consecutive
slice of the original complete sequence. -/
theorem pairedChildWordPrefix_eq_slice
    (z : Sequence n) (R : SecondaryStructure n)
    (hSat : SaturatedStructure R) (p : PairedOrRootNode R)
    (k : Nat) (hk : k ≤ pairedChildCount R p) (hkPos : 0 < k) :
    pairedChildWordPrefix z R p k hk =
      ((Sequence.toWord z).drop (pairedChildInterfaceStart p)).take
        ((orderedPairedChild R p ⟨k - 1, by omega⟩).val.right.val + 1 -
          pairedChildInterfaceStart p) := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [pairedChildWordPrefix_succ]
      by_cases hkZero : k = 0
      · subst k
        simp only [pairedChildWordPrefix_zero, List.nil_append]
        cases p with
        | none =>
            have hfirst := orderedPairedChild_zero_left_root R hSat (by omega)
            change (orderedPairedChild R none ⟨0, by omega⟩).val.left.val = 0
              at hfirst
            unfold pairedNodeWord pairedChildInterfaceStart
            change
              ((Sequence.toWord z).drop
                (orderedPairedChild R none ⟨0, by omega⟩).val.left.val).take
                  (orderedPairedChild R none ⟨0, by omega⟩).val.closedLength =
                (Sequence.toWord z).take
                  ((orderedPairedChild R none ⟨0, by omega⟩).val.right.val + 1)
            rw [hfirst, List.drop_zero]
            congr 1
            unfold Arc.closedLength
            omega
        | some a =>
            have hfirst := orderedPairedChild_zero_left_nonroot R hSat a (by omega)
            change (orderedPairedChild R (some a) ⟨0, by omega⟩).val.left.val =
              a.val.left.val + 1 at hfirst
            unfold pairedNodeWord pairedChildInterfaceStart
            change
              ((Sequence.toWord z).drop
                (orderedPairedChild R (some a) ⟨0, by omega⟩).val.left.val).take
                  (orderedPairedChild R (some a) ⟨0, by omega⟩).val.closedLength =
                ((Sequence.toWord z).drop (a.val.left.val + 1)).take
                  ((orderedPairedChild R (some a) ⟨0, by omega⟩).val.right.val + 1 -
                    (a.val.left.val + 1))
            rw [hfirst]
            congr 1
            unfold Arc.closedLength
            have horder :=
              (orderedPairedChild R (some a) ⟨0, by omega⟩).val.ordered
            omega
      · have ih' := ih (by omega) (by omega)
        rw [ih']
        let previous := orderedPairedChild R p ⟨k - 1, by omega⟩
        let current := orderedPairedChild R p ⟨k, by omega⟩
        have hcurrent : orderedPairedChild R p ⟨k + 1 - 1, by omega⟩ =
            current := by
          have hind : (⟨k + 1 - 1, by omega⟩ : Fin (pairedChildCount R p)) =
              ⟨k, by omega⟩ := by
            apply Fin.ext
            change k + 1 - 1 = k
            omega
          exact congrArg (orderedPairedChild R p) hind
        rw [hcurrent]
        have hprevBound : k - 1 < pairedChildCount R p := by omega
        let previousIndex : Fin (pairedChildCount R p) := ⟨k - 1, hprevBound⟩
        have hprevSucc : previousIndex.val + 1 < pairedChildCount R p := by
          change k - 1 + 1 < pairedChildCount R p
          omega
        have hadj := orderedPairedChild_succ_adjacent R hSat p
          previousIndex hprevSucc
        dsimp only at hadj
        have hsuccIndex :
            (⟨previousIndex.val + 1,
                by omega⟩ : Fin (pairedChildCount R p)) = ⟨k, by omega⟩ := by
          apply Fin.ext
          change k - 1 + 1 = k
          omega
        rw [hsuccIndex] at hadj
        change previous.val.right.val + 1 = current.val.left.val at hadj
        have hstartLe : pairedChildInterfaceStart p ≤
            previous.val.right.val + 1 := by
          cases p with
          | none => simp [pairedChildInterfaceStart]
          | some a =>
              have hprevMem := orderedPairedChild_mem R (some a)
                ⟨k - 1, by omega⟩
              have hparent : parent R (Sum.inl previous) = some a := by
                simpa [pairedChildren, previous] using hprevMem
              have hcontains := parent_pair_contains R hparent
              simp only [PairedNode.StrictlyContains] at hcontains
              simp only [pairedChildInterfaceStart]
              have hleftVal : a.val.left.val < previous.val.left.val :=
                hcontains.1
              have horderVal : previous.val.left.val < previous.val.right.val :=
                previous.val.ordered
              omega
        have htotal :
            current.val.right.val + 1 - pairedChildInterfaceStart p =
              (previous.val.right.val + 1 - pairedChildInterfaceStart p) +
                current.val.closedLength := by
          unfold Arc.closedLength
          have hcurrentOrder : current.val.left.val < current.val.right.val :=
            current.val.ordered
          omega
        have hdrop : pairedChildInterfaceStart p +
              (previous.val.right.val + 1 - pairedChildInterfaceStart p) =
            current.val.left.val := by
          omega
        unfold pairedNodeWord
        rw [htotal, List.take_add, List.drop_drop, hdrop]

/-- On a nonempty saturated backbone, concatenating all root-child words
recovers the one complete sequence word. -/
theorem pairedChildConcatWord_root_eq_toWord
    (z : Sequence n) (R : SecondaryStructure n)
    (hSat : SaturatedStructure R) (hn : 0 < n) :
    pairedChildConcatWord z R none = Sequence.toWord z := by
  have hRootChild := saturatedPairedNodeAt_zero_mem_rootChildren R hSat hn
  have hChildren : 0 < pairedChildCount R none := by
    rw [pairedChildCount]
    exact Finset.card_pos.mpr ⟨_, hRootChild⟩
  have hslice := pairedChildWordPrefix_eq_slice z R hSat none
    (pairedChildCount R none) le_rfl hChildren
  have hlast := orderedPairedChild_last_right_root R hSat hChildren
  unfold pairedChildConcatWord
  rw [hslice]
  simp only [pairedChildInterfaceStart, List.drop_zero]
  have hendpoint :
      (orderedPairedChild R none
        ⟨pairedChildCount R none - 1, by omega⟩).val.right.val + 1 = n :=
    hlast
  rw [hendpoint, Nat.sub_zero]
  simpa only [Sequence.length_toWord] using
    (@List.take_length Nucleotide (Sequence.toWord z))

/-- In a saturated target, the pair at the first strict interior position of
`p` begins there and is an actual paired child of `p`. -/
theorem saturated_firstInterior_is_pairedChild
    (R : SecondaryStructure n) (hSat : SaturatedStructure R)
    (p : PairedNode R)
    (hInterior : p.val.left.val + 1 < p.val.right.val) :
    let q := saturatedPairedNodeAt R hSat
      (firstInteriorPosition p hInterior)
    q.val.left = firstInteriorPosition p hInterior ∧
      q ∈ pairedChildren R (some p) := by
  let i := firstInteriorPosition p hInterior
  let q := saturatedPairedNodeAt R hSat i
  have hi := firstInteriorPosition_strictlyInside p hInterior
  have hqi := saturatedPairedNodeAt_incident R hSat i
  have hpq : PairedNode.StrictlyContains R p (Sum.inl q) :=
    incident_pair_inside_of_inside_pair p q i hi hqi
  have hqleft : q.val.left = i := by
    rcases hqi with hleft | hright
    · exact hleft.symm
    · simp only [PairedNode.StrictlyContains] at hpq
      have hleftLt : q.val.left.val < i.val := by
        rw [hright]
        exact q.val.ordered
      have hiVal : i.val = p.val.left.val + 1 := rfl
      omega
  refine ⟨hqleft, ?_⟩
  have hparent : parent R (Sum.inl q) = some p := by
    apply (parent_eq_iff_isParent R (Sum.inl q) (some p)).mpr
    refine ⟨hpq, ?_⟩
    intro r hrq
    rcases enclosingPairs_nested R (Sum.inl q) r p hrq hpq with
      hrp | hrp | hpr
    · exact Or.inl hrp
    · exact Or.inr hrp
    · simp only [PairedNode.StrictlyContains] at hpr hpq hrq
      have hqleftVal := congrArg Fin.val hqleft
      have hiVal : i.val = p.val.left.val + 1 := rfl
      omega
  simpa [pairedChildren] using hparent

/-- Concatenating every paired-child word of a target pair recovers exactly
its strict-interior sequence word.  The empty list is the adjacent-endpoint
leaf case. -/
theorem pairedChildConcatWord_nonroot_eq_openWord
    (z : Sequence n) (R : SecondaryStructure n)
    (hSat : SaturatedStructure R) (p : PairedNode R) :
    pairedChildConcatWord z R (some p) = pairedNodeOpenWord z p := by
  by_cases hzero : pairedChildCount R (some p) = 0
  · have hopen : p.val.openLength = 0 := by
      by_contra hne
      have hInterior : p.val.left.val + 1 < p.val.right.val := by
        unfold Arc.openLength at hne
        have horder := p.val.ordered
        change p.val.left.val < p.val.right.val at horder
        omega
      let q := saturatedPairedNodeAt R hSat
        (firstInteriorPosition p hInterior)
      have hqChild : q ∈ pairedChildren R (some p) :=
        (saturated_firstInterior_is_pairedChild R hSat p hInterior).2
      have hpos : 0 < pairedChildCount R (some p) := by
        rw [pairedChildCount]
        exact Finset.card_pos.mpr ⟨q, hqChild⟩
      omega
    simp [pairedChildConcatWord, pairedChildWordPrefix, pairedNodeOpenWord,
      hzero, hopen]
  · have hChildren : 0 < pairedChildCount R (some p) :=
      Nat.pos_of_ne_zero hzero
    have hslice := pairedChildWordPrefix_eq_slice z R hSat (some p)
      (pairedChildCount R (some p)) le_rfl hChildren
    have hlast := orderedPairedChild_last_right_nonroot R hSat p hChildren
    unfold pairedChildConcatWord pairedNodeOpenWord
    rw [hslice]
    simp only [pairedChildInterfaceStart]
    have hendpoint :
        (orderedPairedChild R (some p)
          ⟨pairedChildCount R (some p) - 1, by omega⟩).val.right.val + 1 =
          p.val.right.val := hlast
    rw [hendpoint]
    congr 1

/-- Upward interval-tree induction: every target-pair closed interval is an
atomic design. -/
theorem pairedNode_atomicDesign_of_localDistinctness
    (z : Sequence n) (R : SecondaryStructure n)
    (hSat : SaturatedStructure R) (hCompat : StructureCompatible z R)
    (hLocal : LocallyDistinct R z) (p : PairedNode R) :
    AtomicDesign (pairedNodeWord z p) (pairedNodeTarget z p) := by
  have main : ∀ m : Nat, ∀ p : PairedNode R,
      p.val.closedLength = m →
      AtomicDesign (pairedNodeWord z p) (pairedNodeTarget z p) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro p hpLength
        have hDesign : ∀ i : Fin (pairedChildCount R (some p)),
            AtomicDesign
              (pairedNodeWord z (orderedPairedChild R (some p) i))
              (pairedNodeTarget z (orderedPairedChild R (some p) i)) := by
          intro i
          let q := orderedPairedChild R (some p) i
          have hqMem : q ∈ pairedChildren R (some p) :=
            orderedPairedChild_mem R (some p) i
          have hqParent : parent R (Sum.inl q) = some p := by
            simpa [pairedChildren] using hqMem
          have hpq := parent_pair_contains R hqParent
          have hLengthLt : q.val.closedLength < m := by
            rw [← hpLength]
            simp only [PairedNode.StrictlyContains] at hpq
            have hpqLeft : p.val.left.val < q.val.left.val := hpq.1
            have hpqRight : q.val.right.val < p.val.right.val := hpq.2
            have hpOrder : p.val.left.val < p.val.right.val := p.val.ordered
            have hqOrder : q.val.left.val < q.val.right.val := q.val.ordered
            unfold Arc.closedLength
            omega
          exact ih q.val.closedLength hLengthLt q rfl
        let blocks := pairedChildAtomicBlocks z R (some p) hDesign
        have hDistinct :
            AtomicDesignBlock.FirstLettersPairwiseDistinct blocks := by
          exact firstLettersPairwiseDistinct_pairedChildAtomicBlocks
            z R (some p) (hLocal.2 p).1 hDesign
        have hAvoid : AtomicDesignBlock.FirstLettersAvoid blocks (z p.val.right) := by
          apply firstLettersAvoid_pairedChildAtomicBlocks z R (some p)
            (z p.val.right) _ hDesign
          intro i
          exact (hLocal.2 p).2 _ (orderedPairedChild_mem R (some p) i)
        have hOuterCompat : Compatible (z p.val.left) (z p.val.right) :=
          hCompat p.val p.property
        have hWrapped := AtomicDesignBlock.wrap_atomicDesigns
          (z p.val.left) (z p.val.right) blocks hOuterCompat hDistinct hAvoid
        have hConcatOpen : AtomicDesignBlock.concatWord blocks =
            pairedNodeOpenWord z p := by
          exact (concatWord_pairedChildAtomicBlocks z R (some p) hDesign).trans
            (pairedChildConcatWord_nonroot_eq_openWord z R hSat p)
        have hWord : Word.wrap (z p.val.left) (z p.val.right)
              (AtomicDesignBlock.concatWord blocks) = pairedNodeWord z p := by
          rw [hConcatOpen]
          exact (pairedNodeWord_eq_wrap_openWord z p).symm
        let displayedTarget := SecondaryStructure.wrapWord
          (z p.val.left) (z p.val.right)
          (AtomicDesignBlock.concatWord blocks)
          (AtomicDesignBlock.concatTarget blocks)
        have hDisplayedOnActual : AtomicDesign (pairedNodeWord z p)
            (castStructureToEqualWord hWord displayedTarget) :=
          atomicDesign_castStructureToEqualWord hWord displayedTarget hWrapped
        have hActualEq : pairedNodeTarget z p =
            castStructureToEqualWord hWord displayedTarget :=
          hDisplayedOnActual.2.2.2 (pairedNodeTarget z p)
            (saturated_pairedNodeTarget z hSat p)
            (compatible_pairedNodeTarget z hCompat p)
        rw [hActualEq]
        exact hDisplayedOnActual
  exact main p.val.closedLength p rfl

/-! ## Root uniqueness -/

/-- Reindex a public fixed-length structure onto the list word of the same
complete sequence. -/
def structureOnSequenceWord (z : Sequence n) (S : SecondaryStructure n) :
    SecondaryStructure (Sequence.toWord z).length :=
  S.reindexOrderIso (Fin.castOrderIso (Sequence.length_toWord z).symm)

theorem structureOnSequenceWord_injective (z : Sequence n) :
    Function.Injective (structureOnSequenceWord z) := by
  unfold structureOnSequenceWord SecondaryStructure.reindexOrderIso
  exact SecondaryStructure.mapOrderEmbedding_injective _

theorem saturated_structureOnSequenceWord
    (z : Sequence n) {S : SecondaryStructure n}
    (hSat : SaturatedStructure S) :
    SaturatedStructure (structureOnSequenceWord z S) := by
  exact (SecondaryStructure.saturated_reindexOrderIso_iff _ S).2 hSat

theorem compatible_structureOnSequenceWord
    (z : Sequence n) {S : SecondaryStructure n}
    (hCompat : StructureCompatible z S) :
    StructureCompatible (Sequence.toWord z).toSequence
      (structureOnSequenceWord z S) := by
  rw [structureOnSequenceWord,
    SecondaryStructure.structureCompatible_reindexOrderIso_iff]
  have hseq :
      (fun i : Fin n => (Sequence.toWord z).toSequence
        ((Fin.castOrderIso (Sequence.length_toWord z).symm) i)) = z := by
    funext i
    exact Sequence.toSequence_toWord_apply z i
  rw [hseq]
  exact hCompat

/-- Manuscript Theorem 19: a saturated compatible target satisfying the local
child-letter conditions is the unique compatible noncrossing perfect matching
of the complete sequence. -/
theorem saturated_unique_of_localDistinctness
    (R : SecondaryStructure n) (z : Sequence n)
    (hRSat : SaturatedStructure R)
    (hRComp : StructureCompatible z R)
    (hLocal : LocallyDistinct R z)
    (P : SecondaryStructure n)
    (hPSat : SaturatedStructure P)
    (hPComp : StructureCompatible z P) :
    P = R := by
  by_cases hn : n = 0
  · subst n
    exact saturated_unique_zero R P
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hDesign : ∀ i : Fin (pairedChildCount R none),
        AtomicDesign (pairedNodeWord z (orderedPairedChild R none i))
          (pairedNodeTarget z (orderedPairedChild R none i)) := by
      intro i
      exact pairedNode_atomicDesign_of_localDistinctness z R hRSat hRComp
        hLocal (orderedPairedChild R none i)
    let blocks := pairedChildAtomicBlocks z R none hDesign
    have hRootChild := saturatedPairedNodeAt_zero_mem_rootChildren R hRSat hnPos
    have hChildren : 0 < pairedChildCount R none := by
      rw [pairedChildCount]
      exact Finset.card_pos.mpr ⟨_, hRootChild⟩
    have hBlocksNonempty : blocks ≠ [] := by
      simpa [blocks, pairedChildAtomicBlocks] using
        (Nat.ne_of_gt hChildren)
    have hDistinct : AtomicDesignBlock.FirstLettersPairwiseDistinct blocks :=
      firstLettersPairwiseDistinct_pairedChildAtomicBlocks
        z R none hLocal.1 hDesign
    have hWord : AtomicDesignBlock.concatWord blocks = Sequence.toWord z :=
      (concatWord_pairedChildAtomicBlocks z R none hDesign).trans
        (pairedChildConcatWord_root_eq_toWord z R hRSat hnPos)
    let Pword := structureOnSequenceWord z P
    let Rword := structureOnSequenceWord z R
    let Pblocks := castStructureToEqualWord hWord.symm Pword
    let Rblocks := castStructureToEqualWord hWord.symm Rword
    have hPblocksSat : SaturatedStructure Pblocks := by
      exact (saturated_castStructureToEqualWord hWord.symm Pword).2
        (saturated_structureOnSequenceWord z hPSat)
    have hRblocksSat : SaturatedStructure Rblocks := by
      exact (saturated_castStructureToEqualWord hWord.symm Rword).2
        (saturated_structureOnSequenceWord z hRSat)
    have hPblocksComp : StructureCompatible
        (AtomicDesignBlock.concatWord blocks).toSequence Pblocks := by
      exact (compatible_castStructureToEqualWord hWord.symm Pword).2
        (compatible_structureOnSequenceWord z hPComp)
    have hRblocksComp : StructureCompatible
        (AtomicDesignBlock.concatWord blocks).toSequence Rblocks := by
      exact (compatible_castStructureToEqualWord hWord.symm Rword).2
        (compatible_structureOnSequenceWord z hRComp)
    have hPEq := AtomicDesignBlock.concatTarget_unique blocks hBlocksNonempty
      hDistinct Pblocks hPblocksSat hPblocksComp
    have hREq := AtomicDesignBlock.concatTarget_unique blocks hBlocksNonempty
      hDistinct Rblocks hRblocksSat hRblocksComp
    have hCastEq : Pblocks = Rblocks := hPEq.trans hREq.symm
    have hWordEq : Pword = Rword :=
      castStructureToEqualWord_injective hWord.symm hCastEq
    exact structureOnSequenceWord_injective z hWordEq

/-- Predicate-form corollary convenient for callers that quantify the
competitor separately. -/
theorem saturated_uniqueMatching_of_localDistinctness
    (R : SecondaryStructure n) (z : Sequence n)
    (hRSat : SaturatedStructure R)
    (hRComp : StructureCompatible z R)
    (hLocal : LocallyDistinct R z) :
    ∀ P : SecondaryStructure n,
      SaturatedStructure P → StructureCompatible z P → P = R := by
  intro P hPSat hPComp
  exact saturated_unique_of_localDistinctness R z hRSat hRComp hLocal
    P hPSat hPComp

end RNA
