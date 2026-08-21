module

public import RNA.AtMostTwoShort.TargetClass
public import RNA.HelixSubtree

@[expose] public section

set_option autoImplicit false

/-!
# Short-helix resources in actual helix subtrees

The subtree count is defined on maximal helices, using their canonical head
nodes to test membership in `pairedHelixSubtree`.  The exact outgoing-forest
partition then gives an additive resource equation at every helix and at the
virtual root.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Length-two maximal helices whose canonical heads lie in the complete
paired subtree rooted at `H`. -/
def shortHelicesInSubtree (T : SecondaryStructure n) (H : MaximalHelix T) :
    Finset (MaximalHelix T) :=
  (lengthTwoHelices T).filter
    (fun K => K.headNode ∈ pairedHelixSubtree T H)

/-- Number of length-two maximal helices in the complete helix subtree. -/
def shortHelixSubtreeCount (T : SecondaryStructure n)
    (H : MaximalHelix T) : Nat :=
  (shortHelicesInSubtree T H).card

@[simp]
theorem mem_shortHelicesInSubtree_iff (H K : MaximalHelix T) :
    K ∈ shortHelicesInSubtree T H ↔
      K.length = 2 ∧ K.headNode ∈ pairedHelixSubtree T H := by
  simp [shortHelicesInSubtree]

theorem shortHelicesInSubtree_subset_lengthTwoHelices (H : MaximalHelix T) :
    shortHelicesInSubtree T H ⊆ lengthTwoHelices T :=
  Finset.filter_subset _ _

theorem shortHelixSubtreeCount_le_shortHelixCount (H : MaximalHelix T) :
    shortHelixSubtreeCount T H ≤ shortHelixCount T := by
  exact Finset.card_le_card (shortHelicesInSubtree_subset_lengthTwoHelices H)

/-- A length-two helix contributes itself to its complete subtree count. -/
theorem shortHelixSubtreeCount_pos_of_length_two (H : MaximalHelix T)
    (hlen : H.length = 2) : 0 < shortHelixSubtreeCount T H := by
  rw [shortHelixSubtreeCount, Finset.card_pos]
  exact ⟨H, (mem_shortHelicesInSubtree_iff H H).2
    ⟨hlen, headNode_mem_pairedHelixSubtree H⟩⟩

/-- A zero-resource subtree cannot have a short root helix. -/
theorem length_ne_two_of_shortHelixSubtreeCount_eq_zero (H : MaximalHelix T)
    (hzero : shortHelixSubtreeCount T H = 0) : H.length ≠ 2 := by
  intro hlen
  have hpos := shortHelixSubtreeCount_pos_of_length_two H hlen
  omega

/-- The current helix contributes one resource precisely when its own length
is two. -/
def currentShortHelix (H : MaximalHelix T) : Finset (MaximalHelix T) :=
  if H.length = 2 then {H} else ∅

@[simp]
theorem mem_currentShortHelix_iff (H K : MaximalHelix T) :
    K ∈ currentShortHelix H ↔ K = H ∧ H.length = 2 := by
  by_cases hlen : H.length = 2 <;> simp [currentShortHelix, hlen]

private theorem eq_parent_of_head_mem_helixMemberNodes
    (H K : MaximalHelix T)
    (hhead : K.headNode ∈ helixMemberNodes T H) : K = H := by
  apply MaximalHelix.eq_of_common_member
    (H := K) (K := H) (a := K.headNode.val)
  · exact (mem_helixMemberNodes_iff K K.headNode).1
      (headNode_mem_helixMemberNodes K)
  · exact (mem_helixMemberNodes_iff H K.headNode).1 hhead

/-- Exact finite-set form of the short-resource decomposition. -/
theorem shortHelicesInSubtree_decomposition (H : MaximalHelix T) :
    shortHelicesInSubtree T H =
      currentShortHelix H ∪
        Finset.univ.biUnion
          (fun i : Fin (pairedChildCount T (some H.terminalNode)) =>
            shortHelicesInSubtree T (outgoingHelix T H i)) := by
  ext K
  constructor
  · intro hK
    have hlen : K.length = 2 :=
      (mem_shortHelicesInSubtree_iff H K).1 hK |>.1
    have hhead : K.headNode ∈ pairedHelixSubtree T H :=
      (mem_shortHelicesInSubtree_iff H K).1 hK |>.2
    have hdecomp :
        K.headNode ∈
          helixMemberNodes T H ∪ outgoingPairedHelixSubtreeUnion T H := by
      rw [← pairedHelixSubtree_decomposition H]
      exact hhead
    rcases Finset.mem_union.1 hdecomp with hcurrent | houtgoing
    · apply Finset.mem_union_left
      have hEq : K = H := eq_parent_of_head_mem_helixMemberNodes H K hcurrent
      exact (mem_currentShortHelix_iff H K).2
        ⟨hEq, by simpa [← hEq] using hlen⟩
    · apply Finset.mem_union_right
      obtain ⟨i, hi⟩ :=
        (mem_outgoingPairedHelixSubtreeUnion_iff H K.headNode).1 houtgoing
      apply Finset.mem_biUnion.2
      refine ⟨i, Finset.mem_univ i, ?_⟩
      exact (mem_shortHelicesInSubtree_iff (outgoingHelix T H i) K).2
        ⟨hlen, hi⟩
  · intro hK
    rcases Finset.mem_union.1 hK with hcurrent | houtgoing
    · obtain ⟨hEq, hHlen⟩ := (mem_currentShortHelix_iff H K).1 hcurrent
      subst K
      exact (mem_shortHelicesInSubtree_iff H H).2
        ⟨hHlen, headNode_mem_pairedHelixSubtree H⟩
    · obtain ⟨i, _hiUniv, hi⟩ := Finset.mem_biUnion.1 houtgoing
      obtain ⟨hlen, hhead⟩ :=
        (mem_shortHelicesInSubtree_iff (outgoingHelix T H i) K).1 hi
      exact (mem_shortHelicesInSubtree_iff H K).2
        ⟨hlen, pairedHelixSubtree_outgoing_subset H i hhead⟩

private theorem outgoingShortHelices_pairwiseDisjoint (H : MaximalHelix T) :
    ((Finset.univ :
      Finset (Fin (pairedChildCount T (some H.terminalNode)))) :
        Set (Fin (pairedChildCount T (some H.terminalNode)))).PairwiseDisjoint
      (fun i => shortHelicesInSubtree T (outgoingHelix T H i)) := by
  intro i _hi j _hj hij
  change Disjoint
    (shortHelicesInSubtree T (outgoingHelix T H i))
    (shortHelicesInSubtree T (outgoingHelix T H j))
  rw [Finset.disjoint_left]
  intro K hKi hKj
  have hheadi :=
    (mem_shortHelicesInSubtree_iff (outgoingHelix T H i) K).1 hKi |>.2
  have hheadj :=
    (mem_shortHelicesInSubtree_iff (outgoingHelix T H j) K).1 hKj |>.2
  exact (Finset.disjoint_left.1
    (pairedHelixSubtree_outgoing_disjoint H hij)) hheadi hheadj

private theorem currentShortHelix_disjoint_outgoing (H : MaximalHelix T) :
    Disjoint (currentShortHelix H)
      (Finset.univ.biUnion
        (fun i : Fin (pairedChildCount T (some H.terminalNode)) =>
          shortHelicesInSubtree T (outgoingHelix T H i))) := by
  rw [Finset.disjoint_left]
  intro K hcurrent houtgoing
  obtain ⟨hEq, _hHlen⟩ := (mem_currentShortHelix_iff H K).1 hcurrent
  subst K
  obtain ⟨i, _hiUniv, hi⟩ := Finset.mem_biUnion.1 houtgoing
  have hheadChild :=
    (mem_shortHelicesInSubtree_iff (outgoingHelix T H i) H).1 hi |>.2
  exact (Finset.disjoint_left.1 (helixMemberNodes_disjoint_outgoing H i))
    (headNode_mem_helixMemberNodes H) hheadChild

/-- Exact parent-indicator plus actual-outgoing-child sum decomposition. -/
theorem shortHelixSubtreeCount_decomposition (H : MaximalHelix T) :
    shortHelixSubtreeCount T H =
      (if H.length = 2 then 1 else 0) +
        ∑ i : Fin (pairedChildCount T (some H.terminalNode)),
          shortHelixSubtreeCount T (outgoingHelix T H i) := by
  rw [shortHelixSubtreeCount, shortHelicesInSubtree_decomposition H,
    Finset.card_union_of_disjoint (currentShortHelix_disjoint_outgoing H),
    Finset.card_biUnion (outgoingShortHelices_pairwiseDisjoint H)]
  by_cases hlen : H.length = 2 <;>
    simp [currentShortHelix, shortHelixSubtreeCount, hlen]

theorem shortHelicesInSubtree_outgoing_subset (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    shortHelicesInSubtree T (outgoingHelix T H i) ⊆
      shortHelicesInSubtree T H := by
  intro K hK
  obtain ⟨hlen, hhead⟩ :=
    (mem_shortHelicesInSubtree_iff (outgoingHelix T H i) K).1 hK
  exact (mem_shortHelicesInSubtree_iff H K).2
    ⟨hlen, pairedHelixSubtree_outgoing_subset H i hhead⟩

/-- Every actual child subtree has no more short resources than its parent. -/
theorem shortHelixSubtreeCount_outgoing_le (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    shortHelixSubtreeCount T (outgoingHelix T H i) ≤
      shortHelixSubtreeCount T H := by
  exact Finset.card_le_card (shortHelicesInSubtree_outgoing_subset H i)

/-- Under the global class hypothesis, every helix subtree carries at most
two short resources. -/
theorem shortHelixSubtreeCount_le_two (hK : InTargetClassKLeTwo T)
    (H : MaximalHelix T) : shortHelixSubtreeCount T H ≤ 2 :=
  (shortHelixSubtreeCount_le_shortHelixCount H).trans
    (targetClassKLeTwo_shortHelixCount_le hK)

/-- Actual outgoing slots whose subtrees carry at least one short helix. -/
noncomputable def loopShortSupport (T : SecondaryStructure n)
    (H : MaximalHelix T) :
    Finset (Fin (pairedChildCount T (some H.terminalNode))) :=
  Finset.univ.filter
    (fun i => 0 < shortHelixSubtreeCount T (outgoingHelix T H i))

@[simp]
theorem mem_loopShortSupport_iff (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    i ∈ loopShortSupport T H ↔
      0 < shortHelixSubtreeCount T (outgoingHelix T H i) := by
  simp [loopShortSupport]

@[simp]
theorem not_mem_loopShortSupport_iff_count_eq_zero (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    i ∉ loopShortSupport T H ↔
      shortHelixSubtreeCount T (outgoingHelix T H i) = 0 := by
  simp [loopShortSupport]

private theorem support_card_le_sum {m : Nat} (f : Fin m → Nat) :
    (Finset.univ.filter (fun i => 0 < f i)).card ≤ ∑ i, f i := by
  calc
    (Finset.univ.filter (fun i => 0 < f i)).card =
        ∑ i ∈ Finset.univ.filter (fun i => 0 < f i), 1 := by simp
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 < f i), f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.1 hi).2
    _ ≤ ∑ i, f i := by
      exact Finset.sum_le_sum_of_subset
        (Finset.filter_subset _ Finset.univ)

theorem loopShortSupport_card_le_shortHelixSubtreeCount
    (H : MaximalHelix T) :
    (loopShortSupport T H).card ≤ shortHelixSubtreeCount T H := by
  have hsupport := support_card_le_sum
    (fun i : Fin (pairedChildCount T (some H.terminalNode)) =>
      shortHelixSubtreeCount T (outgoingHelix T H i))
  rw [shortHelixSubtreeCount_decomposition H]
  exact hsupport.trans (Nat.le_add_left _ _)

theorem loopShortSupport_card_le_two (hK : InTargetClassKLeTwo T)
    (H : MaximalHelix T) : (loopShortSupport T H).card ≤ 2 :=
  (loopShortSupport_card_le_shortHelixSubtreeCount H).trans
    (shortHelixSubtreeCount_le_two hK H)

/-- Two positive child resources consume the full global budget.  Hence the
current helix cannot itself be short. -/
theorem two_positive_outgoing_implies_length_ne_two
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    {i j : Fin (pairedChildCount T (some H.terminalNode))}
    (hij : i ≠ j)
    (hi : 0 < shortHelixSubtreeCount T (outgoingHelix T H i))
    (hj : 0 < shortHelixSubtreeCount T (outgoingHelix T H j)) :
    H.length ≠ 2 := by
  intro hHshort
  have hsum : 2 ≤
      ∑ k : Fin (pairedChildCount T (some H.terminalNode)),
        shortHelixSubtreeCount T (outgoingHelix T H k) := by
    have hiMem : i ∈ loopShortSupport T H :=
      (mem_loopShortSupport_iff H i).2 hi
    have hjMem : j ∈ loopShortSupport T H :=
      (mem_loopShortSupport_iff H j).2 hj
    have hpairSubset : ({i, j} :
        Finset (Fin (pairedChildCount T (some H.terminalNode)))) ⊆
        loopShortSupport T H := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hiMem
      · exact hjMem
    have hcard : 2 ≤ (loopShortSupport T H).card := by
      have := Finset.card_le_card hpairSubset
      simpa [hij] using this
    have hsupport := support_card_le_sum
      (fun k : Fin (pairedChildCount T (some H.terminalNode)) =>
        shortHelixSubtreeCount T (outgoingHelix T H k))
    exact hcard.trans (by simpa [loopShortSupport] using hsupport)
  have hparent := shortHelixSubtreeCount_le_two hK H
  rw [shortHelixSubtreeCount_decomposition H] at hparent
  simp [hHshort] at hparent
  omega

theorem two_positive_outgoing_implies_length_at_least_three
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    {i j : Fin (pairedChildCount T (some H.terminalNode))}
    (hij : i ≠ j)
    (hi : 0 < shortHelixSubtreeCount T (outgoingHelix T H i))
    (hj : 0 < shortHelixSubtreeCount T (outgoingHelix T H j)) :
    3 ≤ H.length :=
  targetClassKLeTwo_nonshort_length_at_least_three hK H
    (two_positive_outgoing_implies_length_ne_two hK H hij hi hj)

theorem loopShortSupport_card_eq_two_length_ne_two
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (hcard : (loopShortSupport T H).card = 2) : H.length ≠ 2 := by
  obtain ⟨i, j, hij, hsupport⟩ := Finset.card_eq_two.1 hcard
  have hi : i ∈ loopShortSupport T H := by simp [hsupport]
  have hj : j ∈ loopShortSupport T H := by simp [hsupport]
  exact two_positive_outgoing_implies_length_ne_two hK H hij
    ((mem_loopShortSupport_iff H i).1 hi)
    ((mem_loopShortSupport_iff H j).1 hj)

theorem loopShortSupport_card_eq_two_length_at_least_three
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (hcard : (loopShortSupport T H).card = 2) : 3 ≤ H.length :=
  targetClassKLeTwo_nonshort_length_at_least_three hK H
    (loopShortSupport_card_eq_two_length_ne_two hK H hcard)

/-! ## The virtual root -/

/-- Exact partition of all length-two helices among actual root slots. -/
theorem lengthTwoHelices_root_decomposition (T : SecondaryStructure n) :
    lengthTwoHelices T =
      Finset.univ.biUnion
        (fun i : Fin (pairedChildCount T none) =>
          shortHelicesInSubtree T (outgoingHelixAtRootSlot T i)) := by
  ext K
  constructor
  · intro hK
    have hlen := (mem_lengthTwoHelices_iff T K).1 hK
    have hroot : K.headNode ∈ rootPairedHelixSubtreeUnion T := by
      rw [rootPairedHelixSubtreeUnion_eq_univ T]
      simp
    obtain ⟨i, hi⟩ :=
      (mem_rootPairedHelixSubtreeUnion_iff K.headNode).1 hroot
    apply Finset.mem_biUnion.2
    exact ⟨i, Finset.mem_univ i,
      (mem_shortHelicesInSubtree_iff (outgoingHelixAtRootSlot T i) K).2
        ⟨hlen, hi⟩⟩
  · intro hK
    obtain ⟨i, _hiUniv, hi⟩ := Finset.mem_biUnion.1 hK
    exact (mem_lengthTwoHelices_iff T K).2
      ((mem_shortHelicesInSubtree_iff
        (outgoingHelixAtRootSlot T i) K).1 hi).1

private theorem rootShortHelices_pairwiseDisjoint (T : SecondaryStructure n) :
    ((Finset.univ : Finset (Fin (pairedChildCount T none))) :
      Set (Fin (pairedChildCount T none))).PairwiseDisjoint
        (fun i => shortHelicesInSubtree T (outgoingHelixAtRootSlot T i)) := by
  intro i _hi j _hj hij
  change Disjoint
    (shortHelicesInSubtree T (outgoingHelixAtRootSlot T i))
    (shortHelicesInSubtree T (outgoingHelixAtRootSlot T j))
  rw [Finset.disjoint_left]
  intro K hKi hKj
  have hheadi :=
    (mem_shortHelicesInSubtree_iff (outgoingHelixAtRootSlot T i) K).1 hKi |>.2
  have hheadj :=
    (mem_shortHelicesInSubtree_iff (outgoingHelixAtRootSlot T j) K).1 hKj |>.2
  exact (Finset.disjoint_left.1 (pairedHelixSubtree_root_disjoint hij))
    hheadi hheadj

/-- Exact root sum: the all-unpaired target is the empty sum case. -/
theorem shortHelixCount_root_decomposition (T : SecondaryStructure n) :
    shortHelixCount T =
      ∑ i : Fin (pairedChildCount T none),
        shortHelixSubtreeCount T (outgoingHelixAtRootSlot T i) := by
  rw [shortHelixCount, lengthTwoHelices_root_decomposition T,
    Finset.card_biUnion (rootShortHelices_pairwiseDisjoint T)]
  simp [shortHelixSubtreeCount]

/-- Actual root slots whose helix subtrees carry at least one short helix. -/
noncomputable def rootShortSupport (T : SecondaryStructure n) :
    Finset (Fin (pairedChildCount T none)) :=
  Finset.univ.filter
    (fun i => 0 < shortHelixSubtreeCount T (outgoingHelixAtRootSlot T i))

@[simp]
theorem mem_rootShortSupport_iff (T : SecondaryStructure n)
    (i : Fin (pairedChildCount T none)) :
    i ∈ rootShortSupport T ↔
      0 < shortHelixSubtreeCount T (outgoingHelixAtRootSlot T i) := by
  simp [rootShortSupport]

@[simp]
theorem not_mem_rootShortSupport_iff_count_eq_zero
    (T : SecondaryStructure n) (i : Fin (pairedChildCount T none)) :
    i ∉ rootShortSupport T ↔
      shortHelixSubtreeCount T (outgoingHelixAtRootSlot T i) = 0 := by
  simp [rootShortSupport]

theorem rootShortSupport_card_le_shortHelixCount (T : SecondaryStructure n) :
    (rootShortSupport T).card ≤ shortHelixCount T := by
  have hsupport := support_card_le_sum
    (fun i : Fin (pairedChildCount T none) =>
      shortHelixSubtreeCount T (outgoingHelixAtRootSlot T i))
  rw [shortHelixCount_root_decomposition T]
  exact hsupport

/-- At most two actual root-child helix subtrees have positive short count. -/
theorem rootShortSupport_card_le_two (hK : InTargetClassKLeTwo T) :
    (rootShortSupport T).card ≤ 2 :=
  (rootShortSupport_card_le_shortHelixCount T).trans
    (targetClassKLeTwo_shortHelixCount_le hK)

end RNA
