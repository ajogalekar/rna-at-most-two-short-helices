module

public import RNA.AtMostTwoShort.ResourceRoot
public import RNA.AtMostTwoShort.SubtreeConstruction

@[expose] public section

set_option autoImplicit false

/-!
# Global coloring with at most two short helices

The positive-degree branch recursively colors every actual root-child helix
subtree using the port assigned to that child by the resource root allocation.
Those exact domains are pairwise disjoint and partition all target pairs.  The
degree-zero branch is separate: the root partition proves that there are no
paired nodes, so its coloring is genuinely the empty function and every
unpaired node has exact level zero.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-! ## The positive-degree root forest -/

/-- The exact recursive coloring selected for every actual root child. -/
noncomputable def constructedResourceRootSubtreeColorings
    (hK : InTargetClassKLeTwo T) (A : ResourceRootAllocation T hK) :
    RootSubtreeColorings T :=
  fun i => constructedResourceSubtreeColoring hK A.xi
    (outgoingHelixAtRootSlot T i) A.entry (A.ports i)
      (A.requiredOutgoing i)

/-- The extension-stable certificate belonging to a root-child component. -/
noncomputable def constructedResourceRootSubtreeCertificate
    (hK : InTargetClassKLeTwo T) (A : ResourceRootAllocation T hK)
    (i : Fin (pairedChildCount T none)) :
    ResourceSubtreeCertificate hK (outgoingHelixAtRootSlot T i)
      A.xi A.entry (A.ports i)
        (constructedResourceRootSubtreeColorings hK A i) := by
  unfold constructedResourceRootSubtreeColorings
  exact constructedResourceSubtreeCertificate hK A.xi
    (outgoingHelixAtRootSlot T i) A.entry (A.ports i)
      (A.requiredOutgoing i)

/-- Flatten and totalize the pairwise-disjoint root-child assignments. -/
noncomputable def assembledResourceRootColoring
    (hK : InTargetClassKLeTwo T) (A : ResourceRootAllocation T hK) :
    Coloring T :=
  coloringOfRootSubtrees (constructedResourceRootSubtreeColorings hK A)

/-- Every actual root child enters at exact level zero.  The root allocation
chooses either `xi = 0` or `eta = 0`, and its `entry` is that chosen residue. -/
theorem ResourceRootAllocation.entry_eq_zero
    {hK : InTargetClassKLeTwo T} (A : ResourceRootAllocation T hK) :
    A.entry = 0 := by
  by_cases hsmall : pairedChildCount T none ≤ 2
  · have hentry : A.entry = A.xi := A.entry_eq_xi_of_small hsmall
    exact hentry.trans (A.xi_eq_zero_of_entry_xi hentry)
  · have hlarge : 3 ≤ pairedChildCount T none := by omega
    have hentry : A.entry = A.eta := A.entry_eq_eta_of_large hlarge
    exact hentry.trans (A.eta_eq_zero_of_entry_eta hentry)

/-- The extension-stable child certificate instantiated in the complete
flattened root forest. -/
theorem assembledResourceRootSubtreePostcondition
    (hK : InTargetClassKLeTwo T) (A : ResourceRootAllocation T hK)
    (i : Fin (pairedChildCount T none)) :
    ResourceSubtreePostcondition hK (assembledResourceRootColoring hK A)
      (outgoingHelixAtRootSlot T i) A.xi A.entry (A.ports i)
      (constructedResourceRootSubtreeCertificate hK A i).endpoint
      (constructedResourceRootSubtreeCertificate hK A i).transfer
      (constructedResourceRootSubtreeCertificate hK A i).allocation := by
  apply (constructedResourceRootSubtreeCertificate hK A i).sound
  · exact coloringOfRootSubtrees_extends
      (constructedResourceRootSubtreeColorings hK A) i
  · have hchild : (outgoingHelixAtRootSlot T i).headNode ∈
        pairedChildren T none := by
      rw [outgoingHelixAtRootSlot_head]
      exact orderedPairedChild_mem T none i
    rw [entryLevel_of_mem_rootChildren
      (assembledResourceRootColoring hK A) hchild]
    exact A.entry_eq_zero

/-- Every actual root-child head receives its own allocated port. -/
theorem assembledResourceRootColoring_childPortsInstalled
    (hK : InTargetClassKLeTwo T) (A : ResourceRootAllocation T hK) :
    ChildPortsInstalled (assembledResourceRootColoring hK A) none A.ports := by
  intro i
  have hhead := (assembledResourceRootSubtreePostcondition hK A i).headColor
  rw [outgoingHelixAtRootSlot_head] at hhead
  exact hhead

/-- Root properness is exactly the proved actual port exposure; every nonroot
exposure belongs to the unique root-child certificate containing it. -/
theorem assembledResourceRootColoring_proper
    (hK : InTargetClassKLeTwo T) (A : ResourceRootAllocation T hK) :
    ProperColoring (assembledResourceRootColoring hK A) := by
  intro p
  cases p with
  | none =>
      rw [exposedMultiset_root,
        childColorMultiset_eq_portMultiset_of_childPortsInstalled
          (assembledResourceRootColoring hK A) none A.ports
          (assembledResourceRootColoring_childPortsInstalled hK A)]
      exact A.proper
  | some q =>
      have hqAll : q ∈ rootPairedHelixSubtreeUnion T := by
        rw [rootPairedHelixSubtreeUnion_eq_univ]
        exact Finset.mem_univ q
      obtain ⟨i, hi⟩ :=
        (mem_rootPairedHelixSubtreeUnion_iff q).1 hqAll
      exact (assembledResourceRootSubtreePostcondition hK A i).proper q hi

/-- The positive-degree root forest has the named strong separation residue.
Root-unpaired positions are handled at exact level zero, independently of all
subtree proofs. -/
theorem assembledResourceRootColoring_strongTwoSeparatedWith
    (hK : InTargetClassKLeTwo T) (A : ResourceRootAllocation T hK) :
    StrongTwoSeparatedWith (assembledResourceRootColoring hK A) A.xi := by
  constructor
  · intro u
    by_cases hu : u ∈ rootUnpairedHelixSubtreeUnion T
    · obtain ⟨i, hi⟩ :=
        (mem_rootUnpairedHelixSubtreeUnion_iff u).1 hu
      exact (assembledResourceRootSubtreePostcondition hK A i).unpairedAt u hi
    · have huRoot : u ∈ unpairedChildren T none :=
        (mem_root_unpairedChildren_iff_not_mem_rootSubtree u).2 hu
      have hlevel :=
        unpairedLevel_of_mem_rootChildren
          (assembledResourceRootColoring hK A) huRoot
      have hsmall : pairedChildCount T none ≤ 2 :=
        root_pairedChildren_le_two_of_unpaired T
          (targetClassKLeTwo_motifFree hK) ⟨u, huRoot⟩
      have hentry : A.entry = A.xi := A.entry_eq_xi_of_small hsmall
      have hxi : A.xi = 0 := A.xi_eq_zero_of_entry_xi hentry
      rw [hlevel, hxi]
      rfl
  · intro g hgrey
    have hgAll : g ∈ rootPairedHelixSubtreeUnion T := by
      rw [rootPairedHelixSubtreeUnion_eq_univ]
      exact Finset.mem_univ g
    obtain ⟨i, hi⟩ :=
      (mem_rootPairedHelixSubtreeUnion_iff g).1 hgAll
    exact (assembledResourceRootSubtreePostcondition hK A i).greysAt
      g hi hgrey

/-! ## The degree-zero root -/

/-- Root degree zero leaves no target paired node anywhere in the interval
forest. -/
theorem noPairedNode_of_rootDegreeZero
    (hzero : pairedChildCount T none = 0) (p : PairedNode T) : False := by
  have hpAll : p ∈ rootPairedHelixSubtreeUnion T := by
    rw [rootPairedHelixSubtreeUnion_eq_univ]
    exact Finset.mem_univ p
  obtain ⟨i, _hi⟩ :=
    (mem_rootPairedHelixSubtreeUnion_iff p).1 hpAll
  exact Fin.elim0 (Fin.cast hzero i)

/-- The empty coloring on a target whose root has no paired child. -/
def rootDegreeZeroColoring
    (hzero : pairedChildCount T none = 0) : Coloring T :=
  fun p => False.elim (noPairedNode_of_rootDegreeZero hzero p)

/-- Empty exposure at the root and vacuity at nonexistent paired nodes give
global properness. -/
theorem rootDegreeZeroColoring_proper
    (hzero : pairedChildCount T none = 0) :
    ProperColoring (rootDegreeZeroColoring hzero) := by
  intro p
  cases p with
  | none =>
      have hempty : pairedChildren T none = ∅ :=
        (pairedChildCount_eq_zero_iff (T := T) none).1 hzero
      simp [exposedMultiset, childColorMultiset, hempty, ProperExposure]
  | some q =>
      exact False.elim (noPairedNode_of_rootDegreeZero hzero q)

/-- With no paired node, every unpaired position is a root child and has
exact level zero; there are no gray nodes. -/
theorem rootDegreeZeroColoring_strongTwoSeparatedWith
    (hzero : pairedChildCount T none = 0) :
    StrongTwoSeparatedWith (rootDegreeZeroColoring hzero) 0 := by
  constructor
  · intro u
    have hparent : parent T (Sum.inr u) = none := by
      cases hp : parent T (Sum.inr u) with
      | none => rfl
      | some p => exact False.elim (noPairedNode_of_rootDegreeZero hzero p)
    have huRoot : u ∈ unpairedChildren T none := by
      simpa [unpairedChildren] using hparent
    rw [unpairedLevel_of_mem_rootChildren
      (rootDegreeZeroColoring hzero) huRoot]
    rfl
  · intro g _hgrey
    exact False.elim (noPairedNode_of_rootDegreeZero hzero g)

/-! ## Canonical global certificate -/

/-- One witness residue, one total coloring, and the complete global
correctness package for the enlarged target class. -/
structure GlobalColoringCertificateLeTwo
    (T : SecondaryStructure n) (hK : InTargetClassKLeTwo T) where
  xi : Parity
  coloring : Coloring T
  proper : ProperColoring coloring
  strong : StrongTwoSeparatedWith coloring xi

/-- Direct global construction.  This explicitly branches on root degree
zero; every positive-degree target uses the same resource induction,
regardless of whether its global short count is zero, one, or two. -/
noncomputable def globalColoringCertificateLeTwo
    (hK : InTargetClassKLeTwo T) : GlobalColoringCertificateLeTwo T hK := by
  by_cases hzero : pairedChildCount T none = 0
  · exact {
      xi := 0
      coloring := rootDegreeZeroColoring hzero
      proper := rootDegreeZeroColoring_proper hzero
      strong := rootDegreeZeroColoring_strongTwoSeparatedWith hzero }
  · have hpositive : 0 < pairedChildCount T none := Nat.pos_of_ne_zero hzero
    let A := completeResourceRootAllocation hK hpositive
    exact {
      xi := A.xi
      coloring := assembledResourceRootColoring hK A
      proper := assembledResourceRootColoring_proper hK A
      strong := assembledResourceRootColoring_strongTwoSeparatedWith hK A }

/-- Witness-bearing residue form of the global coloring theorem. -/
theorem exists_proper_strongTwoSeparatedWith_leTwo
    (hK : InTargetClassKLeTwo T) :
    ∃ xi, ∃ chi : Coloring T,
      ProperColoring chi ∧ StrongTwoSeparatedWith chi xi := by
  let C := globalColoringCertificateLeTwo hK
  exact ⟨C.xi, C.coloring, C.proper, C.strong⟩

/-- Every at-most-two target has a proper strongly two-separated coloring. -/
theorem targetClassLeTwo_admits_proper_strongTwoSeparated
    (hK : InTargetClassKLeTwo T) :
    ∃ chi : Coloring T, ProperColoring chi ∧ StrongTwoSeparated chi := by
  let C := globalColoringCertificateLeTwo hK
  exact ⟨C.coloring, C.proper,
    (strongTwoSeparated_iff_exists_with C.coloring).2 ⟨C.xi, C.strong⟩⟩

/-- Exact-two is a specialization of the resource-induction theorem, not a
separate construction. -/
theorem targetClassK2_admits_proper_strongTwoSeparated
    (hK : InTargetClassK2 T) :
    ∃ chi : Coloring T, ProperColoring chi ∧ StrongTwoSeparated chi :=
  targetClassLeTwo_admits_proper_strongTwoSeparated hK.1

end RNA
