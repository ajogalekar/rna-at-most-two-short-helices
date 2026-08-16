module

public import RNA.SubtreeConstruction

@[expose] public section

set_option autoImplicit false

/-!
# Global assembly of the class-K coloring

The recursive construction assigns an exact-domain coloring to every
root-child helix subtree.  The root partition makes those domains pairwise
disjoint and proves that their union is all target pairs, so the flattened
forest is a total `Coloring`.  Its subtree certificates establish every
nonroot obligation; the selected root allocation establishes the root
exposure and handles the residue of root-unpaired positions.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-! ## The proof-bearing root forest -/

/-- The exact-domain recursive coloring selected for every actual root-child
helix. -/
noncomputable def constructedRootSubtreeColorings
    (hK : InTargetClassK T) (A : RootAllocation T hK) :
    RootSubtreeColorings T :=
  fun i => constructedSubtreeColoring hK A.row.xi A.row.eta rfl
    (outgoingHelixAtRootSlot T i) A.row.entry (A.ports i)
      (A.safeOutgoing i)

/-- The certificate retained for each component of the root forest. -/
noncomputable def constructedRootSubtreeCertificate
    (hK : InTargetClassK T) (A : RootAllocation T hK)
    (i : Fin (pairedChildCount T none)) :
    SubtreeCertificate hK (outgoingHelixAtRootSlot T i)
      A.row.xi A.row.eta A.row.entry (A.ports i)
        (constructedRootSubtreeColorings hK A i) := by
  unfold constructedRootSubtreeColorings
  exact constructedSubtreeCertificate hK A.row.xi A.row.eta rfl
    (outgoingHelixAtRootSlot T i) A.row.entry (A.ports i)
      (A.safeOutgoing i)

/-- Flatten and totalize the pairwise-disjoint root-child subtree colorings. -/
noncomputable def assembledRootColoring
    (hK : InTargetClassK T) (A : RootAllocation T hK) : Coloring T :=
  coloringOfRootSubtrees (constructedRootSubtreeColorings hK A)

/-- Every root-child helix enters the flattened coloring at the residue
specified by the selected root row. -/
theorem assembledRootColoring_entryResidue
    (hK : InTargetClassK T) (A : RootAllocation T hK)
    (i : Fin (pairedChildCount T none)) :
    A.row.entry = levelParity
      (entryLevel (assembledRootColoring hK A)
        (outgoingHelixAtRootSlot T i).headNode) := by
  have hchild : (outgoingHelixAtRootSlot T i).headNode ∈
      pairedChildren T none := by
    rw [outgoingHelixAtRootSlot_head]
    exact orderedPairedChild_mem T none i
  rw [entryLevel_of_mem_rootChildren (assembledRootColoring hK A) hchild]
  cases A.row <;> rfl

/-- The extension-stable recursive certificate instantiated in the complete
root-forest coloring. -/
theorem assembledRootSubtreePostcondition
    (hK : InTargetClassK T) (A : RootAllocation T hK)
    (i : Fin (pairedChildCount T none)) :
    SubtreePostcondition hK (assembledRootColoring hK A)
      (outgoingHelixAtRootSlot T i) A.row.xi A.row.eta A.row.entry
      (A.ports i) (constructedRootSubtreeCertificate hK A i).endpoint
      (constructedRootSubtreeCertificate hK A i).transfer
      (constructedRootSubtreeCertificate hK A i).allocation := by
  apply (constructedRootSubtreeCertificate hK A i).sound
  · exact coloringOfRootSubtrees_extends
      (constructedRootSubtreeColorings hK A) i
  · exact assembledRootColoring_entryResidue hK A i

/-- The head of every root-child helix receives its actual allocated port. -/
theorem assembledRootColoring_childPortsInstalled
    (hK : InTargetClassK T) (A : RootAllocation T hK) :
    ChildPortsInstalled (assembledRootColoring hK A) none A.ports := by
  intro i
  have hhead := (assembledRootSubtreePostcondition hK A i).headColor
  rw [outgoingHelixAtRootSlot_head] at hhead
  exact hhead

/-! ## Global correctness -/

/-- The flattened root forest is proper at the virtual root and at every
target pair. -/
theorem assembledRootColoring_proper
    (hK : InTargetClassK T) (A : RootAllocation T hK) :
    ProperColoring (assembledRootColoring hK A) := by
  intro p
  cases p with
  | none =>
      exact A.properActualExposure (assembledRootColoring hK A)
        (assembledRootColoring_childPortsInstalled hK A)
  | some q =>
      have hqAll : q ∈ rootPairedHelixSubtreeUnion T := by
        rw [rootPairedHelixSubtreeUnion_eq_univ]
        exact Finset.mem_univ q
      obtain ⟨i, hi⟩ :=
        (mem_rootPairedHelixSubtreeUnion_iff q).1 hqAll
      exact (assembledRootSubtreePostcondition hK A i).proper q hi

/-- Root-allocation coverage forces the selected residue to be zero whenever
the target has an unpaired child of the virtual root. -/
theorem RootAllocation.xi_eq_zero_of_hasUnpairedChild
    {hK : InTargetClassK T} (A : RootAllocation T hK)
    (hrow : HasUnpairedChild T none →
      A.row = .xiOne ∨ A.row = .xiTwo)
    (hu : HasUnpairedChild T none) : A.row.xi = 0 := by
  rcases hrow hu with hxiOne | hxiTwo
  · rw [hxiOne]
    rfl
  · rw [hxiTwo]
    rfl

/-- If the allocation came from complete root coverage, the flattened forest
has the named strong two-separation residue. -/
theorem assembledRootColoring_strongTwoSeparatedWith
    (hK : InTargetClassK T) (A : RootAllocation T hK)
    (hrow : HasUnpairedChild T none →
      A.row = .xiOne ∨ A.row = .xiTwo) :
    StrongTwoSeparatedWith (assembledRootColoring hK A) A.row.xi := by
  constructor
  · intro u
    by_cases hu : u ∈ rootUnpairedHelixSubtreeUnion T
    · obtain ⟨i, hi⟩ :=
        (mem_rootUnpairedHelixSubtreeUnion_iff u).1 hu
      exact (assembledRootSubtreePostcondition hK A i).unpairedAt u hi
    · have huRoot : u ∈ unpairedChildren T none :=
        (mem_root_unpairedChildren_iff_not_mem_rootSubtree u).2 hu
      have hlevel :=
        unpairedLevel_of_mem_rootChildren (assembledRootColoring hK A) huRoot
      have hxi : A.row.xi = 0 :=
        A.xi_eq_zero_of_hasUnpairedChild hrow ⟨u, huRoot⟩
      rw [hlevel, hxi]
      rfl
  · intro g hgrey
    have hgAll : g ∈ rootPairedHelixSubtreeUnion T := by
      rw [rootPairedHelixSubtreeUnion_eq_univ]
      exact Finset.mem_univ g
    obtain ⟨i, hi⟩ :=
      (mem_rootPairedHelixSubtreeUnion_iff g).1 hgAll
    simpa [RootRow.eta] using
      (assembledRootSubtreePostcondition hK A i).greysAt g hi hgrey

/-- Root-forest assembly theorem, retaining the witness residue selected by
the actual root allocation. -/
theorem rootForestAssembly
    (hK : InTargetClassK T) (A : RootAllocation T hK)
    (hrow : HasUnpairedChild T none →
      A.row = .xiOne ∨ A.row = .xiTwo) :
    ProperColoring (assembledRootColoring hK A) ∧
      StrongTwoSeparatedWith (assembledRootColoring hK A) A.row.xi :=
  ⟨assembledRootColoring_proper hK A,
    assembledRootColoring_strongTwoSeparatedWith hK A hrow⟩

/-! ## Canonical certificate and Theorem 12 -/

/-- One total global coloring, together with the actual root allocation and
all correctness evidence.  The allocation is retained for later milestones. -/
structure GlobalColoringCertificate
    (T : SecondaryStructure n) (hK : InTargetClassK T) where
  allocation : RootAllocation T hK
  unpairedRow : HasUnpairedChild T none →
    allocation.row = .xiOne ∨ allocation.row = .xiTwo
  smallRow : ¬ HasUnpairedChild T none ∧ pairedChildCount T none ≤ 2 →
    allocation.row = .xiOne ∨ allocation.row = .xiTwo
  largeRow : ¬ HasUnpairedChild T none ∧ 3 ≤ pairedChildCount T none →
    allocation.row = .etaThree ∨ allocation.row = .etaFour
  coloring : Coloring T
  coloring_eq : coloring = assembledRootColoring hK allocation
  proper : ProperColoring coloring
  strong : StrongTwoSeparatedWith coloring allocation.row.xi

/-- Canonical proof-bearing global coloring selected from complete root
allocation coverage. -/
noncomputable def globalColoringCertificate
    (hK : InTargetClassK T) : GlobalColoringCertificate T hK := by
  let hcoverage := completeRootAllocationCoverage hK
  let A := Classical.choose hcoverage
  have hspec := Classical.choose_spec hcoverage
  refine {
    allocation := A
    unpairedRow := hspec.1
    smallRow := hspec.2.1
    largeRow := hspec.2.2
    coloring := assembledRootColoring hK A
    coloring_eq := rfl
    proper := assembledRootColoring_proper hK A
    strong := assembledRootColoring_strongTwoSeparatedWith hK A hspec.1 }

/-- Witness-bearing form of the global coloring theorem. -/
theorem exists_proper_strongTwoSeparatedWith
    (hK : InTargetClassK T) :
    ∃ xi, ∃ χ : Coloring T,
      ProperColoring χ ∧ StrongTwoSeparatedWith χ xi := by
  let C := globalColoringCertificate hK
  exact ⟨C.allocation.row.xi, C.coloring, C.proper, C.strong⟩

/-- Every class-K target has a proper strongly two-separated coloring. -/
theorem exists_proper_strongTwoSeparated
    (hK : InTargetClassK T) :
    ∃ χ : Coloring T, ProperColoring χ ∧ StrongTwoSeparated χ := by
  obtain ⟨xi, chi, hproper, hstrong⟩ :=
    exists_proper_strongTwoSeparatedWith hK
  exact ⟨chi, hproper,
    (strongTwoSeparated_iff_exists_with chi).2 ⟨xi, hstrong⟩⟩

/-- **Theorem 12 of `docs/CANONICAL_PROOF.md`.** Every target in class K
admits a proper strong-2-separated coloring. -/
theorem targetClass_admits_proper_strongTwoSeparated
    (hK : InTargetClassK T) :
    ∃ χ : Coloring T, ProperColoring χ ∧ StrongTwoSeparated χ :=
  exists_proper_strongTwoSeparated hK

end RNA
