module

public import RNA.Examples
public import RNA.AtMostTwoShort.ShortCount
public import RNA.AtMostTwoShort.SubtreeConstruction
public import RNA.AtMostTwoShort.ResourceRoot
public import RNA.AtMostTwoShort.Designability

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

/-!
# Model-fidelity targets for the at-most-two theorem

The target data and class/count controls in this file are concrete and
kernel-reduced.  Construction-facing coloring and designability checks are
added below once the generic resource theorem is imported.
-/

namespace RNA

open RNA.Examples

/-! ## All-unpaired target -/

def allUnpairedTarget : SecondaryStructure 4 :=
  SecondaryStructure.empty 4

def allASequence : Sequence 4 := fun _ => Nucleotide.A

theorem allUnpairedTarget_inTargetClassKLeTwo :
    InTargetClassKLeTwo allUnpairedTarget := by
  decide

theorem allUnpairedTarget_shortHelixCount :
    shortHelixCount allUnpairedTarget = 0 := by
  decide

theorem allUnpairedTarget_rootDegree :
    pairedChildCount allUnpairedTarget none = 0 := by
  decide

noncomputable def allUnpairedTargetRootDegreeZeroColoring :
    Coloring allUnpairedTarget :=
  rootDegreeZeroColoring allUnpairedTarget_rootDegree

theorem allUnpairedTargetRootDegreeZeroColoring_proper :
    ProperColoring allUnpairedTargetRootDegreeZeroColoring := by
  simpa [allUnpairedTargetRootDegreeZeroColoring] using
    rootDegreeZeroColoring_proper allUnpairedTarget_rootDegree

theorem allUnpairedTargetRootDegreeZeroColoring_strong :
    StrongTwoSeparatedWith allUnpairedTargetRootDegreeZeroColoring 0 := by
  simpa [allUnpairedTargetRootDegreeZeroColoring] using
    rootDegreeZeroColoring_strongTwoSeparatedWith
      allUnpairedTarget_rootDegree

/-- The all-A complete sequence permits no arc at all, so the empty fold is
uniquely optimal.  This is an explicit model-level check independent of the
later generic corollary. -/
theorem allASequence_unique_empty_fold :
    UniqueDesigns allASequence allUnpairedTarget := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp [allUnpairedTarget, SecondaryStructure.empty] at ha
  · intro S hcompatible hne
    have harcs : S.arcs = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro a ha
      have hbad := hcompatible a ha
      simp [allASequence, Compatible] at hbad
    have hEq : S = allUnpairedTarget := by
      apply SecondaryStructure.ext
      simpa [allUnpairedTarget, SecondaryStructure.empty] using harcs
    exact (hne hEq).elim

/-! ## One and two short helices -/

theorem nestedTarget_inTargetClassKLeTwo :
    InTargetClassKLeTwo nestedTarget :=
  inTargetClassKLeTwo_of_inTargetClassK nestedTarget_in_classK

theorem nestedTarget_shortHelixCount : shortHelixCount nestedTarget = 1 :=
  shortHelixCount_eq_one_of_inTargetClassK nestedTarget_in_classK

noncomputable def nestedTargetResourceCertificate :
    GlobalColoringCertificateLeTwo nestedTarget
      nestedTarget_inTargetClassKLeTwo :=
  globalColoringCertificateLeTwo nestedTarget_inTargetClassKLeTwo

theorem nestedTarget_newConstruction_proper :
    ProperColoring nestedTargetResourceCertificate.coloring :=
  nestedTargetResourceCertificate.proper

theorem nestedTarget_newConstruction_strongTwoSeparated :
    StrongTwoSeparated nestedTargetResourceCertificate.coloring :=
  (strongTwoSeparated_iff_exists_with
    nestedTargetResourceCertificate.coloring).2
      ⟨nestedTargetResourceCertificate.xi,
        nestedTargetResourceCertificate.strong⟩

theorem nestedTarget_newConstruction_uniqueDesigns :
    UniqueDesigns
      (sequenceOfProperColoring nestedTargetResourceCertificate.coloring
        nestedTargetResourceCertificate.proper) nestedTarget := by
  simpa [nestedTargetResourceCertificate] using
    atMostTwoShortHelices_uniqueDesigns
      nestedTarget_inTargetClassKLeTwo

/-- Dot-bracket `(())(())`: two length-two root children. -/
def twoShortRootTarget : SecondaryStructure 8 where
  arcs := {
    ⟨0, 3, by decide⟩, ⟨1, 2, by decide⟩,
    ⟨4, 7, by decide⟩, ⟨5, 6, by decide⟩ }
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem twoShortRootTarget_shortHelixCount :
    shortHelixCount twoShortRootTarget = 2 := by
  decide

theorem twoShortRootTarget_inTargetClassK2 :
    InTargetClassK2 twoShortRootTarget := by
  decide

noncomputable def twoShortRootTargetResourceCertificate :
    GlobalColoringCertificateLeTwo twoShortRootTarget
      twoShortRootTarget_inTargetClassK2.1 :=
  globalColoringCertificateLeTwo twoShortRootTarget_inTargetClassK2.1

theorem twoShortRootTarget_newConstruction_proper :
    ProperColoring twoShortRootTargetResourceCertificate.coloring :=
  twoShortRootTargetResourceCertificate.proper

theorem twoShortRootTarget_newConstruction_strongTwoSeparated :
    StrongTwoSeparated twoShortRootTargetResourceCertificate.coloring :=
  (strongTwoSeparated_iff_exists_with
    twoShortRootTargetResourceCertificate.coloring).2
      ⟨twoShortRootTargetResourceCertificate.xi,
        twoShortRootTargetResourceCertificate.strong⟩

theorem twoShortRootTarget_newConstruction_uniqueDesigns :
    UniqueDesigns
      (sequenceOfProperColoring
        twoShortRootTargetResourceCertificate.coloring
        twoShortRootTargetResourceCertificate.proper)
      twoShortRootTarget := by
  simpa [twoShortRootTargetResourceCertificate] using
    exactTwoShortHelices_uniqueDesigns twoShortRootTarget_inTargetClassK2

/-! ## Degree-three root with two resource-positive children -/

/-- Dot-bracket `(())(())((()))`: two short root children and one long root
child. -/
def degreeThreeTwoShortTarget : SecondaryStructure 14 where
  arcs := {
    ⟨0, 3, by decide⟩, ⟨1, 2, by decide⟩,
    ⟨4, 7, by decide⟩, ⟨5, 6, by decide⟩,
    ⟨8, 13, by decide⟩, ⟨9, 12, by decide⟩,
    ⟨10, 11, by decide⟩ }
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem degreeThreeTwoShortTarget_inTargetClassK2 :
    InTargetClassK2 degreeThreeTwoShortTarget := by
  decide

theorem degreeThreeTwoShortTarget_shortHelixCount :
    shortHelixCount degreeThreeTwoShortTarget = 2 := by
  decide

theorem degreeThreeTwoShortTarget_rootDegree :
    pairedChildCount degreeThreeTwoShortTarget none = 3 := by
  decide

/-- The first explicit length-two root helix. -/
def degreeThreeFirstShortHelix :
    MaximalHelix degreeThreeTwoShortTarget :=
  ⟨(⟨0, 3, by decide⟩, ⟨2, by decide⟩), by decide⟩

/-- The second explicit length-two root helix. -/
def degreeThreeSecondShortHelix :
    MaximalHelix degreeThreeTwoShortTarget :=
  ⟨(⟨4, 7, by decide⟩, ⟨2, by decide⟩), by decide⟩

/-- The short-free length-three root helix. -/
def degreeThreeLongHelix : MaximalHelix degreeThreeTwoShortTarget :=
  ⟨(⟨8, 13, by decide⟩, ⟨3, by decide⟩), by decide⟩

@[simp] theorem degreeThreeFirstShortHelix_length :
    degreeThreeFirstShortHelix.length = 2 := rfl

@[simp] theorem degreeThreeSecondShortHelix_length :
    degreeThreeSecondShortHelix.length = 2 := rfl

@[simp] theorem degreeThreeLongHelix_length :
    degreeThreeLongHelix.length = 3 := rfl

theorem degreeThreeFirstShortHead_is_rootChild :
    degreeThreeFirstShortHelix.headNode ∈
      pairedChildren degreeThreeTwoShortTarget none := by
  decide

theorem degreeThreeSecondShortHead_is_rootChild :
    degreeThreeSecondShortHelix.headNode ∈
      pairedChildren degreeThreeTwoShortTarget none := by
  decide

theorem degreeThreeLongHead_is_rootChild :
    degreeThreeLongHelix.headNode ∈
      pairedChildren degreeThreeTwoShortTarget none := by
  decide

noncomputable def degreeThreeRootSlotZero :
    Fin (pairedChildCount degreeThreeTwoShortTarget none) :=
  pairedChildIndex degreeThreeTwoShortTarget none
    degreeThreeFirstShortHelix.headNode
    degreeThreeFirstShortHead_is_rootChild

noncomputable def degreeThreeRootSlotOne :
    Fin (pairedChildCount degreeThreeTwoShortTarget none) :=
  pairedChildIndex degreeThreeTwoShortTarget none
    degreeThreeSecondShortHelix.headNode
    degreeThreeSecondShortHead_is_rootChild

noncomputable def degreeThreeRootSlotTwo :
    Fin (pairedChildCount degreeThreeTwoShortTarget none) :=
  pairedChildIndex degreeThreeTwoShortTarget none
    degreeThreeLongHelix.headNode degreeThreeLongHead_is_rootChild

theorem degreeThree_rootSlotZero_outgoing :
    outgoingHelixAtRootSlot degreeThreeTwoShortTarget
      degreeThreeRootSlotZero = degreeThreeFirstShortHelix := by
  apply MaximalHelix.ext_outer
  have hout := outgoingHelixAtRootSlot_head degreeThreeTwoShortTarget
    degreeThreeRootSlotZero
  have hexplicit : degreeThreeFirstShortHelix.headNode =
      orderedPairedChild degreeThreeTwoShortTarget none
        degreeThreeRootSlotZero := by
    exact (orderedPairedChild_pairedChildIndex degreeThreeTwoShortTarget none
      degreeThreeFirstShortHelix.headNode
      degreeThreeFirstShortHead_is_rootChild).symm
  exact congrArg Subtype.val (hout.trans hexplicit.symm)

theorem degreeThree_rootSlotOne_outgoing :
    outgoingHelixAtRootSlot degreeThreeTwoShortTarget
      degreeThreeRootSlotOne = degreeThreeSecondShortHelix := by
  apply MaximalHelix.ext_outer
  have hout := outgoingHelixAtRootSlot_head degreeThreeTwoShortTarget
    degreeThreeRootSlotOne
  have hexplicit : degreeThreeSecondShortHelix.headNode =
      orderedPairedChild degreeThreeTwoShortTarget none
        degreeThreeRootSlotOne := by
    exact (orderedPairedChild_pairedChildIndex degreeThreeTwoShortTarget none
      degreeThreeSecondShortHelix.headNode
      degreeThreeSecondShortHead_is_rootChild).symm
  exact congrArg Subtype.val (hout.trans hexplicit.symm)

theorem degreeThree_rootSlotTwo_outgoing :
    outgoingHelixAtRootSlot degreeThreeTwoShortTarget
      degreeThreeRootSlotTwo = degreeThreeLongHelix := by
  apply MaximalHelix.ext_outer
  have hout := outgoingHelixAtRootSlot_head degreeThreeTwoShortTarget
    degreeThreeRootSlotTwo
  have hexplicit : degreeThreeLongHelix.headNode =
      orderedPairedChild degreeThreeTwoShortTarget none
        degreeThreeRootSlotTwo := by
    exact (orderedPairedChild_pairedChildIndex degreeThreeTwoShortTarget none
      degreeThreeLongHelix.headNode degreeThreeLongHead_is_rootChild).symm
  exact congrArg Subtype.val (hout.trans hexplicit.symm)

theorem degreeThree_rootSlotZero_positive :
    0 < shortHelixSubtreeCount degreeThreeTwoShortTarget
      (outgoingHelixAtRootSlot degreeThreeTwoShortTarget
        degreeThreeRootSlotZero) := by
  rw [degreeThree_rootSlotZero_outgoing]
  exact shortHelixSubtreeCount_pos_of_length_two
    degreeThreeFirstShortHelix rfl

theorem degreeThree_rootSlotOne_positive :
    0 < shortHelixSubtreeCount degreeThreeTwoShortTarget
      (outgoingHelixAtRootSlot degreeThreeTwoShortTarget
        degreeThreeRootSlotOne) := by
  rw [degreeThree_rootSlotOne_outgoing]
  exact shortHelixSubtreeCount_pos_of_length_two
    degreeThreeSecondShortHelix rfl

theorem degreeThree_rootSlotTwo_shortFree :
    shortHelixSubtreeCount degreeThreeTwoShortTarget
      (outgoingHelixAtRootSlot degreeThreeTwoShortTarget
        degreeThreeRootSlotTwo) = 0 := by
  rw [degreeThree_rootSlotTwo_outgoing]
  decide

/-- The root support is exactly two: the first two actual slots carry the two
short helices and the third slot is short-free. -/
theorem degreeThreeTwoShortTarget_rootShortSupport_card :
    (rootShortSupport degreeThreeTwoShortTarget).card = 2 := by
  have hzero : degreeThreeRootSlotZero ∈
      rootShortSupport degreeThreeTwoShortTarget :=
    (mem_rootShortSupport_iff degreeThreeTwoShortTarget
      degreeThreeRootSlotZero).2 degreeThree_rootSlotZero_positive
  have hone : degreeThreeRootSlotOne ∈
      rootShortSupport degreeThreeTwoShortTarget :=
    (mem_rootShortSupport_iff degreeThreeTwoShortTarget
      degreeThreeRootSlotOne).2 degreeThree_rootSlotOne_positive
  have hne : degreeThreeRootSlotZero ≠ degreeThreeRootSlotOne := by
    intro h
    have hheads := congrArg
      (orderedPairedChild degreeThreeTwoShortTarget none) h
    rw [show orderedPairedChild degreeThreeTwoShortTarget none
          degreeThreeRootSlotZero = degreeThreeFirstShortHelix.headNode by
        exact orderedPairedChild_pairedChildIndex degreeThreeTwoShortTarget
          none degreeThreeFirstShortHelix.headNode
            degreeThreeFirstShortHead_is_rootChild,
      show orderedPairedChild degreeThreeTwoShortTarget none
          degreeThreeRootSlotOne = degreeThreeSecondShortHelix.headNode by
        exact orderedPairedChild_pairedChildIndex degreeThreeTwoShortTarget
          none degreeThreeSecondShortHelix.headNode
            degreeThreeSecondShortHead_is_rootChild] at hheads
    have hheadNe : degreeThreeFirstShortHelix.headNode ≠
        degreeThreeSecondShortHelix.headNode := by decide
    exact hheadNe hheads
  have hsubset : ({degreeThreeRootSlotZero, degreeThreeRootSlotOne} :
      Finset (Fin (pairedChildCount degreeThreeTwoShortTarget none))) ⊆
      rootShortSupport degreeThreeTwoShortTarget := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hzero
    · exact hone
  have hlower : 2 ≤ (rootShortSupport degreeThreeTwoShortTarget).card := by
    have := Finset.card_le_card hsubset
    simpa [hne] using this
  have hupper := rootShortSupport_card_le_two
    degreeThreeTwoShortTarget_inTargetClassK2.1
  omega

/-- The concrete degree-three adaptive root allocation. -/
noncomputable def degreeThreeTwoShortRootAllocation :
    ResourceRootAllocation degreeThreeTwoShortTarget
      degreeThreeTwoShortTarget_inTargetClassK2.1 :=
  completeResourceRootAllocation degreeThreeTwoShortTarget_inTargetClassK2.1
    (by rw [degreeThreeTwoShortTarget_rootDegree]; omega)

theorem degreeThreeTwoShortRoot_entry_eq_eta :
    degreeThreeTwoShortRootAllocation.entry =
      degreeThreeTwoShortRootAllocation.eta :=
  degreeThreeTwoShortRootAllocation.entry_eq_eta_of_large
    (by rw [degreeThreeTwoShortTarget_rootDegree])

theorem degreeThreeTwoShortRoot_first_receives_grey :
    degreeThreeTwoShortRootAllocation.ports degreeThreeRootSlotZero =
      Color.grey := by
  apply degreeThreeTwoShortRootAllocation.positiveGreyAtEta
    degreeThreeTwoShortRoot_entry_eq_eta degreeThreeRootSlotZero
  exact (mem_rootShortSupport_iff degreeThreeTwoShortTarget
    degreeThreeRootSlotZero).2 degreeThree_rootSlotZero_positive

theorem degreeThreeTwoShortRoot_second_receives_grey :
    degreeThreeTwoShortRootAllocation.ports degreeThreeRootSlotOne =
      Color.grey := by
  apply degreeThreeTwoShortRootAllocation.positiveGreyAtEta
    degreeThreeTwoShortRoot_entry_eq_eta degreeThreeRootSlotOne
  exact (mem_rootShortSupport_iff degreeThreeTwoShortTarget
    degreeThreeRootSlotOne).2 degreeThree_rootSlotOne_positive

/-- The actual remaining degree-three slot gets black, so the installed row
is the requested `G,G,B` row on the target's actual ordered children. -/
theorem degreeThreeTwoShortRoot_third_receives_black :
    degreeThreeTwoShortRootAllocation.ports degreeThreeRootSlotTwo =
      Color.black := by
  apply degreeThreeTwoShortRootAllocation.twoSupportThirdBlack
    degreeThreeTwoShortTarget_rootShortSupport_card
      degreeThreeTwoShortTarget_rootDegree degreeThreeRootSlotTwo
  exact (not_mem_rootShortSupport_iff_count_eq_zero
    degreeThreeTwoShortTarget degreeThreeRootSlotTwo).2
      degreeThree_rootSlotTwo_shortFree

theorem degreeThreeTwoShortRoot_exposure_proper :
    ProperExposure
      (rootPortExposure degreeThreeTwoShortRootAllocation.ports) :=
  degreeThreeTwoShortRootAllocation.proper

noncomputable def degreeThreeTwoShortGlobalCertificate :
    GlobalColoringCertificateLeTwo degreeThreeTwoShortTarget
      degreeThreeTwoShortTarget_inTargetClassK2.1 :=
  globalColoringCertificateLeTwo degreeThreeTwoShortTarget_inTargetClassK2.1

theorem degreeThreeTwoShortGlobal_proper :
    ProperColoring degreeThreeTwoShortGlobalCertificate.coloring :=
  degreeThreeTwoShortGlobalCertificate.proper

theorem degreeThreeTwoShortGlobal_strongTwoSeparated :
    StrongTwoSeparated degreeThreeTwoShortGlobalCertificate.coloring :=
  (strongTwoSeparated_iff_exists_with
    degreeThreeTwoShortGlobalCertificate.coloring).2
      ⟨degreeThreeTwoShortGlobalCertificate.xi,
        degreeThreeTwoShortGlobalCertificate.strong⟩

theorem degreeThreeTwoShortGlobal_uniqueDesigns :
    UniqueDesigns
      (sequenceOfProperColoring
        degreeThreeTwoShortGlobalCertificate.coloring
        degreeThreeTwoShortGlobalCertificate.proper)
      degreeThreeTwoShortTarget := by
  simpa [degreeThreeTwoShortGlobalCertificate] using
    exactTwoShortHelices_uniqueDesigns
      degreeThreeTwoShortTarget_inTargetClassK2

/-! ## Internal two-demand M loop -/

/-- Track-B Type-I witness `(((((((())(()))))((())))))`.  No minimality claim
is attached to this example. -/
def internalTwoDemandTarget : SecondaryStructure 26 where
  arcs := {
    ⟨0, 25, by decide⟩, ⟨1, 24, by decide⟩,
    ⟨2, 23, by decide⟩,
    ⟨3, 16, by decide⟩, ⟨4, 15, by decide⟩,
    ⟨5, 14, by decide⟩,
    ⟨6, 9, by decide⟩, ⟨7, 8, by decide⟩,
    ⟨10, 13, by decide⟩, ⟨11, 12, by decide⟩,
    ⟨17, 22, by decide⟩, ⟨18, 21, by decide⟩,
    ⟨19, 20, by decide⟩ }
  isPartialMatching := by decide
  isNoncrossing := by decide

set_option maxHeartbeats 800000 in
-- Kernel reduction of the explicit 26-position target needs extra heartbeats.
theorem internalTwoDemandTarget_inTargetClassK2 :
    InTargetClassK2 internalTwoDemandTarget := by
  decide

set_option maxHeartbeats 800000 in
-- Computing all maximal helices of the explicit witness is intentionally finite.
theorem internalTwoDemandTarget_shortHelixCount :
    shortHelixCount internalTwoDemandTarget = 2 := by
  decide

/-- The length-three helix whose terminal pair is the critical internal M
loop. -/
def internalTwoDemandIncomingHelix :
    MaximalHelix internalTwoDemandTarget :=
  ⟨(⟨3, 16, by decide⟩, ⟨3, by decide⟩), by decide⟩

/-- The left length-two child at the critical internal M loop. -/
def internalTwoDemandLeftShortHelix :
    MaximalHelix internalTwoDemandTarget :=
  ⟨(⟨6, 9, by decide⟩, ⟨2, by decide⟩), by decide⟩

/-- The right length-two child at the critical internal M loop. -/
def internalTwoDemandRightShortHelix :
    MaximalHelix internalTwoDemandTarget :=
  ⟨(⟨10, 13, by decide⟩, ⟨2, by decide⟩), by decide⟩

@[simp] theorem internalTwoDemandIncomingHelix_length :
    internalTwoDemandIncomingHelix.length = 3 := rfl

@[simp] theorem internalTwoDemandLeftShortHelix_length :
    internalTwoDemandLeftShortHelix.length = 2 := rfl

@[simp] theorem internalTwoDemandRightShortHelix_length :
    internalTwoDemandRightShortHelix.length = 2 := rfl

def internalTwoDemandMNode : PairedNode internalTwoDemandTarget :=
  ⟨⟨5, 14, by decide⟩, by decide⟩

theorem internalTwoDemandIncomingHelix_terminal :
    internalTwoDemandIncomingHelix.terminalNode =
      internalTwoDemandMNode := by
  apply Subtype.ext
  apply Arc.stackOffset_arc_unique
    internalTwoDemandIncomingHelix.terminalPair_stackOffset
  decide

theorem internalTwoDemandMNode_is_M :
    IsMEndpoint internalTwoDemandMNode := by
  decide

theorem internalTwoDemandIncoming_terminal_is_M :
    IsMEndpoint internalTwoDemandIncomingHelix.terminalNode := by
  rw [internalTwoDemandIncomingHelix_terminal]
  exact internalTwoDemandMNode_is_M

theorem internalTwoDemand_pairedChildCount :
    pairedChildCount internalTwoDemandTarget
      (some internalTwoDemandIncomingHelix.terminalNode) = 2 := by
  rw [internalTwoDemandIncomingHelix_terminal]
  decide

theorem internalTwoDemandLeftShortHead_is_child :
    internalTwoDemandLeftShortHelix.headNode ∈
      pairedChildren internalTwoDemandTarget
        (some internalTwoDemandIncomingHelix.terminalNode) := by
  rw [internalTwoDemandIncomingHelix_terminal]
  decide

theorem internalTwoDemandRightShortHead_is_child :
    internalTwoDemandRightShortHelix.headNode ∈
      pairedChildren internalTwoDemandTarget
        (some internalTwoDemandIncomingHelix.terminalNode) := by
  rw [internalTwoDemandIncomingHelix_terminal]
  decide

noncomputable def internalTwoDemandLeftSlot :
    Fin (pairedChildCount internalTwoDemandTarget
      (some internalTwoDemandIncomingHelix.terminalNode)) :=
  pairedChildIndex internalTwoDemandTarget
    (some internalTwoDemandIncomingHelix.terminalNode)
      internalTwoDemandLeftShortHelix.headNode
        internalTwoDemandLeftShortHead_is_child

noncomputable def internalTwoDemandRightSlot :
    Fin (pairedChildCount internalTwoDemandTarget
      (some internalTwoDemandIncomingHelix.terminalNode)) :=
  pairedChildIndex internalTwoDemandTarget
    (some internalTwoDemandIncomingHelix.terminalNode)
      internalTwoDemandRightShortHelix.headNode
        internalTwoDemandRightShortHead_is_child

theorem internalTwoDemand_leftSlot_outgoing :
    outgoingHelix internalTwoDemandTarget internalTwoDemandIncomingHelix
      internalTwoDemandLeftSlot = internalTwoDemandLeftShortHelix := by
  apply MaximalHelix.ext_outer
  have hout := outgoingHelix_headNode internalTwoDemandTarget
    internalTwoDemandIncomingHelix internalTwoDemandLeftSlot
  have hexplicit : internalTwoDemandLeftShortHelix.headNode =
      orderedPairedChild internalTwoDemandTarget
        (some internalTwoDemandIncomingHelix.terminalNode)
          internalTwoDemandLeftSlot := by
    exact (orderedPairedChild_pairedChildIndex internalTwoDemandTarget
      (some internalTwoDemandIncomingHelix.terminalNode)
        internalTwoDemandLeftShortHelix.headNode
          internalTwoDemandLeftShortHead_is_child).symm
  exact congrArg Subtype.val (hout.trans hexplicit.symm)

theorem internalTwoDemand_rightSlot_outgoing :
    outgoingHelix internalTwoDemandTarget internalTwoDemandIncomingHelix
      internalTwoDemandRightSlot = internalTwoDemandRightShortHelix := by
  apply MaximalHelix.ext_outer
  have hout := outgoingHelix_headNode internalTwoDemandTarget
    internalTwoDemandIncomingHelix internalTwoDemandRightSlot
  have hexplicit : internalTwoDemandRightShortHelix.headNode =
      orderedPairedChild internalTwoDemandTarget
        (some internalTwoDemandIncomingHelix.terminalNode)
          internalTwoDemandRightSlot := by
    exact (orderedPairedChild_pairedChildIndex internalTwoDemandTarget
      (some internalTwoDemandIncomingHelix.terminalNode)
        internalTwoDemandRightShortHelix.headNode
          internalTwoDemandRightShortHead_is_child).symm
  exact congrArg Subtype.val (hout.trans hexplicit.symm)

theorem internalTwoDemand_leftSlot_positive :
    0 < shortHelixSubtreeCount internalTwoDemandTarget
      (outgoingHelix internalTwoDemandTarget internalTwoDemandIncomingHelix
        internalTwoDemandLeftSlot) := by
  rw [internalTwoDemand_leftSlot_outgoing]
  exact shortHelixSubtreeCount_pos_of_length_two
    internalTwoDemandLeftShortHelix rfl

theorem internalTwoDemand_rightSlot_positive :
    0 < shortHelixSubtreeCount internalTwoDemandTarget
      (outgoingHelix internalTwoDemandTarget internalTwoDemandIncomingHelix
        internalTwoDemandRightSlot) := by
  rw [internalTwoDemand_rightSlot_outgoing]
  exact shortHelixSubtreeCount_pos_of_length_two
    internalTwoDemandRightShortHelix rfl

/-- The critical M loop has exactly two actual resource-positive child
subtrees. -/
theorem internalTwoDemand_loopShortSupport_card :
    (loopShortSupport internalTwoDemandTarget
      internalTwoDemandIncomingHelix).card = 2 := by
  have hleft : internalTwoDemandLeftSlot ∈
      loopShortSupport internalTwoDemandTarget
        internalTwoDemandIncomingHelix :=
    (mem_loopShortSupport_iff internalTwoDemandIncomingHelix
      internalTwoDemandLeftSlot).2 internalTwoDemand_leftSlot_positive
  have hright : internalTwoDemandRightSlot ∈
      loopShortSupport internalTwoDemandTarget
        internalTwoDemandIncomingHelix :=
    (mem_loopShortSupport_iff internalTwoDemandIncomingHelix
      internalTwoDemandRightSlot).2 internalTwoDemand_rightSlot_positive
  have hne : internalTwoDemandLeftSlot ≠ internalTwoDemandRightSlot := by
    intro h
    have hheads := congrArg
      (orderedPairedChild internalTwoDemandTarget
        (some internalTwoDemandIncomingHelix.terminalNode)) h
    rw [show orderedPairedChild internalTwoDemandTarget
          (some internalTwoDemandIncomingHelix.terminalNode)
            internalTwoDemandLeftSlot =
              internalTwoDemandLeftShortHelix.headNode by
        exact orderedPairedChild_pairedChildIndex internalTwoDemandTarget
          (some internalTwoDemandIncomingHelix.terminalNode)
            internalTwoDemandLeftShortHelix.headNode
              internalTwoDemandLeftShortHead_is_child,
      show orderedPairedChild internalTwoDemandTarget
          (some internalTwoDemandIncomingHelix.terminalNode)
            internalTwoDemandRightSlot =
              internalTwoDemandRightShortHelix.headNode by
        exact orderedPairedChild_pairedChildIndex internalTwoDemandTarget
          (some internalTwoDemandIncomingHelix.terminalNode)
            internalTwoDemandRightShortHelix.headNode
              internalTwoDemandRightShortHead_is_child] at hheads
    have hheadNe : internalTwoDemandLeftShortHelix.headNode ≠
        internalTwoDemandRightShortHelix.headNode := by decide
    exact hheadNe hheads
  have hsubset : ({internalTwoDemandLeftSlot, internalTwoDemandRightSlot} :
      Finset (Fin (pairedChildCount internalTwoDemandTarget
        (some internalTwoDemandIncomingHelix.terminalNode)))) ⊆
      loopShortSupport internalTwoDemandTarget
        internalTwoDemandIncomingHelix := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hleft
    · exact hright
  have hlower : 2 ≤ (loopShortSupport internalTwoDemandTarget
      internalTwoDemandIncomingHelix).card := by
    have := Finset.card_le_card hsubset
    simpa [hne] using this
  have hupper := loopShortSupport_card_le_two
    internalTwoDemandTarget_inTargetClassK2.1
      internalTwoDemandIncomingHelix
  omega

/-- The support equation itself forces the critical incoming helix to be
long; the explicit witness has exact length three. -/
theorem internalTwoDemand_incoming_length_at_least_three :
    3 ≤ internalTwoDemandIncomingHelix.length :=
  loopShortSupport_card_eq_two_length_at_least_three
    internalTwoDemandTarget_inTargetClassK2.1
      internalTwoDemandIncomingHelix
        internalTwoDemand_loopShortSupport_card

set_option maxHeartbeats 800000 in
-- Reducing the explicit 26-position subtree support needs extra heartbeats.
theorem internalTwoDemand_incoming_requiredInterface :
    RequiredInterface internalTwoDemandTarget
      internalTwoDemandIncomingHelix 0 0 Color.black := by
  have hcountPos : 0 < shortHelixSubtreeCount internalTwoDemandTarget
      internalTwoDemandIncomingHelix := by
    have hle := loopShortSupport_card_le_shortHelixSubtreeCount
      internalTwoDemandIncomingHelix
    rw [internalTwoDemand_loopShortSupport_card] at hle
    omega
  exact (requiredInterface_of_count_pos internalTwoDemandIncomingHelix
    0 0 Color.black hcountPos).2 (inQ_xi_black 0)

set_option maxHeartbeats 800000 in
-- Elaborating the dependent Q-interface transfer for that witness is finite
-- but large.
/-- The transfer dispatcher at the critical loop is instantiated at a valid
Q interface.  Its retained two-demand fact is the machine-checked
non-grey close required by the adaptive M row. -/
noncomputable def internalTwoDemandTransferChoice :
    ResourceTransferChoice internalTwoDemandTarget_inTargetClassK2.1
      internalTwoDemandIncomingHelix 0 0 Color.black .M
        internalTwoDemand_incoming_requiredInterface :=
  chooseResourceTransfer internalTwoDemandTarget_inTargetClassK2.1
    internalTwoDemandIncomingHelix 0 0 Color.black .M
      internalTwoDemand_incoming_requiredInterface

theorem internalTwoDemandTransfer_closesNonGrey :
    (internalTwoDemandTransferChoice.transfer.closingColor
      internalTwoDemandIncomingHelix.positive).NonGrey :=
  internalTwoDemandTransferChoice.twoDemandClosingNonGrey rfl
    internalTwoDemand_loopShortSupport_card

/-- The actual two-demand loop allocation selected from that transfer. -/
noncomputable def internalTwoDemandResourceAllocation :
    ResourceLoopAllocation internalTwoDemandTarget
      internalTwoDemandTarget_inTargetClassK2.1
        internalTwoDemandIncomingHelix .M
          (internalTwoDemandTransferChoice.transfer.closingColor
            internalTwoDemandIncomingHelix.positive) 0 :=
  completeResourceLoopAllocation
    internalTwoDemandTarget_inTargetClassK2.1
      internalTwoDemandIncomingHelix .M
        internalTwoDemandIncoming_terminal_is_M
          (internalTwoDemandTransferChoice.transfer.closingColor
            internalTwoDemandIncomingHelix.positive) 0
              internalTwoDemandTransferChoice.lClosingNonGrey
                internalTwoDemandTransferChoice.twoDemandClosingNonGrey

theorem internalTwoDemand_left_child_receives_grey :
    internalTwoDemandResourceAllocation.ports
      internalTwoDemandLeftSlot = Color.grey :=
  internalTwoDemandResourceAllocation.positiveGreyAtM rfl
    internalTwoDemandLeftSlot
      ((mem_loopShortSupport_iff internalTwoDemandIncomingHelix
        internalTwoDemandLeftSlot).2 internalTwoDemand_leftSlot_positive)

theorem internalTwoDemand_right_child_receives_grey :
    internalTwoDemandResourceAllocation.ports
      internalTwoDemandRightSlot = Color.grey :=
  internalTwoDemandResourceAllocation.positiveGreyAtM rfl
    internalTwoDemandRightSlot
      ((mem_loopShortSupport_iff internalTwoDemandIncomingHelix
        internalTwoDemandRightSlot).2 internalTwoDemand_rightSlot_positive)

noncomputable def internalTwoDemandGlobalCertificate :
    GlobalColoringCertificateLeTwo internalTwoDemandTarget
      internalTwoDemandTarget_inTargetClassK2.1 :=
  globalColoringCertificateLeTwo internalTwoDemandTarget_inTargetClassK2.1

theorem internalTwoDemandGlobal_proper :
    ProperColoring internalTwoDemandGlobalCertificate.coloring :=
  internalTwoDemandGlobalCertificate.proper

theorem internalTwoDemandGlobal_strongTwoSeparated :
    StrongTwoSeparated internalTwoDemandGlobalCertificate.coloring :=
  (strongTwoSeparated_iff_exists_with
    internalTwoDemandGlobalCertificate.coloring).2
      ⟨internalTwoDemandGlobalCertificate.xi,
        internalTwoDemandGlobalCertificate.strong⟩

theorem internalTwoDemandGlobal_uniqueDesigns :
    UniqueDesigns
      (sequenceOfProperColoring
        internalTwoDemandGlobalCertificate.coloring
        internalTwoDemandGlobalCertificate.proper)
      internalTwoDemandTarget := by
  simpa [internalTwoDemandGlobalCertificate] using
    exactTwoShortHelices_uniqueDesigns
      internalTwoDemandTarget_inTargetClassK2

/-! ## Negative class controls -/

/-- Dot-bracket `((.))((.))((.))`: three short helices. -/
def threeShortControl : SecondaryStructure 15 where
  arcs := {
    ⟨0, 4, by decide⟩, ⟨1, 3, by decide⟩,
    ⟨5, 9, by decide⟩, ⟨6, 8, by decide⟩,
    ⟨10, 14, by decide⟩, ⟨11, 13, by decide⟩ }
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem threeShortControl_shortHelixCount :
    shortHelixCount threeShortControl = 3 := by
  decide

theorem threeShortControl_not_inTargetClassKLeTwo :
    ¬ InTargetClassKLeTwo threeShortControl := by
  decide

/-- A single adjacent pair is one maximal helix of length one. -/
def lengthOneControl : SecondaryStructure 2 where
  arcs := {⟨0, 1, by decide⟩}
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem lengthOneControl_not_inTargetClassKLeTwo :
    ¬ InTargetClassKLeTwo lengthOneControl := by
  decide

/- The concrete example theorems are validation endpoints, not reusable
automation premises.  Register only this module's local declaration-name
components with Lean's documented premise deny-list.  Besides keeping premise
search focused, this prevents the suggestion exporter from recursively
traversing the deliberately large kernel-reduced 26-position signatures. -/
run_cmd do
  let env ← Lean.getEnv
  let localComponents : List String := env.constants.map₂.foldl (init := [])
    fun names name _ =>
      if (env.getModuleIdxFor? name).isNone then
        match name with
        | .str _ component => component :: names
        | _ => names
      else
        names
  Lean.modifyEnv fun env =>
    localComponents.foldl (fun env component =>
      Lean.LibrarySuggestions.nameDenyListExt.addEntry env component) env

end RNA
