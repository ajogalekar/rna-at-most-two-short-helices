module

public import RNA.GlobalSequence
public import RNA.Milestone3Examples

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# Kernel-checked sequence-assignment examples for Milestone 4

These examples exercise the deterministic sequence assignment and its
load-bearing grey-orientation rule, the tight pairing inventory, and the
prefix-balance obstruction.
-/

namespace RNA.Milestone4Examples

open Nucleotide

/-! ## The two nodes of `(())` -/

def nestedOuterNode : PairedNode Examples.nestedTarget :=
  ⟨Examples.outerArc, by decide⟩

def nestedInnerNode : PairedNode Examples.nestedTarget :=
  ⟨Examples.innerArc, by decide⟩

theorem nestedInner_parent :
    parent Examples.nestedTarget (Sum.inl nestedInnerNode) =
      some nestedOuterNode := by
  decide

/-! ## An explicit black coloring produces `GGCC` -/

def nestedAllBlackColoring : Coloring Examples.nestedTarget :=
  fun _ => Color.black

theorem nestedAllBlackColoring_proper :
    ProperColoring nestedAllBlackColoring := by
  decide

noncomputable def nestedAllBlackSequence : Sequence 4 :=
  sequenceOfProperColoring nestedAllBlackColoring
    nestedAllBlackColoring_proper

theorem nestedAllBlackSequence_eq_ggcc :
    nestedAllBlackSequence = Examples.ggcc := by
  funext i
  fin_cases i
  · change nestedAllBlackSequence nestedOuterNode.val.left = G
    simpa [nestedAllBlackSequence] using
      (sequenceOfProperColoring_black_left nestedAllBlackColoring
        nestedAllBlackColoring_proper nestedOuterNode rfl)
  · change nestedAllBlackSequence nestedInnerNode.val.left = G
    simpa [nestedAllBlackSequence] using
      (sequenceOfProperColoring_black_left nestedAllBlackColoring
        nestedAllBlackColoring_proper nestedInnerNode rfl)
  · change nestedAllBlackSequence nestedInnerNode.val.right = C
    simpa [nestedAllBlackSequence] using
      (sequenceOfProperColoring_black_right nestedAllBlackColoring
        nestedAllBlackColoring_proper nestedInnerNode rfl)
  · change nestedAllBlackSequence nestedOuterNode.val.right = C
    simpa [nestedAllBlackSequence] using
      (sequenceOfProperColoring_black_right nestedAllBlackColoring
        nestedAllBlackColoring_proper nestedOuterNode rfl)

theorem nestedAllBlackSequence_targetCompatible :
    StructureCompatible nestedAllBlackSequence Examples.nestedTarget := by
  exact structureCompatible_sequenceOfProperColoring
    nestedAllBlackColoring nestedAllBlackColoring_proper

/-! ## Correct top-down orientation of the all-grey coloring -/

def nestedAllGreyColoring : Coloring Examples.nestedTarget :=
  fun _ => Color.grey

theorem nestedAllGreyColoring_proper :
    ProperColoring nestedAllGreyColoring := by
  decide

theorem nestedAllGrey_inner_copies_outer :
    leftLetterOfProperColoring nestedAllGreyColoring
        nestedAllGreyColoring_proper nestedInnerNode =
      leftLetterOfProperColoring nestedAllGreyColoring
        nestedAllGreyColoring_proper nestedOuterNode := by
  exact leftLetter_grey_child_of_grey_parent
    nestedAllGreyColoring nestedAllGreyColoring_proper
    nestedOuterNode nestedInnerNode rfl nestedInner_parent rfl

theorem nestedAllGrey_outer_left_eq_A :
    leftLetterOfProperColoring nestedAllGreyColoring
      nestedAllGreyColoring_proper nestedOuterNode = A := by
  rw [leftLetter_grey_at_anchor nestedAllGreyColoring
    nestedAllGreyColoring_proper nestedOuterNode rfl none (by decide)]
  · have hchild : nestedOuterNode ∈
        pairedChildren Examples.nestedTarget none := by
      decide
    have hmem : nestedOuterNode ∈
        orderedGreyChildren nestedAllGreyColoring none :=
      (mem_orderedGreyChildren_iff nestedAllGreyColoring none
        nestedOuterNode).2 ⟨hchild, rfl⟩
    have hrank := List.idxOf_lt_length_of_mem hmem
    rw [orderedGreyChildren_length] at hrank
    have hfilter := Finset.card_filter_le
      (pairedChildren Examples.nestedTarget none)
      (fun v => nestedAllGreyColoring v = Color.grey)
    change (childrenOfColor nestedAllGreyColoring none Color.grey).card ≤
      (pairedChildren Examples.nestedTarget none).card at hfilter
    have hrootCard :
        (pairedChildren Examples.nestedTarget none).card = 1 := by
      decide
    have hrankZero :
        greySiblingRank nestedAllGreyColoring none nestedOuterNode = 0 := by
      change (orderedGreyChildren nestedAllGreyColoring none).idxOf
        nestedOuterNode = 0
      omega
    simp [greyRankLetter, hrankZero]
  · intro q h
    cases h

theorem nestedAllGrey_inner_left_eq_A :
    leftLetterOfProperColoring nestedAllGreyColoring
      nestedAllGreyColoring_proper nestedInnerNode = A := by
  rw [nestedAllGrey_inner_copies_outer]
  exact nestedAllGrey_outer_left_eq_A

def aauu : Sequence 4 := ![A, A, U, U]

noncomputable def nestedAllGreySequence : Sequence 4 :=
  sequenceOfProperColoring nestedAllGreyColoring nestedAllGreyColoring_proper

theorem nestedAllGreySequence_eq_aauu :
    nestedAllGreySequence = aauu := by
  funext i
  fin_cases i
  · change nestedAllGreySequence nestedOuterNode.val.left = A
    simpa [nestedAllGreySequence] using nestedAllGrey_outer_left_eq_A
  · change nestedAllGreySequence nestedInnerNode.val.left = A
    simpa [nestedAllGreySequence] using nestedAllGrey_inner_left_eq_A
  · change nestedAllGreySequence nestedInnerNode.val.right = U
    simp [nestedAllGreySequence, nestedAllGrey_inner_left_eq_A]
  · change nestedAllGreySequence nestedOuterNode.val.right = U
    simp [nestedAllGreySequence, nestedAllGrey_outer_left_eq_A]

theorem nestedAllGreySequence_targetCompatible :
    StructureCompatible nestedAllGreySequence Examples.nestedTarget := by
  exact structureCompatible_sequenceOfProperColoring
    nestedAllGreyColoring nestedAllGreyColoring_proper

/-! ## The deliberately wrong opposite orientation gives `AUAU` -/

def incorrectOppositeGreyOrientation : Sequence 4 := Examples.auau

theorem incorrectOppositeGreyOrientation_eq_auau :
    incorrectOppositeGreyOrientation = ![A, U, A, U] := by
  rfl

theorem correctGreyOrientation_ne_incorrect :
    nestedAllGreySequence ≠ incorrectOppositeGreyOrientation := by
  rw [nestedAllGreySequence_eq_aauu]
  decide

theorem incorrectOppositeGreyOrientation_disjoint_tie :
    StructureCompatible incorrectOppositeGreyOrientation Examples.nestedTarget ∧
      StructureCompatible incorrectOppositeGreyOrientation Examples.disjointTarget ∧
      Examples.disjointTarget ≠ Examples.nestedTarget ∧
      pairCount Examples.disjointTarget = pairCount Examples.nestedTarget := by
  exact Examples.auau_disjoint_tie

/-! ## Two grey root children receive distinct deterministic orientations -/

def disjointLeftNode : PairedNode Examples.disjointTarget :=
  ⟨Examples.leftAdjacentArc, by decide⟩

def disjointRightNode : PairedNode Examples.disjointTarget :=
  ⟨Examples.rightAdjacentArc, by decide⟩

def disjointAllGreyColoring : Coloring Examples.disjointTarget :=
  fun _ => Color.grey

theorem disjointAllGreyColoring_proper :
    ProperColoring disjointAllGreyColoring := by
  decide

theorem disjointLeft_is_root_child :
    disjointLeftNode ∈ pairedChildren Examples.disjointTarget none := by
  decide

theorem disjointRight_is_root_child :
    disjointRightNode ∈ pairedChildren Examples.disjointTarget none := by
  decide

theorem disjointGreyRoot_left_eq_A :
    leftLetterOfProperColoring disjointAllGreyColoring
      disjointAllGreyColoring_proper disjointLeftNode = A := by
  rw [leftLetter_grey_at_anchor disjointAllGreyColoring
    disjointAllGreyColoring_proper disjointLeftNode rfl none (by decide)]
  · let L := orderedGreyChildren disjointAllGreyColoring none
    have hleftMem : disjointLeftNode ∈ L :=
      (mem_orderedGreyChildren_iff disjointAllGreyColoring none
        disjointLeftNode).2 ⟨disjointLeft_is_root_child, rfl⟩
    have hrightMem : disjointRightNode ∈ L :=
      (mem_orderedGreyChildren_iff disjointAllGreyColoring none
        disjointRightNode).2 ⟨disjointRight_is_root_child, rfl⟩
    have hleftRankLt := List.idxOf_lt_length_of_mem hleftMem
    have hrightRankLt := List.idxOf_lt_length_of_mem hrightMem
    have hsorted : L.SortedLT := by
      exact Finset.sortedLT_sort
        (childrenOfColor disjointAllGreyColoring none Color.grey)
    have hnodeOrder : disjointLeftNode < disjointRightNode := by
      decide
    have hrankOrder :
        greySiblingRank disjointAllGreyColoring none disjointLeftNode <
          greySiblingRank disjointAllGreyColoring none disjointRightNode := by
      change L.idxOf disjointLeftNode < L.idxOf disjointRightNode
      rw [← hsorted.getElem_lt_getElem_iff
        (hi := hleftRankLt) (hj := hrightRankLt)]
      simpa using hnodeOrder
    have hleftLtTwo := greySiblingRank_lt_two disjointAllGreyColoring
      disjointAllGreyColoring_proper none disjointLeftNode
      disjointLeft_is_root_child rfl
    have hrightLtTwo := greySiblingRank_lt_two disjointAllGreyColoring
      disjointAllGreyColoring_proper none disjointRightNode
      disjointRight_is_root_child rfl
    have hleftZero :
        greySiblingRank disjointAllGreyColoring none disjointLeftNode = 0 := by
      omega
    simp [greyRankLetter, hleftZero]
  · intro q h
    cases h

theorem disjointGreyRoot_right_eq_U :
    leftLetterOfProperColoring disjointAllGreyColoring
      disjointAllGreyColoring_proper disjointRightNode = U := by
  rw [leftLetter_grey_at_anchor disjointAllGreyColoring
    disjointAllGreyColoring_proper disjointRightNode rfl none (by decide)]
  · let L := orderedGreyChildren disjointAllGreyColoring none
    have hleftMem : disjointLeftNode ∈ L :=
      (mem_orderedGreyChildren_iff disjointAllGreyColoring none
        disjointLeftNode).2 ⟨disjointLeft_is_root_child, rfl⟩
    have hrightMem : disjointRightNode ∈ L :=
      (mem_orderedGreyChildren_iff disjointAllGreyColoring none
        disjointRightNode).2 ⟨disjointRight_is_root_child, rfl⟩
    have hleftRankLt := List.idxOf_lt_length_of_mem hleftMem
    have hrightRankLt := List.idxOf_lt_length_of_mem hrightMem
    have hsorted : L.SortedLT := by
      exact Finset.sortedLT_sort
        (childrenOfColor disjointAllGreyColoring none Color.grey)
    have hnodeOrder : disjointLeftNode < disjointRightNode := by
      decide
    have hrankOrder :
        greySiblingRank disjointAllGreyColoring none disjointLeftNode <
          greySiblingRank disjointAllGreyColoring none disjointRightNode := by
      change L.idxOf disjointLeftNode < L.idxOf disjointRightNode
      rw [← hsorted.getElem_lt_getElem_iff
        (hi := hleftRankLt) (hj := hrightRankLt)]
      simpa using hnodeOrder
    have hrightLtTwo := greySiblingRank_lt_two disjointAllGreyColoring
      disjointAllGreyColoring_proper none disjointRightNode
      disjointRight_is_root_child rfl
    have hrightOne :
        greySiblingRank disjointAllGreyColoring none disjointRightNode = 1 := by
      omega
    simp [greyRankLetter, hrightOne]
  · intro q h
    cases h

theorem disjointGreyRoot_left_letters_ne :
    leftLetterOfProperColoring disjointAllGreyColoring
        disjointAllGreyColoring_proper disjointLeftNode ≠
      leftLetterOfProperColoring disjointAllGreyColoring
        disjointAllGreyColoring_proper disjointRightNode := by
  rw [disjointGreyRoot_left_eq_A, disjointGreyRoot_right_eq_U]
  decide

def auua : Sequence 4 := ![A, U, U, A]

noncomputable def disjointAllGreySequence : Sequence 4 :=
  sequenceOfProperColoring disjointAllGreyColoring
    disjointAllGreyColoring_proper

theorem disjointAllGreySequence_eq_auua :
    disjointAllGreySequence = auua := by
  funext i
  fin_cases i
  · change disjointAllGreySequence disjointLeftNode.val.left = A
    simpa [disjointAllGreySequence] using disjointGreyRoot_left_eq_A
  · change disjointAllGreySequence disjointLeftNode.val.right = U
    simp [disjointAllGreySequence, disjointGreyRoot_left_eq_A]
  · change disjointAllGreySequence disjointRightNode.val.left = U
    simpa [disjointAllGreySequence] using disjointGreyRoot_right_eq_U
  · change disjointAllGreySequence disjointRightNode.val.right = A
    simp [disjointAllGreySequence, disjointGreyRoot_right_eq_U]

/-! ## Canonical class-K sequence witness and compatibility -/

theorem smallestCertificate_row_xiOne :
    Milestone3Examples.smallestCertificate.allocation.row = .xiOne := by
  have hsmall :
      ¬ HasUnpairedChild Milestone3Examples.smallestTarget none ∧
        pairedChildCount Milestone3Examples.smallestTarget none ≤ 2 := by
    decide
  rcases Milestone3Examples.smallestCertificate.smallRow hsmall with
    hrow | hrow
  · exact hrow
  · have hcount :=
      Milestone3Examples.smallestCertificate.allocation.count_eq
    have hone :
        pairedChildCount Milestone3Examples.smallestTarget none = 1 := by
      decide
    rw [hrow, hone] at hcount
    simp [RootRow.count] at hcount

theorem smallestOuter_is_root_child :
    nestedOuterNode ∈
      pairedChildren Milestone3Examples.smallestTarget none := by
  decide

noncomputable def smallestOuterRootIndex :
    Fin (pairedChildCount Milestone3Examples.smallestTarget none) :=
  pairedChildIndex Milestone3Examples.smallestTarget none nestedOuterNode
    smallestOuter_is_root_child

def smallestExplicitHelix :
    MaximalHelix Milestone3Examples.smallestTarget :=
  ⟨(Examples.outerArc, ⟨2, by decide⟩), by decide⟩

noncomputable def smallestRootHelix :
    MaximalHelix Milestone3Examples.smallestTarget :=
  outgoingHelixAtRootSlot Milestone3Examples.smallestTarget
    smallestOuterRootIndex

theorem smallestRootHelix_eq_explicit :
    smallestRootHelix = smallestExplicitHelix := by
  apply MaximalHelix.ext_outer
  change smallestRootHelix.head = smallestExplicitHelix.head
  have hhead := outgoingHelixAtRootSlot_head
    Milestone3Examples.smallestTarget smallestOuterRootIndex
  unfold smallestOuterRootIndex at hhead
  rw [orderedPairedChild_pairedChildIndex] at hhead
  exact congrArg Subtype.val hhead

theorem smallestExplicitHelix_terminal :
    smallestExplicitHelix.terminalNode = nestedInnerNode := by
  apply Subtype.ext
  apply Arc.stackOffset_arc_unique
    smallestExplicitHelix.terminalPair_stackOffset
  decide

theorem smallestCertificate_outer_black :
    Milestone3Examples.smallestCertificate.coloring nestedOuterNode =
      Color.black := by
  have hportMem :
      Milestone3Examples.smallestCertificate.allocation.ports
          smallestOuterRootIndex ∈
        portMultiset
          Milestone3Examples.smallestCertificate.allocation.ports := by
    simp [portMultiset]
  rw [Milestone3Examples.smallestCertificate.allocation.sameDisplayedMultiset,
    smallestCertificate_row_xiOne] at hportMem
  have hdisplay :
      portMultiset RootRow.xiOne.ports =
        ({Color.black} : Multiset Color) := by
    decide
  rw [hdisplay] at hportMem
  have hport :
      Milestone3Examples.smallestCertificate.allocation.ports
        smallestOuterRootIndex = Color.black := by
    simpa using hportMem
  have hinstalled := assembledRootColoring_childPortsInstalled
    Milestone3Examples.smallestTarget_in_classK
    Milestone3Examples.smallestCertificate.allocation
    smallestOuterRootIndex
  unfold smallestOuterRootIndex at hinstalled
  rw [orderedPairedChild_pairedChildIndex] at hinstalled
  rw [Milestone3Examples.smallestCertificate.coloring_eq]
  exact hinstalled.trans hport

theorem nestedInner_is_E : IsEEndpoint nestedInnerNode := by
  decide

theorem nestedInner_is_child_of_outer :
    nestedInnerNode ∈
      pairedChildren Milestone3Examples.smallestTarget
        (some nestedOuterNode) := by
  decide

theorem smallestCertificate_inner_black :
    Milestone3Examples.smallestCertificate.coloring nestedInnerNode =
      Color.black := by
  cases hinner :
      Milestone3Examples.smallestCertificate.coloring nestedInnerNode with
  | black => rfl
  | white =>
      exfalso
      have hzero := white_children_card_eq_zero_of_parent_black
        Milestone3Examples.smallestCertificate.coloring
        Milestone3Examples.smallestCertificate.proper nestedOuterNode
        smallestCertificate_outer_black
      have hmem : nestedInnerNode ∈ childrenOfColor
          Milestone3Examples.smallestCertificate.coloring
          (some nestedOuterNode) Color.white :=
        (mem_childrenOfColor_iff
          Milestone3Examples.smallestCertificate.coloring
          (some nestedOuterNode) Color.white nestedInnerNode).2
          ⟨nestedInner_is_child_of_outer, hinner⟩
      rw [Finset.card_eq_zero.mp hzero] at hmem
      simp at hmem
  | grey =>
      exfalso
      let cert := constructedRootSubtreeCertificate
        Milestone3Examples.smallestTarget_in_classK
        Milestone3Examples.smallestCertificate.allocation
        smallestOuterRootIndex
      have hpost := assembledRootSubtreePostcondition
        Milestone3Examples.smallestTarget_in_classK
        Milestone3Examples.smallestCertificate.allocation
        smallestOuterRootIndex
      have hE : HasEndpointType
          (outgoingHelixAtRootSlot Milestone3Examples.smallestTarget
            smallestOuterRootIndex).terminalNode .E := by
        change IsEEndpoint smallestRootHelix.terminalNode
        rw [smallestRootHelix_eq_explicit,
          smallestExplicitHelix_terminal]
        exact nestedInner_is_E
      have hendpoint : cert.endpoint = .E :=
        endpointType_unique
          (outgoingHelixAtRootSlot Milestone3Examples.smallestTarget
            smallestOuterRootIndex).terminalNode
          cert.endpoint_spec hE
      have hterminal := hpost.terminalResidue
      rw [hendpoint] at hterminal
      change levelParity
          (pairedLevel Milestone3Examples.smallestCertificate.coloring
            smallestRootHelix.terminalNode) =
        Milestone3Examples.smallestCertificate.allocation.row.xi at hterminal
      rw [smallestRootHelix_eq_explicit,
        smallestExplicitHelix_terminal] at hterminal
      have hgrey :=
        Milestone3Examples.smallestCertificate.strong.2
          nestedInnerNode hinner
      exact Milestone3Examples.smallestCertificate.allocation.row.xi.ne_opposite
        (hterminal.symm.trans hgrey)

noncomputable def smallestCanonicalSequence : Sequence 4 :=
  sequenceOfProperColoring
    Milestone3Examples.smallestCertificate.coloring
    Milestone3Examples.smallestCertificate.proper

theorem smallestCanonicalSequence_eq_ggcc :
    smallestCanonicalSequence = Examples.ggcc := by
  funext i
  fin_cases i
  · change smallestCanonicalSequence nestedOuterNode.val.left = G
    simpa [smallestCanonicalSequence] using
      (sequenceOfProperColoring_black_left
        Milestone3Examples.smallestCertificate.coloring
        Milestone3Examples.smallestCertificate.proper nestedOuterNode
        smallestCertificate_outer_black)
  · change smallestCanonicalSequence nestedInnerNode.val.left = G
    simpa [smallestCanonicalSequence] using
      (sequenceOfProperColoring_black_left
        Milestone3Examples.smallestCertificate.coloring
        Milestone3Examples.smallestCertificate.proper nestedInnerNode
        smallestCertificate_inner_black)
  · change smallestCanonicalSequence nestedInnerNode.val.right = C
    simpa [smallestCanonicalSequence] using
      (sequenceOfProperColoring_black_right
        Milestone3Examples.smallestCertificate.coloring
        Milestone3Examples.smallestCertificate.proper nestedInnerNode
        smallestCertificate_inner_black)
  · change smallestCanonicalSequence nestedOuterNode.val.right = C
    simpa [smallestCanonicalSequence] using
      (sequenceOfProperColoring_black_right
        Milestone3Examples.smallestCertificate.coloring
        Milestone3Examples.smallestCertificate.proper nestedOuterNode
        smallestCertificate_outer_black)

theorem smallestCanonicalSequence_targetCompatible :
    StructureCompatible smallestCanonicalSequence
      Milestone3Examples.smallestTarget := by
  exact structureCompatible_sequenceOfProperColoring
    Milestone3Examples.smallestCertificate.coloring
    Milestone3Examples.smallestCertificate.proper

/-- The inventory theorem applies to every compatible secondary structure on
the same four-position backbone, not only to enumerated examples. -/
theorem smallestCanonicalSequence_inventory_bound
    (S : SecondaryStructure 4)
    (hS : StructureCompatible smallestCanonicalSequence S) :
    pairCount S ≤ pairCount Milestone3Examples.smallestTarget := by
  exact pairCount_le_sequenceOfProperColoring
    Milestone3Examples.smallestCertificate.coloring
    Milestone3Examples.smallestCertificate.proper S hS

noncomputable def smallestGlobalSequenceCertificate :
    GlobalSequenceAssignmentCertificate
      Milestone3Examples.smallestTarget
      Milestone3Examples.smallestTarget_in_classK :=
  globalSequenceAssignmentCertificate
    Milestone3Examples.smallestTarget_in_classK

theorem smallestGlobalSequence_targetCompatible :
    StructureCompatible
      smallestGlobalSequenceCertificate.assignment.sequence
      Milestone3Examples.smallestTarget :=
  smallestGlobalSequenceCertificate.assignment.targetCompatible

theorem smallestGlobalSequence_eq_ggcc :
    smallestGlobalSequenceCertificate.assignment.sequence = Examples.ggcc := by
  change smallestCanonicalSequence = Examples.ggcc
  exact smallestCanonicalSequence_eq_ggcc

/-! ## A nontrivial equality case for the pairing inventory

The assigned sequence is `AUGCA`.  The target pairs `(0,1)` and `(2,3)`, while
the distinct competitor pairs `(1,4)` and `(2,3)`.  Thus the competitor ties
the target and visibly consumes its unique `U`, `C`, and `G` positions.
-/

def inventoryGreyArc : Arc 5 := ⟨0, 1, by decide⟩

def inventoryBlackArc : Arc 5 := ⟨2, 3, by decide⟩

def inventoryTarget : SecondaryStructure 5 where
  arcs := {inventoryGreyArc, inventoryBlackArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

def inventoryGreyNode : PairedNode inventoryTarget :=
  ⟨inventoryGreyArc, by decide⟩

def inventoryBlackNode : PairedNode inventoryTarget :=
  ⟨inventoryBlackArc, by decide⟩

def inventoryColoring : Coloring inventoryTarget :=
  fun v => if v.val = inventoryGreyArc then Color.grey else Color.black

theorem inventoryColoring_proper : ProperColoring inventoryColoring := by
  decide

theorem inventoryGreyNode_color :
    inventoryColoring inventoryGreyNode = Color.grey := by
  rfl

theorem inventoryBlackNode_color :
    inventoryColoring inventoryBlackNode = Color.black := by
  rfl

theorem inventoryGreyNode_left_eq_A :
    leftLetterOfProperColoring inventoryColoring
      inventoryColoring_proper inventoryGreyNode = A := by
  rw [leftLetter_grey_at_anchor inventoryColoring
    inventoryColoring_proper inventoryGreyNode inventoryGreyNode_color
    none (by decide)]
  · have hmem : inventoryGreyNode ∈
        orderedGreyChildren inventoryColoring none :=
      (mem_orderedGreyChildren_iff inventoryColoring none
        inventoryGreyNode).2 ⟨by decide, inventoryGreyNode_color⟩
    have hcardLe :
        (childrenOfColor inventoryColoring none Color.grey).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have haGrey :=
        (mem_childrenOfColor_iff inventoryColoring none Color.grey a).1 ha |>.2
      have hbGrey :=
        (mem_childrenOfColor_iff inventoryColoring none Color.grey b).1 hb |>.2
      have haVal : a.val = inventoryGreyArc := by
        by_contra hne
        simp [inventoryColoring, hne] at haGrey
      have hbVal : b.val = inventoryGreyArc := by
        by_contra hne
        simp [inventoryColoring, hne] at hbGrey
      exact Subtype.ext (haVal.trans hbVal.symm)
    have hcardPos :
        0 < (childrenOfColor inventoryColoring none Color.grey).card :=
      Finset.card_pos.mpr ⟨inventoryGreyNode,
        (mem_childrenOfColor_iff inventoryColoring none Color.grey
          inventoryGreyNode).2 ⟨by decide, inventoryGreyNode_color⟩⟩
    have hcardEq :
        (childrenOfColor inventoryColoring none Color.grey).card = 1 := by
      omega
    have hrankLt := List.idxOf_lt_length_of_mem hmem
    rw [orderedGreyChildren_length, hcardEq] at hrankLt
    have hrank :
        greySiblingRank inventoryColoring none inventoryGreyNode = 0 := by
      change (orderedGreyChildren inventoryColoring none).idxOf
        inventoryGreyNode = 0
      omega
    simp [greyRankLetter, hrank]
  · intro q h
    cases h

def augca : Sequence 5 := ![A, U, G, C, A]

noncomputable def inventorySequence : Sequence 5 :=
  sequenceOfProperColoring inventoryColoring inventoryColoring_proper

theorem inventorySequence_eq_augca : inventorySequence = augca := by
  funext i
  fin_cases i
  · change inventorySequence inventoryGreyNode.val.left = A
    simpa [inventorySequence] using inventoryGreyNode_left_eq_A
  · change inventorySequence inventoryGreyNode.val.right = U
    simp [inventorySequence, inventoryGreyNode_left_eq_A]
  · change inventorySequence inventoryBlackNode.val.left = G
    simpa [inventorySequence] using
      (sequenceOfProperColoring_black_left inventoryColoring
        inventoryColoring_proper inventoryBlackNode inventoryBlackNode_color)
  · change inventorySequence inventoryBlackNode.val.right = C
    simpa [inventorySequence] using
      (sequenceOfProperColoring_black_right inventoryColoring
        inventoryColoring_proper inventoryBlackNode inventoryBlackNode_color)
  · let u : UnpairedPosition inventoryTarget := ⟨4, by decide⟩
    change inventorySequence (4 : Fin 5) = A
    have hcoord : (4 : Fin 5) = u.val := by
      apply Fin.ext
      simp [u]
    rw [hcoord]
    exact sequenceOfProperColoring_unpaired inventoryColoring
      inventoryColoring_proper u

theorem inventorySequence_counts :
    nucleotideCount inventorySequence A = 2 ∧
      nucleotideCount inventorySequence U = 1 ∧
      nucleotideCount inventorySequence C = 1 ∧
      nucleotideCount inventorySequence G = 1 := by
  rw [inventorySequence_eq_augca]
  decide

def inventoryTieOuterArc : Arc 5 := ⟨1, 4, by decide⟩

def inventoryTie : SecondaryStructure 5 where
  arcs := {inventoryTieOuterArc, inventoryBlackArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem inventoryTie_compatible :
    StructureCompatible inventorySequence inventoryTie := by
  rw [inventorySequence_eq_augca]
  decide

theorem inventoryTie_distinct : inventoryTie ≠ inventoryTarget := by
  decide

theorem inventoryTie_pairCount_eq :
    pairCount inventoryTie = pairCount inventoryTarget := by
  decide

theorem inventoryTie_respects_universal_bound :
    pairCount inventoryTie ≤ pairCount inventoryTarget := by
  exact pairCount_le_sequenceOfProperColoring inventoryColoring
    inventoryColoring_proper inventoryTie inventoryTie_compatible

theorem inventoryTie_uses_all_limiting_nucleotides :
    (∀ i : Fin 5, inventorySequence i = U →
      inventoryTie.positionPaired i) ∧
      (∀ i : Fin 5, inventorySequence i = C →
        inventoryTie.positionPaired i) ∧
      (∀ i : Fin 5, inventorySequence i = G →
        inventoryTie.positionPaired i) := by
  exact equality_uses_all_limiting_nucleotides inventoryColoring
    inventoryColoring_proper inventoryTie inventoryTie_compatible
    inventoryTie_pairCount_eq

theorem inventoryTie_pairs_explicit_U_C_G :
    inventorySequence (1 : Fin 5) = U ∧
      inventoryTie.positionPaired (1 : Fin 5) ∧
      inventorySequence (3 : Fin 5) = C ∧
      inventoryTie.positionPaired (3 : Fin 5) ∧
      inventorySequence (2 : Fin 5) = G ∧
      inventoryTie.positionPaired (2 : Fin 5) := by
  rw [inventorySequence_eq_augca]
  decide

/-! ## Representative prefix balances on the internal M-to-L target

This explicit proper coloring makes the incoming terminal and the short-helix
head grey and every other pair black.  Its short-head left and grey right
balances are `2`; the target-unpaired position inside the short L loop has
balance `3`.
-/

def internalBalanceColoring :
    Coloring Milestone3Examples.internalMToLTarget :=
  fun v =>
    if v.val = Milestone3Examples.internalIncomingTerminal ∨
        v.val = Milestone3Examples.internalShortOuter then
      Color.grey
    else
      Color.black

theorem internalBalanceColoring_proper :
    ProperColoring internalBalanceColoring := by
  decide

theorem internalBalance_shortHead_grey :
    internalBalanceColoring
      Milestone3Examples.internalShortHeadNode = Color.grey := by
  rfl

def internalBalanceUnpaired :
    UnpairedPosition Milestone3Examples.internalMToLTarget :=
  ⟨5, by decide⟩

noncomputable def internalBalanceSequence : Sequence 17 :=
  sequenceOfProperColoring internalBalanceColoring
    internalBalanceColoring_proper

theorem internalBalance_shortHead_level :
    pairedLevel internalBalanceColoring
      Milestone3Examples.internalShortHeadNode = 2 := by
  decide

theorem internalBalance_unpaired_level :
    unpairedLevel internalBalanceColoring internalBalanceUnpaired = 3 := by
  decide

theorem internalBalance_pairedLeft_value :
    prefixBalanceAt internalBalanceSequence
      Milestone3Examples.internalShortHeadNode.val.left = 2 := by
  calc
    prefixBalanceAt internalBalanceSequence
        Milestone3Examples.internalShortHeadNode.val.left =
        pairedLevel internalBalanceColoring
          Milestone3Examples.internalShortHeadNode := by
      simpa [internalBalanceSequence] using
        (prefixBalanceAt_pairedLeft_eq_pairedLevel internalBalanceColoring
          internalBalanceColoring_proper
          Milestone3Examples.internalShortHeadNode)
    _ = 2 := internalBalance_shortHead_level

theorem internalBalance_unpaired_value :
    prefixBalanceAt internalBalanceSequence internalBalanceUnpaired.val = 3 := by
  calc
    prefixBalanceAt internalBalanceSequence internalBalanceUnpaired.val =
        unpairedLevel internalBalanceColoring internalBalanceUnpaired := by
      simpa [internalBalanceSequence] using
        (prefixBalanceAt_unpaired_eq_unpairedLevel internalBalanceColoring
          internalBalanceColoring_proper internalBalanceUnpaired)
    _ = 3 := internalBalance_unpaired_level

theorem internalBalance_greyRight_value :
    prefixBalanceAt internalBalanceSequence
      Milestone3Examples.internalShortHeadNode.val.right = 2 ∧
    prefixBalanceAt internalBalanceSequence
      Milestone3Examples.internalShortHeadNode.val.left = 2 ∧
    pairedLevel internalBalanceColoring
      Milestone3Examples.internalShortHeadNode = 2 := by
  have hgrey := prefixBalanceAt_greyRight_eq internalBalanceColoring
    internalBalanceColoring_proper
    Milestone3Examples.internalShortHeadNode internalBalance_shortHead_grey
  constructor
  · calc
      prefixBalanceAt internalBalanceSequence
          Milestone3Examples.internalShortHeadNode.val.right =
          prefixBalanceAt internalBalanceSequence
            Milestone3Examples.internalShortHeadNode.val.left := by
        simpa [internalBalanceSequence] using hgrey.1
      _ = 2 := internalBalance_pairedLeft_value
  · exact ⟨internalBalance_pairedLeft_value,
      internalBalance_shortHead_level⟩

/-! ## An explicit unequal-balance A-U competitor arc

The target sequence is `AUGAC`.  The competitor contains only `(1,3)`, a
compatible `U-A` arc.  Its endpoint balances are `0` and `1`; position `2`
is the intervening `G` and is explicitly unpaired by the competitor.
-/

def imbalanceGreyArc : Arc 5 := ⟨0, 1, by decide⟩

def imbalanceBlackArc : Arc 5 := ⟨2, 4, by decide⟩

def imbalanceTarget : SecondaryStructure 5 where
  arcs := {imbalanceGreyArc, imbalanceBlackArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

def imbalanceGreyNode : PairedNode imbalanceTarget :=
  ⟨imbalanceGreyArc, by decide⟩

def imbalanceBlackNode : PairedNode imbalanceTarget :=
  ⟨imbalanceBlackArc, by decide⟩

def imbalanceUnpaired : UnpairedPosition imbalanceTarget :=
  ⟨3, by decide⟩

def imbalanceColoring : Coloring imbalanceTarget :=
  fun v => if v.val = imbalanceGreyArc then Color.grey else Color.black

theorem imbalanceColoring_proper : ProperColoring imbalanceColoring := by
  decide

theorem imbalanceGreyNode_color :
    imbalanceColoring imbalanceGreyNode = Color.grey := by
  rfl

theorem imbalanceBlackNode_color :
    imbalanceColoring imbalanceBlackNode = Color.black := by
  rfl

theorem imbalanceGreyNode_left_eq_A :
    leftLetterOfProperColoring imbalanceColoring
      imbalanceColoring_proper imbalanceGreyNode = A := by
  rw [leftLetter_grey_at_anchor imbalanceColoring
    imbalanceColoring_proper imbalanceGreyNode imbalanceGreyNode_color
    none (by decide)]
  · have hmem : imbalanceGreyNode ∈
        orderedGreyChildren imbalanceColoring none :=
      (mem_orderedGreyChildren_iff imbalanceColoring none
        imbalanceGreyNode).2 ⟨by decide, imbalanceGreyNode_color⟩
    have hcardLe :
        (childrenOfColor imbalanceColoring none Color.grey).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have haGrey :=
        (mem_childrenOfColor_iff imbalanceColoring none Color.grey a).1 ha |>.2
      have hbGrey :=
        (mem_childrenOfColor_iff imbalanceColoring none Color.grey b).1 hb |>.2
      have haVal : a.val = imbalanceGreyArc := by
        by_contra hne
        simp [imbalanceColoring, hne] at haGrey
      have hbVal : b.val = imbalanceGreyArc := by
        by_contra hne
        simp [imbalanceColoring, hne] at hbGrey
      exact Subtype.ext (haVal.trans hbVal.symm)
    have hcardPos :
        0 < (childrenOfColor imbalanceColoring none Color.grey).card :=
      Finset.card_pos.mpr ⟨imbalanceGreyNode,
        (mem_childrenOfColor_iff imbalanceColoring none Color.grey
          imbalanceGreyNode).2 ⟨by decide, imbalanceGreyNode_color⟩⟩
    have hcardEq :
        (childrenOfColor imbalanceColoring none Color.grey).card = 1 := by
      omega
    have hrankLt := List.idxOf_lt_length_of_mem hmem
    rw [orderedGreyChildren_length, hcardEq] at hrankLt
    have hrank :
        greySiblingRank imbalanceColoring none imbalanceGreyNode = 0 := by
      change (orderedGreyChildren imbalanceColoring none).idxOf
        imbalanceGreyNode = 0
      omega
    simp [greyRankLetter, hrank]
  · intro q h
    cases h

def augac : Sequence 5 := ![A, U, G, A, C]

noncomputable def imbalanceSequence : Sequence 5 :=
  sequenceOfProperColoring imbalanceColoring imbalanceColoring_proper

theorem imbalanceSequence_eq_augac : imbalanceSequence = augac := by
  funext i
  fin_cases i
  · change imbalanceSequence imbalanceGreyNode.val.left = A
    simpa [imbalanceSequence] using imbalanceGreyNode_left_eq_A
  · change imbalanceSequence imbalanceGreyNode.val.right = U
    simp [imbalanceSequence, imbalanceGreyNode_left_eq_A]
  · change imbalanceSequence imbalanceBlackNode.val.left = G
    simpa [imbalanceSequence] using
      (sequenceOfProperColoring_black_left imbalanceColoring
        imbalanceColoring_proper imbalanceBlackNode imbalanceBlackNode_color)
  · change imbalanceSequence imbalanceUnpaired.val = A
    simp [imbalanceSequence]
  · change imbalanceSequence imbalanceBlackNode.val.right = C
    simpa [imbalanceSequence] using
      (sequenceOfProperColoring_black_right imbalanceColoring
        imbalanceColoring_proper imbalanceBlackNode imbalanceBlackNode_color)

def imbalanceCompetitorArc : Arc 5 := ⟨1, 3, by decide⟩

def imbalanceCompetitor : SecondaryStructure 5 where
  arcs := {imbalanceCompetitorArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem imbalanceCompetitor_compatible :
    StructureCompatible imbalanceSequence imbalanceCompetitor := by
  rw [imbalanceSequence_eq_augac]
  decide

theorem imbalance_left_prefix :
    prefixBalanceAt imbalanceSequence imbalanceCompetitorArc.left = 0 := by
  have hgrey := prefixBalanceAt_greyRight_eq imbalanceColoring
    imbalanceColoring_proper imbalanceGreyNode imbalanceGreyNode_color
  calc
    prefixBalanceAt imbalanceSequence imbalanceCompetitorArc.left =
        pairedLevel imbalanceColoring imbalanceGreyNode := by
      change prefixBalanceAt imbalanceSequence imbalanceGreyNode.val.right = _
      simpa [imbalanceSequence] using hgrey.1.trans hgrey.2
    _ = 0 := by decide

theorem imbalance_right_prefix :
    prefixBalanceAt imbalanceSequence imbalanceCompetitorArc.right = 1 := by
  calc
    prefixBalanceAt imbalanceSequence imbalanceCompetitorArc.right =
        unpairedLevel imbalanceColoring imbalanceUnpaired := by
      change prefixBalanceAt imbalanceSequence imbalanceUnpaired.val = _
      simpa [imbalanceSequence] using
        (prefixBalanceAt_unpaired_eq_unpairedLevel imbalanceColoring
          imbalanceColoring_proper imbalanceUnpaired)
    _ = 1 := by decide

theorem imbalanceCompetitor_endpoint_balances_ne :
    prefixBalanceAt imbalanceSequence imbalanceCompetitorArc.left ≠
      prefixBalanceAt imbalanceSequence imbalanceCompetitorArc.right := by
  rw [imbalance_left_prefix, imbalance_right_prefix]
  decide

theorem imbalanceCompetitor_AU_endpoints :
    (imbalanceSequence imbalanceCompetitorArc.left = A ∧
      imbalanceSequence imbalanceCompetitorArc.right = U) ∨
    (imbalanceSequence imbalanceCompetitorArc.left = U ∧
      imbalanceSequence imbalanceCompetitorArc.right = A) := by
  rw [imbalanceSequence_eq_augac]
  decide

theorem imbalanceCompetitor_explicit_unmatched_G :
    imbalanceSequence (2 : Fin 5) = G ∧
      ¬ imbalanceCompetitor.positionPaired (2 : Fin 5) := by
  rw [imbalanceSequence_eq_augac]
  decide

theorem imbalanceCompetitor_obstruction :
    ∃ k : Fin 5,
      (imbalanceSequence k = G ∨ imbalanceSequence k = C) ∧
        ¬ imbalanceCompetitor.positionPaired k := by
  exact levelImbalance_obstruction imbalanceColoring
    imbalanceColoring_proper imbalanceCompetitor
    imbalanceCompetitor_compatible imbalanceCompetitorArc (by decide)
    imbalanceCompetitor_AU_endpoints
    imbalanceCompetitor_endpoint_balances_ne

end RNA.Milestone4Examples
