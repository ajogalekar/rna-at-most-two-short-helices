module

public import RNA.GlobalColoring
public import RNA.Examples

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# Kernel-checked Milestone 3 construction examples

This file fixes the five concrete targets, checks their class-K membership,
endpoint shapes, selected local rows, and short-child policies, and then
instantiates the global proof-bearing coloring on each target.
-/

namespace RNA.Milestone3Examples

open RNA
open Color

theorem certificate_strongTwoSeparated
    {n : Nat} {T : SecondaryStructure n} {hK : InTargetClassK T}
    (C : GlobalColoringCertificate T hK) :
    StrongTwoSeparated C.coloring :=
  (strongTwoSeparated_iff_exists_with C.coloring).2
    ⟨C.allocation.row.xi, C.strong⟩

/-! ## Smallest target `(())` -/

abbrev smallestTarget : SecondaryStructure 4 := Examples.nestedTarget

theorem smallestTarget_in_classK : InTargetClassK smallestTarget :=
  Examples.nestedTarget_in_classK

theorem smallestTarget_shortHelix_length :
    (shortHelix smallestTarget smallestTarget_in_classK).length = 2 :=
  shortHelix_length smallestTarget smallestTarget_in_classK

def smallestTransfer : LocalTransfer 2 0 1 0 Color.black :=
  twoPairTransferOfSafe 0 1 0 0 Color.black (by decide) (by decide)

theorem smallestTransfer_colors :
    smallestTransfer.colors = [Color.black, Color.black] := by
  rfl

theorem smallestTransfer_validBridge :
    ValidTwoPair 0 1 0 (Color.black, Color.black) := by
  decide

theorem smallestTransfer_internallyProper :
    InternallyProper smallestTransfer.colors :=
  smallestTransfer.internallyProper

noncomputable def smallestCertificate :
    GlobalColoringCertificate smallestTarget smallestTarget_in_classK :=
  globalColoringCertificate smallestTarget_in_classK

theorem smallestCertificate_proper :
    ProperColoring smallestCertificate.coloring :=
  smallestCertificate.proper

theorem smallestCertificate_strong :
    StrongTwoSeparated smallestCertificate.coloring :=
  certificate_strongTwoSeparated smallestCertificate

/-! ## Root-unpaired target `.(())` -/

def rootUnpairedOuter : Arc 5 :=
  ⟨1, 4, by decide⟩

def rootUnpairedInner : Arc 5 :=
  ⟨2, 3, by decide⟩

def rootUnpairedTarget : SecondaryStructure 5 where
  arcs := {rootUnpairedOuter, rootUnpairedInner}
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem rootUnpairedTarget_in_classK : InTargetClassK rootUnpairedTarget := by
  decide

def rootUnpairedPosition : UnpairedPosition rootUnpairedTarget :=
  ⟨0, by decide⟩

theorem rootUnpairedPosition_is_rootChild :
    rootUnpairedPosition ∈ unpairedChildren rootUnpairedTarget none := by
  decide

theorem rootUnpaired_pairedChildCount :
    pairedChildCount rootUnpairedTarget none = 1 := by
  decide

noncomputable def rootUnpairedAllocation :
    RootAllocation rootUnpairedTarget rootUnpairedTarget_in_classK :=
  xiRootAllocation rootUnpairedTarget_in_classK .xiOne (Or.inl rfl)
    rootUnpaired_pairedChildCount

@[simp] theorem rootUnpairedAllocation_row :
    rootUnpairedAllocation.row = .xiOne := by
  rfl

theorem rootUnpairedAllocation_xi_zero :
    rootUnpairedAllocation.row.xi = 0 := by
  rw [rootUnpairedAllocation_row]
  rfl

theorem rootUnpaired_level_zero (χ : Coloring rootUnpairedTarget) :
    unpairedLevel χ rootUnpairedPosition = 0 :=
  unpairedLevel_of_mem_rootChildren χ rootUnpairedPosition_is_rootChild

theorem rootUnpaired_residue_eq_xi (χ : Coloring rootUnpairedTarget) :
    levelParity (unpairedLevel χ rootUnpairedPosition) =
      rootUnpairedAllocation.row.xi := by
  rw [rootUnpaired_level_zero, rootUnpairedAllocation_xi_zero]
  rfl

theorem rootUnpairedAllocation_proper :
    ProperExposure (rootPortExposure rootUnpairedAllocation.ports) :=
  rootUnpairedAllocation.proper

noncomputable def rootUnpairedCertificate :
    GlobalColoringCertificate rootUnpairedTarget
      rootUnpairedTarget_in_classK :=
  globalColoringCertificate rootUnpairedTarget_in_classK

theorem rootUnpairedCertificate_proper :
    ProperColoring rootUnpairedCertificate.coloring :=
  rootUnpairedCertificate.proper

theorem rootUnpairedCertificate_strong :
    StrongTwoSeparated rootUnpairedCertificate.coloring :=
  certificate_strongTwoSeparated rootUnpairedCertificate

theorem rootUnpairedCertificate_row :
    rootUnpairedCertificate.allocation.row = .xiOne := by
  have hu : HasUnpairedChild rootUnpairedTarget none :=
    ⟨rootUnpairedPosition, rootUnpairedPosition_is_rootChild⟩
  rcases rootUnpairedCertificate.unpairedRow hu with hrow | hrow
  · exact hrow
  · have hcount := rootUnpairedCertificate.allocation.count_eq
    rw [hrow, rootUnpaired_pairedChildCount] at hcount
    simp [RootRow.count] at hcount

theorem rootUnpairedCertificate_xi_zero :
    rootUnpairedCertificate.allocation.row.xi = 0 := by
  rw [rootUnpairedCertificate_row]
  rfl

theorem rootUnpairedCertificate_unpairedResidue :
    levelParity
        (unpairedLevel rootUnpairedCertificate.coloring rootUnpairedPosition) =
      rootUnpairedCertificate.allocation.row.xi :=
  rootUnpairedCertificate.strong.1 rootUnpairedPosition

/-! ## Eta-root target `(())((()))((()))` -/

def etaRootShortOuter : Arc 16 := ⟨0, 3, by decide⟩
def etaRootShortInner : Arc 16 := ⟨1, 2, by decide⟩
def etaRootLongOneOuter : Arc 16 := ⟨4, 9, by decide⟩
def etaRootLongOneMiddle : Arc 16 := ⟨5, 8, by decide⟩
def etaRootLongOneInner : Arc 16 := ⟨6, 7, by decide⟩
def etaRootLongTwoOuter : Arc 16 := ⟨10, 15, by decide⟩
def etaRootLongTwoMiddle : Arc 16 := ⟨11, 14, by decide⟩
def etaRootLongTwoInner : Arc 16 := ⟨12, 13, by decide⟩

def etaRootTarget : SecondaryStructure 16 where
  arcs := {etaRootShortOuter, etaRootShortInner,
    etaRootLongOneOuter, etaRootLongOneMiddle, etaRootLongOneInner,
    etaRootLongTwoOuter, etaRootLongTwoMiddle, etaRootLongTwoInner}
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem etaRootTarget_in_classK : InTargetClassK etaRootTarget := by
  decide

theorem etaRoot_pairedChildCount :
    pairedChildCount etaRootTarget none = 3 := by
  decide

theorem etaRoot_no_unpairedChild :
    ¬ HasUnpairedChild etaRootTarget none := by
  decide

def etaRootExplicitShortHelix : MaximalHelix etaRootTarget :=
  ⟨(etaRootShortOuter, ⟨2, by decide⟩), by decide⟩

theorem etaRootExplicitShortHelix_length :
    etaRootExplicitShortHelix.length = 2 := by
  rfl

theorem etaRootExplicitShortHelix_eq_shortHelix :
    etaRootExplicitShortHelix =
      shortHelix etaRootTarget etaRootTarget_in_classK :=
  eq_shortHelix_of_length_two etaRootTarget etaRootTarget_in_classK
    etaRootExplicitShortHelix etaRootExplicitShortHelix_length

theorem etaRootExplicitShortHead_is_rootChild :
    etaRootExplicitShortHelix.headNode ∈
      pairedChildren etaRootTarget none := by
  decide

theorem etaRootCanonicalShortHead_is_rootChild :
    (shortHelix etaRootTarget etaRootTarget_in_classK).headNode ∈
      pairedChildren etaRootTarget none := by
  rw [← etaRootExplicitShortHelix_eq_shortHelix]
  exact etaRootExplicitShortHead_is_rootChild

noncomputable def etaRootAllocationExample :
    RootAllocation etaRootTarget etaRootTarget_in_classK :=
  etaRootAllocation etaRootTarget_in_classK .three etaRoot_pairedChildCount

@[simp] theorem etaRootAllocationExample_row :
    etaRootAllocationExample.row = .etaThree := by
  simpa [etaRootAllocationExample, EtaRootRow.toRootRow] using
    etaRootAllocation_row etaRootTarget_in_classK .three
      etaRoot_pairedChildCount

theorem etaRootAllocationExample_entry_eq_eta :
    etaRootAllocationExample.row.entry =
      etaRootAllocationExample.row.eta := by
  rw [etaRootAllocationExample_row]
  decide

noncomputable def etaRootShortIndex :
    Fin (pairedChildCount etaRootTarget none) :=
  pairedChildIndex etaRootTarget none
    (shortHelix etaRootTarget etaRootTarget_in_classK).headNode
    etaRootCanonicalShortHead_is_rootChild

theorem etaRoot_short_receives_grey :
    etaRootAllocationExample.ports etaRootShortIndex = Color.grey := by
  exact etaRootAllocationExample.shortGreyAtEta
    etaRootCanonicalShortHead_is_rootChild
    etaRootAllocationExample_entry_eq_eta

theorem etaRootAllocationExample_proper :
    ProperExposure (rootPortExposure etaRootAllocationExample.ports) :=
  etaRootAllocationExample.proper

theorem etaRootAllocationExample_all_safe :
    ∀ i, Safe (outgoingHelixAtRootSlot etaRootTarget i).length
      etaRootAllocationExample.row.entry etaRootAllocationExample.row.eta
      (etaRootAllocationExample.ports i) :=
  etaRootAllocationExample.safeOutgoing

noncomputable def etaRootCertificate :
    GlobalColoringCertificate etaRootTarget etaRootTarget_in_classK :=
  globalColoringCertificate etaRootTarget_in_classK

theorem etaRootCertificate_proper :
    ProperColoring etaRootCertificate.coloring :=
  etaRootCertificate.proper

theorem etaRootCertificate_strong :
    StrongTwoSeparated etaRootCertificate.coloring :=
  certificate_strongTwoSeparated etaRootCertificate

theorem etaRootCertificate_row :
    etaRootCertificate.allocation.row = .etaThree := by
  have hlarge : ¬ HasUnpairedChild etaRootTarget none ∧
      3 ≤ pairedChildCount etaRootTarget none :=
    ⟨etaRoot_no_unpairedChild, by rw [etaRoot_pairedChildCount]⟩
  rcases etaRootCertificate.largeRow hlarge with hrow | hrow
  · exact hrow
  · have hcount := etaRootCertificate.allocation.count_eq
    rw [hrow, etaRoot_pairedChildCount] at hcount
    simp [RootRow.count] at hcount

theorem etaRootCertificate_entry_eq_eta :
    etaRootCertificate.allocation.row.entry =
      etaRootCertificate.allocation.row.eta := by
  rw [etaRootCertificate_row]
  decide

noncomputable def etaRootCertificateShortIndex :
    Fin (pairedChildCount etaRootTarget none) :=
  pairedChildIndex etaRootTarget none
    (shortHelix etaRootTarget etaRootTarget_in_classK).headNode
    etaRootCanonicalShortHead_is_rootChild

theorem etaRootCertificate_short_receives_grey :
    etaRootCertificate.allocation.ports etaRootCertificateShortIndex =
      Color.grey :=
  etaRootCertificate.allocation.shortGreyAtEta
    etaRootCanonicalShortHead_is_rootChild etaRootCertificate_entry_eq_eta

theorem etaRootCertificate_shortHead_grey :
    etaRootCertificate.coloring
        (shortHelix etaRootTarget etaRootTarget_in_classK).headNode =
      Color.grey := by
  rw [etaRootCertificate.coloring_eq]
  have hcolor := assembledRootColoring_childPortsInstalled
    etaRootTarget_in_classK etaRootCertificate.allocation
      etaRootCertificateShortIndex
  unfold etaRootCertificateShortIndex at hcolor
  rw [orderedPairedChild_pairedChildIndex] at hcolor
  exact hcolor.trans etaRootCertificate_short_receives_grey

/-! ## Internal M-to-L short helix

The balanced target `(((((.))((())))))` realizes the requested shape: a
length-three incoming helix ends at M and has a length-two L child plus a
length-three child.
-/

def internalIncomingOuter : Arc 17 := ⟨0, 16, by decide⟩
def internalIncomingMiddle : Arc 17 := ⟨1, 15, by decide⟩
def internalIncomingTerminal : Arc 17 := ⟨2, 14, by decide⟩
def internalShortOuter : Arc 17 := ⟨3, 7, by decide⟩
def internalShortTerminal : Arc 17 := ⟨4, 6, by decide⟩
def internalLongOuter : Arc 17 := ⟨8, 13, by decide⟩
def internalLongMiddle : Arc 17 := ⟨9, 12, by decide⟩
def internalLongTerminal : Arc 17 := ⟨10, 11, by decide⟩

def internalMToLTarget : SecondaryStructure 17 where
  arcs := {internalIncomingOuter, internalIncomingMiddle,
    internalIncomingTerminal, internalShortOuter, internalShortTerminal,
    internalLongOuter, internalLongMiddle, internalLongTerminal}
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem internalMToLTarget_in_classK : InTargetClassK internalMToLTarget := by
  decide

def internalMNode : PairedNode internalMToLTarget :=
  ⟨internalIncomingTerminal, by decide⟩

def internalShortHeadNode : PairedNode internalMToLTarget :=
  ⟨internalShortOuter, by decide⟩

def internalShortTerminalNode : PairedNode internalMToLTarget :=
  ⟨internalShortTerminal, by decide⟩

theorem internalMNode_is_M : IsMEndpoint internalMNode := by
  decide

theorem internalMNode_is_loop : IsLoopNode internalMNode :=
  isLoopNode_of_endpointType internalMNode .M internalMNode_is_M

theorem internalShortTerminalNode_is_L :
    IsLEndpoint internalShortTerminalNode := by
  decide

theorem internalShortHead_enters_from_M :
    internalShortHeadNode ∈
      pairedChildren internalMToLTarget (some internalMNode) := by
  decide

def internalExplicitShortHelix : MaximalHelix internalMToLTarget :=
  ⟨(internalShortOuter, ⟨2, by decide⟩), by decide⟩

theorem internalExplicitShortHelix_length :
    internalExplicitShortHelix.length = 2 := by
  rfl

theorem internalExplicitShortHelix_eq_shortHelix :
    internalExplicitShortHelix =
      shortHelix internalMToLTarget internalMToLTarget_in_classK :=
  eq_shortHelix_of_length_two internalMToLTarget internalMToLTarget_in_classK
    internalExplicitShortHelix internalExplicitShortHelix_length

theorem internalExplicitShortHelix_head :
    internalExplicitShortHelix.headNode = internalShortHeadNode := by
  rfl

def internalExplicitIncomingHelix : MaximalHelix internalMToLTarget :=
  ⟨(internalIncomingOuter, ⟨3, by decide⟩), by decide⟩

theorem internalExplicitIncomingHelix_terminal :
    internalExplicitIncomingHelix.terminalNode = internalMNode := by
  apply Subtype.ext
  apply Arc.stackOffset_arc_unique
    internalExplicitIncomingHelix.terminalPair_stackOffset
  decide

theorem internalRoot_pairedChildCount :
    pairedChildCount internalMToLTarget none = 1 := by
  decide

def internalRootIndex : Fin (pairedChildCount internalMToLTarget none) :=
  ⟨0, by rw [internalRoot_pairedChildCount]; decide⟩

theorem internalExplicitIncomingHead_is_rootChild :
    internalExplicitIncomingHelix.headNode ∈
      pairedChildren internalMToLTarget none := by
  decide

theorem internalRootOutgoing_eq_explicitIncoming :
    outgoingHelixAtRootSlot internalMToLTarget internalRootIndex =
      internalExplicitIncomingHelix := by
  apply MaximalHelix.ext_outer
  have hout := outgoingHelixAtRootSlot_head internalMToLTarget internalRootIndex
  have hexplicit : internalExplicitIncomingHelix.headNode =
      orderedPairedChild internalMToLTarget none internalRootIndex := by
    have hone : pairedChildCount internalMToLTarget none = 1 :=
      internalRoot_pairedChildCount
    have hindex : internalRootIndex =
        pairedChildIndex internalMToLTarget none
          internalExplicitIncomingHelix.headNode
          internalExplicitIncomingHead_is_rootChild := by
      apply (finCongr internalRoot_pairedChildCount).injective
      apply Subsingleton.elim
    rw [hindex, orderedPairedChild_pairedChildIndex]
  exact congrArg Subtype.val (hout.trans hexplicit.symm)

theorem internalRootOutgoing_terminal :
    (outgoingHelixAtRootSlot internalMToLTarget
      internalRootIndex).terminalNode = internalMNode := by
  rw [internalRootOutgoing_eq_explicitIncoming]
  exact internalExplicitIncomingHelix_terminal

theorem internalCanonicalShortHead_enters_from_M :
    (shortHelix internalMToLTarget internalMToLTarget_in_classK).headNode ∈
      pairedChildren internalMToLTarget (some internalMNode) := by
  rw [← internalExplicitShortHelix_eq_shortHelix,
    internalExplicitShortHelix_head]
  exact internalShortHead_enters_from_M

noncomputable def internalMAllocation :
    LoopAllocation internalMToLTarget internalMToLTarget_in_classK
      internalMNode .M Color.grey 0 :=
  completeLoopAllocationCoverage internalMToLTarget_in_classK
    internalMNode internalMNode_is_loop .M internalMNode_is_M
    Color.grey 0 (by simp)

@[simp] theorem internalMAllocation_entry :
    internalMAllocation.entry = (0 : Parity).opposite :=
  internalMAllocation.mEntry rfl

noncomputable def internalShortChildIndex :
    Fin (pairedChildCount internalMToLTarget (some internalMNode)) :=
  pairedChildIndex internalMToLTarget (some internalMNode)
    (shortHelix internalMToLTarget internalMToLTarget_in_classK).headNode
    internalCanonicalShortHead_enters_from_M

theorem internal_short_child_receives_grey :
    internalMAllocation.ports internalShortChildIndex = Color.grey :=
  internalMAllocation.shortGreyAtM rfl
    internalCanonicalShortHead_enters_from_M

theorem internalMAllocation_proper :
    ProperExposure
      (loopPortExposure Color.grey internalMAllocation.ports) :=
  internalMAllocation.proper

theorem internalMAllocation_all_safe :
    ∀ i, Safe
      (outgoingHelixAtLoopSlot internalMToLTarget internalMNode
        internalMNode_is_loop i).length
      internalMAllocation.entry (0 : Parity).opposite
      (internalMAllocation.ports i) :=
  internalMAllocation.safeOutgoing internalMNode_is_loop internalMNode_is_M

def internalShortTransfer : LocalTransfer 2 1 1 0 Color.grey :=
  twoPairTransferOfSafe 0 1 1 0 Color.grey (by decide) (by decide)

theorem internalShortTransfer_starts_grey :
    internalShortTransfer.colors.head? = some Color.grey :=
  internalShortTransfer.first_eq

theorem internalShortTransfer_colors :
    internalShortTransfer.colors = [Color.grey, Color.black] := by
  rfl

noncomputable def internalMToLCertificate :
    GlobalColoringCertificate internalMToLTarget
      internalMToLTarget_in_classK :=
  globalColoringCertificate internalMToLTarget_in_classK

theorem internalMToLCertificate_proper :
    ProperColoring internalMToLCertificate.coloring :=
  internalMToLCertificate.proper

theorem internalMToLCertificate_strong :
    StrongTwoSeparated internalMToLCertificate.coloring :=
  certificate_strongTwoSeparated internalMToLCertificate

theorem internalMToLCertificate_shortHead_grey :
    internalMToLCertificate.coloring internalShortHeadNode = Color.grey := by
  rw [internalMToLCertificate.coloring_eq]
  let H := outgoingHelixAtRootSlot internalMToLTarget internalRootIndex
  let cert := constructedRootSubtreeCertificate
    internalMToLTarget_in_classK internalMToLCertificate.allocation
      internalRootIndex
  have hpost := assembledRootSubtreePostcondition
    internalMToLTarget_in_classK internalMToLCertificate.allocation
      internalRootIndex
  have hterminal : H.terminalNode = internalMNode := by
    simpa [H] using internalRootOutgoing_terminal
  have hM : HasEndpointType H.terminalNode .M := by
    rw [hterminal]
    exact internalMNode_is_M
  have hendpoint : cert.endpoint = .M :=
    endpointType_unique H.terminalNode cert.endpoint_spec hM
  have hshort :
      (shortHelix internalMToLTarget
        internalMToLTarget_in_classK).headNode ∈
        pairedChildren internalMToLTarget (some H.terminalNode) := by
    rw [hterminal]
    exact internalCanonicalShortHead_enters_from_M
  let j := pairedChildIndex internalMToLTarget (some H.terminalNode)
    (shortHelix internalMToLTarget
      internalMToLTarget_in_classK).headNode hshort
  have hport : cert.allocation.ports j = Color.grey :=
    cert.allocation.shortGreyAtM hendpoint hshort
  have hcolor := hpost.childPorts j
  rw [orderedPairedChild_pairedChildIndex] at hcolor
  have hhead :
      (shortHelix internalMToLTarget
        internalMToLTarget_in_classK).headNode = internalShortHeadNode := by
    rw [← internalExplicitShortHelix_eq_shortHelix,
      internalExplicitShortHelix_head]
  simpa [H, cert, j, hhead] using hcolor.trans hport

/-! ## Deeper recursive target

The target has two nested M branch points.  Its unique short helix lies below
the second M; its terminal is L, while both other branch leaves are E.
-/

def deepTopOuter : Arc 29 := ⟨0, 28, by decide⟩
def deepTopMiddle : Arc 29 := ⟨1, 27, by decide⟩
def deepTopTerminal : Arc 29 := ⟨2, 26, by decide⟩
def deepSecondOuter : Arc 29 := ⟨3, 19, by decide⟩
def deepSecondMiddle : Arc 29 := ⟨4, 18, by decide⟩
def deepSecondTerminal : Arc 29 := ⟨5, 17, by decide⟩
def deepShortOuter : Arc 29 := ⟨6, 10, by decide⟩
def deepShortTerminal : Arc 29 := ⟨7, 9, by decide⟩
def deepInnerEOuter : Arc 29 := ⟨11, 16, by decide⟩
def deepInnerEMiddle : Arc 29 := ⟨12, 15, by decide⟩
def deepInnerETerminal : Arc 29 := ⟨13, 14, by decide⟩
def deepOuterEOuter : Arc 29 := ⟨20, 25, by decide⟩
def deepOuterEMiddle : Arc 29 := ⟨21, 24, by decide⟩
def deepOuterETerminal : Arc 29 := ⟨22, 23, by decide⟩

def deeperRecursiveTarget : SecondaryStructure 29 where
  arcs := {deepTopOuter, deepTopMiddle, deepTopTerminal,
    deepSecondOuter, deepSecondMiddle, deepSecondTerminal,
    deepShortOuter, deepShortTerminal,
    deepInnerEOuter, deepInnerEMiddle, deepInnerETerminal,
    deepOuterEOuter, deepOuterEMiddle, deepOuterETerminal}
  isPartialMatching := by decide
  isNoncrossing := by decide

set_option maxHeartbeats 1000000 in
-- The kernel decision procedure exhausts the finite maximal-helix candidates
-- of this 29-position example.
theorem deeperRecursiveTarget_in_classK :
    InTargetClassK deeperRecursiveTarget := by
  decide

def deepTopMNode : PairedNode deeperRecursiveTarget :=
  ⟨deepTopTerminal, by decide⟩

def deepSecondMNode : PairedNode deeperRecursiveTarget :=
  ⟨deepSecondTerminal, by decide⟩

def deepShortHeadNode : PairedNode deeperRecursiveTarget :=
  ⟨deepShortOuter, by decide⟩

def deepShortLNode : PairedNode deeperRecursiveTarget :=
  ⟨deepShortTerminal, by decide⟩

def deepInnerENode : PairedNode deeperRecursiveTarget :=
  ⟨deepInnerETerminal, by decide⟩

def deepOuterENode : PairedNode deeperRecursiveTarget :=
  ⟨deepOuterETerminal, by decide⟩

theorem deepTopMNode_is_M : IsMEndpoint deepTopMNode := by
  decide

theorem deepSecondMNode_is_M : IsMEndpoint deepSecondMNode := by
  decide

theorem deepShortLNode_is_L : IsLEndpoint deepShortLNode := by
  decide

theorem deepInnerENode_is_E : IsEEndpoint deepInnerENode := by
  decide

theorem deepOuterENode_is_E : IsEEndpoint deepOuterENode := by
  decide

theorem deepSecondMNode_is_loop : IsLoopNode deepSecondMNode :=
  isLoopNode_of_endpointType deepSecondMNode .M deepSecondMNode_is_M

theorem deepShortHead_enters_from_second_M :
    deepShortHeadNode ∈
      pairedChildren deeperRecursiveTarget (some deepSecondMNode) := by
  decide

theorem deepSecondMHead_enters_from_top_M :
    (⟨deepSecondOuter, by decide⟩ : PairedNode deeperRecursiveTarget) ∈
      pairedChildren deeperRecursiveTarget (some deepTopMNode) := by
  decide

def deepExplicitShortHelix : MaximalHelix deeperRecursiveTarget :=
  ⟨(deepShortOuter, ⟨2, by decide⟩), by decide⟩

theorem deepExplicitShortHelix_length :
    deepExplicitShortHelix.length = 2 := by
  rfl

theorem deepExplicitShortHelix_eq_shortHelix :
    deepExplicitShortHelix =
      shortHelix deeperRecursiveTarget deeperRecursiveTarget_in_classK :=
  eq_shortHelix_of_length_two deeperRecursiveTarget
    deeperRecursiveTarget_in_classK deepExplicitShortHelix
    deepExplicitShortHelix_length

theorem deepExplicitShortHelix_head :
    deepExplicitShortHelix.headNode = deepShortHeadNode := by
  rfl

theorem deepCanonicalShortHead_enters_from_second_M :
    (shortHelix deeperRecursiveTarget
      deeperRecursiveTarget_in_classK).headNode ∈
      pairedChildren deeperRecursiveTarget (some deepSecondMNode) := by
  rw [← deepExplicitShortHelix_eq_shortHelix,
    deepExplicitShortHelix_head]
  exact deepShortHead_enters_from_second_M

noncomputable def deepSecondMAllocation :
    LoopAllocation deeperRecursiveTarget deeperRecursiveTarget_in_classK
      deepSecondMNode .M Color.grey 0 :=
  completeLoopAllocationCoverage deeperRecursiveTarget_in_classK
    deepSecondMNode deepSecondMNode_is_loop .M deepSecondMNode_is_M
    Color.grey 0 (by simp)

noncomputable def deepShortChildIndex :
    Fin (pairedChildCount deeperRecursiveTarget (some deepSecondMNode)) :=
  pairedChildIndex deeperRecursiveTarget (some deepSecondMNode)
    (shortHelix deeperRecursiveTarget
      deeperRecursiveTarget_in_classK).headNode
    deepCanonicalShortHead_enters_from_second_M

theorem deep_short_child_receives_grey :
    deepSecondMAllocation.ports deepShortChildIndex = Color.grey :=
  deepSecondMAllocation.shortGreyAtM rfl
    deepCanonicalShortHead_enters_from_second_M

theorem deepSecondMAllocation_proper :
    ProperExposure
      (loopPortExposure Color.grey deepSecondMAllocation.ports) :=
  deepSecondMAllocation.proper

theorem deepSecondMAllocation_all_safe :
    ∀ i, Safe
      (outgoingHelixAtLoopSlot deeperRecursiveTarget deepSecondMNode
        deepSecondMNode_is_loop i).length
      deepSecondMAllocation.entry (0 : Parity).opposite
      (deepSecondMAllocation.ports i) :=
  deepSecondMAllocation.safeOutgoing deepSecondMNode_is_loop
    deepSecondMNode_is_M

noncomputable def deeperRecursiveCertificate :
    GlobalColoringCertificate deeperRecursiveTarget
      deeperRecursiveTarget_in_classK :=
  globalColoringCertificate deeperRecursiveTarget_in_classK

theorem deeperRecursiveCertificate_proper :
    ProperColoring deeperRecursiveCertificate.coloring :=
  deeperRecursiveCertificate.proper

theorem deeperRecursiveCertificate_strong :
    StrongTwoSeparated deeperRecursiveCertificate.coloring :=
  certificate_strongTwoSeparated deeperRecursiveCertificate

theorem deeperRecursiveTarget_globalTheorem :
    ∃ χ : Coloring deeperRecursiveTarget,
      ProperColoring χ ∧ StrongTwoSeparated χ :=
  targetClass_admits_proper_strongTwoSeparated
    deeperRecursiveTarget_in_classK

end RNA.Milestone3Examples
