module

public import RNA.Coloring
public import RNA.Examples
public import RNA.HelixPartition
public import RNA.Endpoint
public import RNA.HelixTransfer
public import RNA.LocalAllocations

@[expose] public section

set_option autoImplicit false

/-!
# Kernel-checked local-colouring examples for Milestone 2

Further endpoint, allocation, and transfer examples are added here by the
modules that introduce those notions.  These first examples exercise the
three-colour algebra and the distinction between ordinary and strong
separation on an actual interval tree.
-/

namespace RNA.Milestone2Examples

open Color

example : Color.inv (Color.inv Color.black) = Color.black := by decide
example : Color.inv (Color.inv Color.white) = Color.white := by decide
example : Color.inv (Color.inv Color.grey) = Color.grey := by decide

example : Color.delta (Color.inv Color.black) = -Color.delta Color.black := by decide
example : Color.delta (Color.inv Color.white) = -Color.delta Color.white := by decide
example : Color.delta (Color.inv Color.grey) = -Color.delta Color.grey := by decide

example : ProperExposure {Color.black, Color.white, Color.grey, Color.grey} := by decide
example : ¬ ProperExposure {Color.black, Color.black} := by decide
example : ¬ ProperExposure {Color.white, Color.white} := by decide
example : ¬ ProperExposure {Color.grey, Color.grey, Color.grey} := by decide

example : ¬ ProperAdjacent Color.black Color.white := by decide
example : ¬ ProperAdjacent Color.white Color.black := by decide
example : ProperAdjacent Color.black Color.black := by decide
example : ProperAdjacent Color.black Color.grey := by decide
example : ProperAdjacent Color.grey Color.black := by decide
example : ProperAdjacent Color.grey Color.grey := by decide

/-! A black pair encloses one unpaired position and leaves another unpaired
position at the root.  There are no grey pairs, so ordinary separation is
vacuous, while the two unpaired positions have opposite parity and therefore
cannot satisfy strong two-separation. -/

def mixedParityArc : Arc 4 where
  left := 0
  right := 2
  ordered := by decide

def mixedParityTarget : SecondaryStructure 4 where
  arcs := {mixedParityArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

def mixedParityColoring : Coloring mixedParityTarget :=
  fun _ => Color.black

theorem mixedParityColoring_proper : ProperColoring mixedParityColoring := by
  decide

theorem separation_vacuous_without_grey :
    Separated mixedParityColoring := by
  decide

theorem strong_separation_not_vacuous_without_grey :
    ¬ StrongTwoSeparated mixedParityColoring := by
  decide

example (χ : Coloring mixedParityTarget) :
    StrongTwoSeparated χ → Separated χ :=
  strongTwoSeparated_implies_separated χ

/-! ## Canonical maximal-helix lookup -/

theorem outerArc_in_its_canonical_maximalHelix :
    Examples.outerArc ∈ helixMembers Examples.nestedTarget
      (maximalHelixContaining Examples.nestedTarget Examples.outerArc (by decide)) := by
  exact mem_maximalHelixContaining _ _ _

theorem nestedTarget_unique_shortHelix_length :
    (shortHelix Examples.nestedTarget Examples.nestedTarget_in_classK).length = 2 := by
  exact shortHelix_length _ _

/-! ## Checked endpoint shapes on actual interval trees -/

def eArc : Arc 2 where
  left := 0
  right := 1
  ordered := by decide

def eTarget : SecondaryStructure 2 where
  arcs := {eArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

def eNode : PairedNode eTarget := ⟨eArc, by decide⟩

theorem eNode_is_E : IsEEndpoint eNode := by decide

def lZeroArc : Arc 3 where
  left := 0
  right := 2
  ordered := by decide

def lZeroTarget : SecondaryStructure 3 where
  arcs := {lZeroArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

def lZeroNode : PairedNode lZeroTarget := ⟨lZeroArc, by decide⟩

theorem lZeroNode_is_L : IsLEndpoint lZeroNode := by decide

def lOneOuter : Arc 6 where
  left := 0
  right := 5
  ordered := by decide

def lOneChild : Arc 6 where
  left := 2
  right := 4
  ordered := by decide

def lOneTarget : SecondaryStructure 6 where
  arcs := {lOneOuter, lOneChild}
  isPartialMatching := by decide
  isNoncrossing := by decide

def lOneNode : PairedNode lOneTarget := ⟨lOneOuter, by decide⟩

theorem lOneNode_is_L : IsLEndpoint lOneNode := by decide

def mTwoOuter : Arc 6 where
  left := 0
  right := 5
  ordered := by decide

def mTwoLeft : Arc 6 where
  left := 1
  right := 2
  ordered := by decide

def mTwoRight : Arc 6 where
  left := 3
  right := 4
  ordered := by decide

def mTwoTarget : SecondaryStructure 6 where
  arcs := {mTwoOuter, mTwoLeft, mTwoRight}
  isPartialMatching := by decide
  isNoncrossing := by decide

def mTwoNode : PairedNode mTwoTarget := ⟨mTwoOuter, by decide⟩

theorem mTwoNode_is_M : IsMEndpoint mTwoNode := by decide

def mThreeOuter : Arc 8 where
  left := 0
  right := 7
  ordered := by decide

def mThreeLeft : Arc 8 where
  left := 1
  right := 2
  ordered := by decide

def mThreeMiddle : Arc 8 where
  left := 3
  right := 4
  ordered := by decide

def mThreeRight : Arc 8 where
  left := 5
  right := 6
  ordered := by decide

def mThreeTarget : SecondaryStructure 8 where
  arcs := {mThreeOuter, mThreeLeft, mThreeMiddle, mThreeRight}
  isPartialMatching := by decide
  isNoncrossing := by decide

def mThreeNode : PairedNode mThreeTarget := ⟨mThreeOuter, by decide⟩

theorem mThreeNode_is_M : IsMEndpoint mThreeNode := by decide

example : IsLoopNode eNode :=
  isLoopNode_of_endpointType eNode .E eNode_is_E

example : IsLoopNode lZeroNode :=
  isLoopNode_of_endpointType lZeroNode .L lZeroNode_is_L

example : IsLoopNode lOneNode :=
  isLoopNode_of_endpointType lOneNode .L lOneNode_is_L

example : IsLoopNode mTwoNode :=
  isLoopNode_of_endpointType mTwoNode .M mTwoNode_is_M

example : IsLoopNode mThreeNode :=
  isLoopNode_of_endpointType mThreeNode .M mThreeNode_is_M

/-! ## Exact two-pair rows and rejected alternatives -/

example : ValidTwoPair 0 1 0 (Color.black, Color.black) := by decide
example : ValidTwoPair 0 1 1 (Color.black, Color.grey) := by decide
example : ValidTwoPair 1 1 0 (Color.grey, Color.black) := by decide
example : ValidTwoPair 1 1 1 (Color.grey, Color.grey) := by decide

example : ¬ ValidTwoPair 0 1 0 (Color.black, Color.grey) := by decide
example : ¬ ValidTwoPair 0 1 1 (Color.black, Color.black) := by decide
example : ¬ ValidTwoPair 1 1 0 (Color.black, Color.black) := by decide
example : ¬ ValidTwoPair 1 1 1 (Color.black, Color.grey) := by decide

example :
    Finset.univ.filter (ValidTwoPair 0 1 0) =
      {(Color.black, Color.black), (Color.white, Color.white)} := by
  simpa [twoPairTable] using validTwoPairFinset_eq_table 0 1 0 0 (by decide)

example :
    Finset.univ.filter (ValidTwoPair 0 1 1) =
      {(Color.black, Color.grey), (Color.white, Color.grey)} := by
  simpa [twoPairTable] using validTwoPairFinset_eq_table 0 1 0 1 (by decide)

example :
    Finset.univ.filter (ValidTwoPair 1 1 0) =
      {(Color.grey, Color.black), (Color.grey, Color.white)} := by
  simpa [twoPairTable] using validTwoPairFinset_eq_table 0 1 1 0 (by decide)

example :
    Finset.univ.filter (ValidTwoPair 1 1 1) =
      {(Color.black, Color.black), (Color.white, Color.white),
        (Color.grey, Color.grey)} := by
  simpa [twoPairTable] using validTwoPairFinset_eq_table 0 1 1 1 (by decide)

/-! ## Long transfer at the first two permitted lengths -/

example : Nonempty (LocalTransfer 3 0 1 0 Color.black) := by
  exact exists_longHelixTransfer 3 0 1 0 Color.black (by omega) (by decide)

example : Nonempty (LocalTransfer 4 1 1 0 Color.grey) := by
  exact exists_longHelixTransfer 4 1 1 0 Color.grey (by omega) (by decide)

/-! ## Every displayed root and M-allocation row -/

example : ProperExposure
    (rootPortExposure RootRow.xiOne.ports) := RootRow.proper .xiOne
example : ProperExposure
    (rootPortExposure RootRow.xiTwo.ports) := RootRow.proper .xiTwo
example : ProperExposure
    (rootPortExposure RootRow.etaThree.ports) := RootRow.proper .etaThree
example : ProperExposure
    (rootPortExposure RootRow.etaFour.ports) := RootRow.proper .etaFour

example (a : Color) (d : MArity) :
    ProperExposure (loopPortExposure a (ordinaryMPorts a d)) :=
  ordinaryMExposure_proper a d

example (a : Color) (d : MArity) (short : Fin d.count) :
    ProperExposure (loopPortExposure a (designatedMPortsAt a d short)) :=
  designatedMExposure_proper a d short

example (short : Fin MArity.two.count) :
    loopPortExposure Color.grey
        (designatedMPortsAt Color.grey .two short) =
      ({Color.grey, Color.grey, Color.black} : Multiset Color) :=
  designatedM_tight_exposure short

example : ProperExposure (loopPortExposure Color.grey noPorts) :=
  eExposure_proper Color.grey

example : ProperExposure (loopPortExposure Color.black noPorts) :=
  lZeroExposure_proper Color.black Color.black_nonGrey

example : ProperExposure
    (loopPortExposure Color.white (lOnePort Color.white)) :=
  lOneExposure_proper Color.white Color.white_nonGrey

example : ∃ A : RootAllocation Examples.nestedTarget
    Examples.nestedTarget_in_classK, ProperExposure (rootPortExposure A.ports) := by
  obtain ⟨A, _hu, _hsmall, _hlarge⟩ :=
    completeRootAllocationCoverage Examples.nestedTarget_in_classK
  exact ⟨A, A.proper⟩

def nestedInnerNode : PairedNode Examples.nestedTarget :=
  ⟨Examples.innerArc, by decide⟩

theorem nestedInnerNode_is_E : IsEEndpoint nestedInnerNode := by decide

theorem nestedInnerNode_is_loop : IsLoopNode nestedInnerNode :=
  isLoopNode_of_endpointType nestedInnerNode .E nestedInnerNode_is_E

example : Nonempty (LoopAllocation Examples.nestedTarget
    Examples.nestedTarget_in_classK nestedInnerNode .E Color.black 0) := by
  exact exists_completeLoopAllocationCoverage
    Examples.nestedTarget_in_classK nestedInnerNode nestedInnerNode_is_loop
    .E nestedInnerNode_is_E Color.black 0 (by simp)

end RNA.Milestone2Examples
