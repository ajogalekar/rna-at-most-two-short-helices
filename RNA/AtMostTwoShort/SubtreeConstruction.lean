module

public import RNA.AtMostTwoShort.ResourceCertificate

@[expose] public section

set_option autoImplicit false

/-!
# Resource-aware recursive subtree construction

This is a new recursion parallel to the completed exact-one construction.  It
uses the same exact paired-subtree measure and the same disjoint flattening
algebra, but its recursive interface is `RequiredInterface`: a short-free
child receives every F interface, while a child carrying one or two short
helices receives a Q interface.

The transfer choice retains both closing facts needed by the actual loop
allocator.  In particular, an M endpoint with two positive-short outgoing
subtrees uses `longTransfer_eta_closesNonGrey_of_Q`; this is part of this
recursion rather than a premise imported from an older designability theorem.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Every maximal helix in the enlarged class has one of the two locally
allowed lengths. -/
theorem targetClassKLeTwo_helix_length_allowed
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T) :
    H.length = 2 ∨ 3 ≤ H.length := by
  by_cases htwo : H.length = 2
  · exact Or.inl htwo
  · exact Or.inr
      (targetClassKLeTwo_nonshort_length_at_least_three hK H htwo)

/-- The local word selected at a resource recursion step, bundled with the
two named closing-colour facts required by L allocation and by the exceptional
two-demand M allocation. -/
structure ResourceTransferChoice
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (xi entry : Parity) (first : Color) (e : EndpointType)
    (hrequired : RequiredInterface T H xi entry first) where
  transfer : LocalTransfer H.length entry xi.opposite
    (requestedExit xi xi.opposite e) first
  lClosingNonGrey : e = .L →
    (transfer.closingColor H.positive).NonGrey
  twoDemandClosingNonGrey : e = .M →
    (loopShortSupport T H).card = 2 →
      (transfer.closingColor H.positive).NonGrey

/-- Select the ordinary allowed-length transfer except at an M endpoint with
two positive-short outgoing subtrees.  In that branch the parent resource
count is positive, so its required interface is Q; the two-child count also
forces the incoming helix to be long. -/
noncomputable def chooseResourceTransfer
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (xi entry : Parity) (first : Color) (e : EndpointType)
    (hrequired : RequiredInterface T H xi entry first) :
    ResourceTransferChoice hK H xi entry first e hrequired := by
  have hallowed := targetClassKLeTwo_helix_length_allowed hK H
  have hsafe := hrequired.safe hK H
  cases e with
  | E =>
      let tr := allowedHelixTransfer H xi entry xi first hallowed hsafe
      refine {
        transfer := tr
        lClosingNonGrey := ?_
        twoDemandClosingNonGrey := ?_ }
      · intro hbad
        simp at hbad
      · intro hbad
        simp at hbad
  | L =>
      let tr := allowedHelixTransfer H xi entry xi first hallowed hsafe
      refine {
        transfer := tr
        lClosingNonGrey := ?_
        twoDemandClosingNonGrey := ?_ }
      · intro _
        apply tr.closingColor_nonGrey H.positive
        exact (Parity.opposite_opposite xi).symm
      · intro hbad
        simp at hbad
  | M =>
      by_cases htwo : (loopShortSupport T H).card = 2
      · have hlong : 3 ≤ H.length :=
          loopShortSupport_card_eq_two_length_at_least_three hK H htwo
        have hcountPos : 0 < shortHelixSubtreeCount T H := by
          have hle := loopShortSupport_card_le_shortHelixSubtreeCount H
          omega
        have hQ : InQ xi entry first :=
          requiredInterface_inQ_of_count_pos hcountPos hrequired
        let longTr := longTransfer_eta_closesNonGrey_of_Q
          H.length xi entry first hlong hQ
        refine {
          transfer := longTr.1
          lClosingNonGrey := ?_
          twoDemandClosingNonGrey := ?_ }
        · intro hbad
          simp at hbad
        · intro _ _
          exact longTr.closingColor_nonGrey H.positive
      · let tr := allowedHelixTransfer H xi entry xi.opposite first
          hallowed hsafe
        refine {
          transfer := tr
          lClosingNonGrey := ?_
          twoDemandClosingNonGrey := ?_ }
        · intro hbad
          simp at hbad
        · intro _ hcard
          exact False.elim (htwo hcard)

/-- The parent transfer fixes the residue at the entry of every actual
outgoing child.  This is the level bridge used by every recursive child
certificate; it depends only on the actual parent path, not on any sibling. -/
theorem ResourceLoopAllocation.entry_eq_outgoing_entryLevel
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (xi entry : Parity) (first : Color) (e : EndpointType)
    (_he : HasEndpointType H.terminalNode e)
    (tr : LocalTransfer H.length entry xi.opposite
      (requestedExit xi xi.opposite e) first)
    (A : ResourceLoopAllocation T hK H e
      (tr.closingColor H.positive) xi)
    (chi : Coloring T) (hinstalled : HelixWordInstalled chi H tr.colors)
    (hentry : entry = levelParity (entryLevel chi H.headNode))
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    A.entry = levelParity
      (entryLevel chi (outgoingHelix T H i).headNode) := by
  have hchild : (outgoingHelix T H i).headNode ∈
      pairedChildren T (some H.terminalNode) := by
    rw [outgoingHelix_headNode]
    exact orderedPairedChild_mem T (some H.terminalNode) i
  have hlevel := entryLevel_of_mem_pairedChildren chi hchild
  have hterminal :=
    installedLocalTransfer_terminalLevel chi H tr hinstalled hentry
  rw [hlevel]
  calc
    A.entry = requestedExit xi xi.opposite e :=
      A.entry_eq_requestedExit
    _ = levelParity (pairedLevel chi H.terminalNode) := hterminal.symm

/-- Recursive proof object and exact-domain colouring for one resource-aware
helix subtree. -/
noncomputable def constructResourceSubtree
    (hK : InTargetClassKLeTwo T) (xi : Parity)
    (H : MaximalHelix T) (entry : Parity) (first : Color)
    (hrequired : RequiredInterface T H xi entry first) :
    CertifiedResourceSubtree hK H xi entry first := by
  let hpLoop : IsLoopNode H.terminalNode := ⟨H, rfl⟩
  let e : EndpointType := Classical.choose
    (loopNode_endpointType_exists (targetClassKLeTwo_motifFree hK)
      H.terminalNode hpLoop)
  have he : HasEndpointType H.terminalNode e :=
    Classical.choose_spec
      (loopNode_endpointType_exists (targetClassKLeTwo_motifFree hK)
        H.terminalNode hpLoop)
  let choice := chooseResourceTransfer hK H xi entry first e hrequired
  let tr := choice.transfer
  let A : ResourceLoopAllocation T hK H e
      (tr.closingColor H.positive) xi :=
    completeResourceLoopAllocation hK H e he
      (tr.closingColor H.positive) xi
      choice.lClosingNonGrey choice.twoDemandClosingNonGrey
  have childShortCountLeTwo
      (i : Fin (pairedChildCount T (some H.terminalNode))) :
      shortHelixSubtreeCount T (outgoingHelix T H i) ≤ 2 :=
    shortHelixSubtreeCount_le_two hK (outgoingHelix T H i)
  have childRequired
      (i : Fin (pairedChildCount T (some H.terminalNode))) :
      RequiredInterface T (outgoingHelix T H i) xi A.entry (A.ports i) := by
    by_cases hzero :
        shortHelixSubtreeCount T (outgoingHelix T H i) = 0
    · exact A.requiredOutgoing i
    · have hpositive :
          1 ≤ shortHelixSubtreeCount T (outgoingHelix T H i) :=
        Nat.one_le_iff_ne_zero.2 hzero
      have hbound := childShortCountLeTwo i
      have hpositiveCases :
          shortHelixSubtreeCount T (outgoingHelix T H i) = 1 ∨
            shortHelixSubtreeCount T (outgoingHelix T H i) = 2 := by
        omega
      rcases hpositiveCases with hone | htwo
      · exact A.requiredOutgoing i
      · exact A.requiredOutgoing i
  let childResult
      (i : Fin (pairedChildCount T (some H.terminalNode))) :=
    constructResourceSubtree hK xi (outgoingHelix T H i)
      A.entry (A.ports i) (childRequired i)
  let children : OutgoingSubtreeColorings H := fun i => (childResult i).1
  have childCert (i : Fin (pairedChildCount T (some H.terminalNode))) :
      ResourceSubtreeCertificate hK (outgoingHelix T H i) xi A.entry
        (A.ports i) (children i) := by
    simpa [children, childResult] using (childResult i).2
  let sigma : SubtreeColoring H :=
    assembleSubtreeColoring H tr.colors tr.length_eq children
  refine ⟨sigma, {
    endpoint := e
    endpoint_spec := he
    transfer := tr
    allocation := A
    sound := ?_ }⟩
  intro chi hextends hentry
  have hextendsAssembly : ExtendsSubtree chi
      (assembleSubtreeColoring H tr.colors tr.length_eq children) := by
    simpa [sigma] using hextends
  have hinstalled : HelixWordInstalled chi H tr.colors :=
    helixWordInstalled_of_extendsSubtree_assemble chi H tr.colors
      tr.length_eq children hextendsAssembly
  have hchildExtends
      (i : Fin (pairedChildCount T (some H.terminalNode))) :
      ExtendsSubtree chi (children i) :=
    extendsSubtree_child_of_extends_assemble chi H tr.colors tr.length_eq
      children hextendsAssembly i
  have hchildEntry
      (i : Fin (pairedChildCount T (some H.terminalNode))) :
      A.entry = levelParity
        (entryLevel chi (outgoingHelix T H i).headNode) :=
    A.entry_eq_outgoing_entryLevel hK H xi entry first e he tr chi
      hinstalled hentry i
  have hchildPost
      (i : Fin (pairedChildCount T (some H.terminalNode))) :
      ResourceSubtreePostcondition hK chi (outgoingHelix T H i) xi
        A.entry (A.ports i) (childCert i).endpoint
          (childCert i).transfer (childCert i).allocation :=
    (childCert i).sound chi (hchildExtends i) (hchildEntry i)
  have hports : ChildPortsInstalled chi (some H.terminalNode) A.ports := by
    intro i
    have hhead := (hchildPost i).headColor
    rw [outgoingHelix_headNode] at hhead
    exact hhead
  have hterminal : levelParity (pairedLevel chi H.terminalNode) =
      requestedExit xi xi.opposite e :=
    installedLocalTransfer_terminalLevel chi H tr hinstalled hentry
  have hclosingActual : chi H.terminalNode = tr.closingColor H.positive :=
    installedLocalTransfer_terminalColor_eq_closingColor chi H tr hinstalled
  refine {
    headColor := installedLocalTransfer_headColor chi H tr hinstalled
    installed := hinstalled
    proper := ?_
    greysAt := ?_
    unpairedAt := ?_
    childPorts := hports
    terminalResidue := hterminal
    lTerminalNonGrey := ?_
    twoDemandTerminalNonGrey := ?_ }
  · intro p hp
    rw [resource_paired_subtree_exact_decomposition H] at hp
    rcases Finset.mem_union.mp hp with hpMember | hpChild
    · by_cases hterminalNode : p = H.terminalNode
      · subst p
        exact A.properActualExposure chi hclosingActual hports
      · apply properExposure_nonterminalHelixMember_of_installed
          chi H tr.colors hinstalled tr.internallyProper p
        · exact (mem_helixMemberNodes_iff H p).1 hpMember
        · exact hterminalNode
    · obtain ⟨i, hi⟩ :=
        (mem_outgoingPairedHelixSubtreeUnion_iff H p).1 hpChild
      exact (hchildPost i).proper p hi
  · intro p hp hpGrey
    rw [resource_paired_subtree_exact_decomposition H] at hp
    rcases Finset.mem_union.mp hp with hpMember | hpChild
    · let k := helixMemberOffset H p hpMember
      have hkNode : H.offsetNode k = p :=
        offsetNode_helixMemberOffset H p hpMember
      have hglobal :=
        installedLocalTransfer_globalGreysAt chi H tr hinstalled hentry
      have hkGrey : chi (H.offsetNode k) = Color.grey := by
        simpa [hkNode] using hpGrey
      simpa [hkNode] using hglobal k hkGrey
    · obtain ⟨i, hi⟩ :=
        (mem_outgoingPairedHelixSubtreeUnion_iff H p).1 hpChild
      exact (hchildPost i).greysAt p hi hpGrey
  · intro u hu
    rw [resource_unpaired_subtree_exact_decomposition H] at hu
    rcases Finset.mem_union.mp hu with huDirect | huChild
    · have hlevel := unpairedLevel_of_mem_pairedChildren chi huDirect
      have hhas : HasUnpairedChild T (some H.terminalNode) := ⟨u, huDirect⟩
      cases heq : e with
      | L =>
          rw [hlevel, hterminal]
          simp [heq]
      | M =>
          have heM : IsMEndpoint H.terminalNode := by
            simpa [heq, HasEndpointType] using he
          exact False.elim (heM.1 hhas)
      | E =>
          have heE : IsEEndpoint H.terminalNode := by
            simpa [heq, HasEndpointType] using he
          exact False.elim (heE.1 hhas)
    · obtain ⟨i, hi⟩ :=
        (mem_outgoingUnpairedHelixSubtreeUnion_iff H u).1 huChild
      exact (hchildPost i).unpairedAt u hi
  · intro heL
    rw [hclosingActual]
    exact choice.lClosingNonGrey heL
  · intro heM hcard
    rw [hclosingActual]
    exact choice.twoDemandClosingNonGrey heM hcard
termination_by helixSubtreePairCount T H
decreasing_by
  exact helixSubtreePairCount_outgoing_lt H i

/-- Canonical exact-domain assignment returned by the resource recursion. -/
noncomputable def constructedResourceSubtreeColoring
    (hK : InTargetClassKLeTwo T) (xi : Parity)
    (H : MaximalHelix T) (entry : Parity) (first : Color)
    (hrequired : RequiredInterface T H xi entry first) : SubtreeColoring H :=
  (constructResourceSubtree hK xi H entry first hrequired).1

/-- Certificate retained for the canonical resource assignment. -/
noncomputable def constructedResourceSubtreeCertificate
    (hK : InTargetClassKLeTwo T) (xi : Parity)
    (H : MaximalHelix T) (entry : Parity) (first : Color)
    (hrequired : RequiredInterface T H xi entry first) :
    ResourceSubtreeCertificate hK H xi entry first
      (constructedResourceSubtreeColoring hK xi H entry first hrequired) :=
  (constructResourceSubtree hK xi H entry first hrequired).2

/-- Every required F/Q interface has an exact-domain, extension-stable
resource subtree certificate. -/
theorem exists_resourceSubtreeColoring
    (hK : InTargetClassKLeTwo T) (xi : Parity)
    (H : MaximalHelix T) (entry : Parity) (first : Color)
    (hrequired : RequiredInterface T H xi entry first) :
    ∃ sigma : SubtreeColoring H,
      Nonempty (ResourceSubtreeCertificate hK H xi entry first sigma) :=
  ⟨constructedResourceSubtreeColoring hK xi H entry first hrequired,
    ⟨constructedResourceSubtreeCertificate hK xi H entry first
      hrequired⟩⟩

/-- Semantic acceptance follows from the direct resource recursion. -/
theorem acceptsInterface_of_required
    (hK : InTargetClassKLeTwo T) (xi : Parity)
    (H : MaximalHelix T) (entry : Parity) (first : Color)
    (hrequired : RequiredInterface T H xi entry first) :
    AcceptsInterface T H xi entry first := by
  refine ⟨hK, constructedResourceSubtreeColoring hK xi H entry first
    hrequired, ?_⟩
  exact ⟨constructedResourceSubtreeCertificate hK xi H entry first
    hrequired⟩

/-- Zero-resource branch of the extension-stable invariant: every F
interface is accepted. -/
theorem resourceInvariant_F
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (hzero : shortHelixSubtreeCount T H = 0)
    (xi entry : Parity) (first : Color) (hF : InF xi entry first) :
    AcceptsInterface T H xi entry first := by
  apply acceptsInterface_of_required hK xi H entry first
  simpa [RequiredInterface, hzero] using hF

/-- Positive-resource branch of the extension-stable invariant: when the
subtree count is one or two, every Q interface is accepted. -/
theorem resourceInvariant_Q
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (hpos : 1 ≤ shortHelixSubtreeCount T H)
    (hle : shortHelixSubtreeCount T H ≤ 2)
    (xi entry : Parity) (first : Color) (hQ : InQ xi entry first) :
    AcceptsInterface T H xi entry first := by
  apply acceptsInterface_of_required hK xi H entry first
  have hne : shortHelixSubtreeCount T H ≠ 0 := by omega
  simpa [RequiredInterface, hne] using hQ

/-- The formal F/Q resource invariant in one statement. -/
theorem constructResourceSubtree_resourceInvariant
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T) :
    (∀ xi entry first,
      shortHelixSubtreeCount T H = 0 → InF xi entry first →
        AcceptsInterface T H xi entry first) ∧
    (∀ xi entry first,
      1 ≤ shortHelixSubtreeCount T H →
      shortHelixSubtreeCount T H ≤ 2 → InQ xi entry first →
        AcceptsInterface T H xi entry first) := by
  constructor
  · intro xi entry first hzero hF
    exact resourceInvariant_F hK H hzero xi entry first hF
  · intro xi entry first hpos hle hQ
    exact resourceInvariant_Q hK H hpos hle xi entry first hQ

end RNA
