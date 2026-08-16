module

public import RNA.Milestone3Local
public import RNA.SubtreeColoring

@[expose] public section

set_option autoImplicit false

/-!
# Recursive construction on a maximal-helix subtree

The certificate in this file is stable under every total colouring extending
the exact-domain partial assignment.  Its only hypothesis about colours above
the subtree is the prescribed residue at the head entry interface.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Requested terminal residue for the three endpoint classes. -/
def requestedExit (xi eta : Parity) : EndpointType → Parity
  | .L => xi
  | .M => eta
  | .E => xi

@[simp] theorem requestedExit_L (xi eta : Parity) :
    requestedExit xi eta .L = xi := rfl

@[simp] theorem requestedExit_M (xi eta : Parity) :
    requestedExit xi eta .M = eta := rfl

@[simp] theorem requestedExit_E (xi eta : Parity) :
    requestedExit xi eta .E = xi := rfl

/-- The complete extension-stable postcondition at one helix subtree. -/
structure SubtreePostcondition
    (hK : InTargetClassK T) (chi : Coloring T) (H : MaximalHelix T)
    (xi eta entry : Parity) (first : Color) (e : EndpointType)
    (tr : LocalTransfer H.length entry eta (requestedExit xi eta e) first)
    (A : LoopAllocation T hK H.terminalNode e
      (tr.closingColor H.positive) xi) : Prop where
  headColor : chi H.headNode = first
  installed : HelixWordInstalled chi H tr.colors
  proper : ∀ p ∈ pairedHelixSubtree T H,
    ProperExposure (exposedMultiset chi (some p))
  greysAt : ∀ p ∈ pairedHelixSubtree T H, chi p = Color.grey →
    levelParity (pairedLevel chi p) = eta
  unpairedAt : ∀ u ∈ unpairedHelixSubtree T H,
    levelParity (unpairedLevel chi u) = xi
  childPorts : ChildPortsInstalled chi (some H.terminalNode) A.ports
  terminalResidue :
    levelParity (pairedLevel chi H.terminalNode) = requestedExit xi eta e
  lTerminalNonGrey : e = .L → (chi H.terminalNode).NonGrey

/-- A proof-bearing exact-domain assignment with its selected local data. -/
structure SubtreeCertificate
    (hK : InTargetClassK T) (H : MaximalHelix T)
    (xi eta entry : Parity) (first : Color)
    (sigma : SubtreeColoring H) where
  endpoint : EndpointType
  endpoint_spec : HasEndpointType H.terminalNode endpoint
  transfer :
    LocalTransfer H.length entry eta (requestedExit xi eta endpoint) first
  allocation : LoopAllocation T hK H.terminalNode endpoint
    (transfer.closingColor H.positive) xi
  sound : ∀ chi : Coloring T, ExtendsSubtree chi sigma →
    entry = levelParity (entryLevel chi H.headNode) →
      SubtreePostcondition hK chi H xi eta entry first endpoint
        transfer allocation

/-- The parent transfer and endpoint allocation give every actual outgoing
child exactly the entry residue indexed by its recursive certificate. -/
theorem LoopAllocation.entry_eq_outgoing_entryLevel
    (hK : InTargetClassK T) (H : MaximalHelix T)
    (xi eta entry : Parity) (first : Color) (e : EndpointType)
    (hopposite : eta = xi.opposite)
    (he : HasEndpointType H.terminalNode e)
    (tr : LocalTransfer H.length entry eta (requestedExit xi eta e) first)
    (A : LoopAllocation T hK H.terminalNode e
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
  cases e with
  | L =>
      calc
        A.entry = xi := A.lEntry rfl
        _ = requestedExit xi eta .L := rfl
        _ = levelParity (pairedLevel chi H.terminalNode) := hterminal.symm
  | M =>
      calc
        A.entry = xi.opposite := A.mEntry rfl
        _ = eta := hopposite.symm
        _ = requestedExit xi eta .M := rfl
        _ = levelParity (pairedLevel chi H.terminalNode) := hterminal.symm
  | E =>
      change IsEEndpoint H.terminalNode at he
      exact Fin.elim0 (finCongr he.2 i)

/-- Type of a constructed subtree assignment together with its certificate. -/
abbrev CertifiedSubtree
    (hK : InTargetClassK T) (H : MaximalHelix T)
    (xi eta entry : Parity) (first : Color) :=
  Σ sigma : SubtreeColoring H,
    SubtreeCertificate hK H xi eta entry first sigma

/-- Recursive proof object and exact-domain colouring for one helix subtree. -/
noncomputable def constructSubtree
    (hK : InTargetClassK T) (xi eta : Parity)
    (hopposite : eta = xi.opposite)
    (H : MaximalHelix T) (entry : Parity) (first : Color)
    (hsafe : Safe H.length entry eta first) :
    CertifiedSubtree hK H xi eta entry first := by
  let hpLoop : IsLoopNode H.terminalNode := ⟨H, rfl⟩
  let e : EndpointType := Classical.choose
    (targetClass_loopNode_endpointType hK H.terminalNode hpLoop)
  have he : HasEndpointType H.terminalNode e :=
    (Classical.choose_spec
      (targetClass_loopNode_endpointType hK H.terminalNode hpLoop)).1
  let tr : LocalTransfer H.length entry eta (requestedExit xi eta e) first :=
    transferForClassKHelix hK H entry eta (requestedExit xi eta e) first hsafe
  have hxi_etaOpposite : xi = eta.opposite := by
    rw [hopposite, Parity.opposite_opposite]
  have hclosing : e = .L → (tr.closingColor H.positive).NonGrey := by
    intro heL
    apply tr.closingColor_nonGrey H.positive
    simpa [heL] using hxi_etaOpposite
  let A : LoopAllocation T hK H.terminalNode e
      (tr.closingColor H.positive) xi :=
    completeLoopAllocationCoverage hK H.terminalNode hpLoop e he
      (tr.closingColor H.positive) xi hclosing
  have childSafe
      (i : Fin (pairedChildCount T (some H.terminalNode))) :
      Safe (outgoingHelix T H i).length A.entry eta (A.ports i) := by
    simpa [outgoingHelix, hopposite] using A.safeOutgoing hpLoop he i
  let childResult
      (i : Fin (pairedChildCount T (some H.terminalNode))) :=
    constructSubtree hK xi eta hopposite (outgoingHelix T H i)
      A.entry (A.ports i) (childSafe i)
  let children : OutgoingSubtreeColorings H := fun i => (childResult i).1
  have childCert (i : Fin (pairedChildCount T (some H.terminalNode))) :
      SubtreeCertificate hK (outgoingHelix T H i) xi eta A.entry
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
    LoopAllocation.entry_eq_outgoing_entryLevel hK H xi eta entry first e
      hopposite he tr A chi hinstalled hentry i
  have hchildPost
      (i : Fin (pairedChildCount T (some H.terminalNode))) :
      SubtreePostcondition hK chi (outgoingHelix T H i) xi eta A.entry
        (A.ports i) (childCert i).endpoint (childCert i).transfer
          (childCert i).allocation :=
    (childCert i).sound chi (hchildExtends i) (hchildEntry i)
  have hports : ChildPortsInstalled chi (some H.terminalNode) A.ports := by
    intro i
    have hhead := (hchildPost i).headColor
    rw [outgoingHelix_headNode] at hhead
    exact hhead
  have hterminal : levelParity (pairedLevel chi H.terminalNode) =
      requestedExit xi eta e :=
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
    lTerminalNonGrey := ?_ }
  · intro p hp
    rw [pairedHelixSubtree_decomposition H] at hp
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
    rw [pairedHelixSubtree_decomposition H] at hp
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
    rw [unpairedHelixSubtree_decomposition H] at hu
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
    exact hclosing heL
termination_by helixSubtreePairCount T H
decreasing_by
  exact helixSubtreePairCount_outgoing_lt H i

/-- Canonical exact-domain assignment returned by the recursive construction. -/
noncomputable def constructedSubtreeColoring
    (hK : InTargetClassK T) (xi eta : Parity)
    (hopposite : eta = xi.opposite)
    (H : MaximalHelix T) (entry : Parity) (first : Color)
    (hsafe : Safe H.length entry eta first) : SubtreeColoring H :=
  (constructSubtree hK xi eta hopposite H entry first hsafe).1

/-- Certificate retained for the canonical recursive assignment. -/
noncomputable def constructedSubtreeCertificate
    (hK : InTargetClassK T) (xi eta : Parity)
    (hopposite : eta = xi.opposite)
    (H : MaximalHelix T) (entry : Parity) (first : Color)
    (hsafe : Safe H.length entry eta first) :
    SubtreeCertificate hK H xi eta entry first
      (constructedSubtreeColoring hK xi eta hopposite H entry first hsafe) :=
  (constructSubtree hK xi eta hopposite H entry first hsafe).2

/-- Every safe class-K helix admits an exact-domain subtree colouring with the
complete extension-stable Section 6 certificate. -/
theorem exists_subtreeColoring
    (hK : InTargetClassK T) (xi eta : Parity)
    (hopposite : eta = xi.opposite)
    (H : MaximalHelix T) (entry : Parity) (first : Color)
    (hsafe : Safe H.length entry eta first) :
    ∃ sigma : SubtreeColoring H,
      Nonempty (SubtreeCertificate hK H xi eta entry first sigma) :=
  ⟨constructedSubtreeColoring hK xi eta hopposite H entry first hsafe,
    ⟨constructedSubtreeCertificate hK xi eta hopposite H entry first hsafe⟩⟩

end RNA
