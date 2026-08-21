module

public import RNA.SubtreeConstruction
public import RNA.AtMostTwoShort.Transfers
public import RNA.AtMostTwoShort.ResourceAllocations

@[expose] public section

set_option autoImplicit false

/-!
# Extension-stable resource subtree certificates

The completed exact-one certificate is intentionally left unchanged.  This
parallel certificate is indexed by the enlarged target class and by an actual
resource-aware child allocation.  Its `sound` field quantifies over every
total extension of the exact subtree domain; this is the formal statement
that later sibling installations cannot invalidate an already constructed
child.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Complete extension-stable postcondition at a resource-constructed helix
subtree. -/
structure ResourceSubtreePostcondition
    (hK : InTargetClassKLeTwo T) (chi : Coloring T) (H : MaximalHelix T)
    (xi entry : Parity) (first : Color) (e : EndpointType)
    (tr : LocalTransfer H.length entry xi.opposite
      (requestedExit xi xi.opposite e) first)
    (A : ResourceLoopAllocation T hK H e
      (tr.closingColor H.positive) xi) : Prop where
  headColor : chi H.headNode = first
  installed : HelixWordInstalled chi H tr.colors
  proper : ∀ p ∈ pairedHelixSubtree T H,
    ProperExposure (exposedMultiset chi (some p))
  greysAt : ∀ p ∈ pairedHelixSubtree T H, chi p = Color.grey →
    levelParity (pairedLevel chi p) = xi.opposite
  unpairedAt : ∀ u ∈ unpairedHelixSubtree T H,
    levelParity (unpairedLevel chi u) = xi
  childPorts : ChildPortsInstalled chi (some H.terminalNode) A.ports
  terminalResidue :
    levelParity (pairedLevel chi H.terminalNode) =
      requestedExit xi xi.opposite e
  lTerminalNonGrey : e = .L -> (chi H.terminalNode).NonGrey
  twoDemandTerminalNonGrey :
    e = .M -> (loopShortSupport T H).card = 2 ->
      (chi H.terminalNode).NonGrey

/-- A proof-bearing exact-domain assignment for one complete resource
subtree. -/
structure ResourceSubtreeCertificate
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (xi entry : Parity) (first : Color)
    (sigma : SubtreeColoring H) where
  endpoint : EndpointType
  endpoint_spec : HasEndpointType H.terminalNode endpoint
  transfer : LocalTransfer H.length entry xi.opposite
    (requestedExit xi xi.opposite endpoint) first
  allocation : ResourceLoopAllocation T hK H endpoint
    (transfer.closingColor H.positive) xi
  sound : ∀ chi : Coloring T, ExtendsSubtree chi sigma →
    entry = levelParity (entryLevel chi H.headNode) →
      ResourceSubtreePostcondition hK chi H xi entry first endpoint
        transfer allocation

/-- Type of a constructed exact subtree assignment together with its retained
resource certificate. -/
abbrev CertifiedResourceSubtree
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (xi entry : Parity) (first : Color) :=
  Sigma fun sigma : SubtreeColoring H =>
    ResourceSubtreeCertificate hK H xi entry first sigma

/-- Semantic acceptance of an interface by the complete helix subtree.  The
construction proves guaranteed F/Q subsets of this relation; it does not claim
that either subset is exact. -/
def AcceptsInterface
    (T : SecondaryStructure n) (H : MaximalHelix T)
    (xi entry : Parity) (first : Color) : Prop :=
  exists hK : InTargetClassKLeTwo T, exists sigma : SubtreeColoring H,
    Nonempty (ResourceSubtreeCertificate hK H xi entry first sigma)

/-! ## Explicit gluing facts retained by the construction -/

/-- Actual outgoing child domains are pairwise disjoint. -/
theorem resource_child_domains_pairwiseDisjoint
    (H : MaximalHelix T)
    {i j : Fin (pairedChildCount T (some H.terminalNode))} (hne : i ≠ j) :
    Disjoint (pairedHelixSubtree T (outgoingHelix T H i))
      (pairedHelixSubtree T (outgoingHelix T H j)) :=
  pairedHelixSubtree_outgoing_disjoint H hne

/-- The installed parent helix word has no node in an outgoing child domain. -/
theorem resource_parent_domain_disjoint_child
    (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    Disjoint (helixMemberNodes T H)
      (pairedHelixSubtree T (outgoingHelix T H i)) :=
  helixMemberNodes_disjoint_outgoing H i

/-- The parent word and the actual child subtrees cover exactly the complete
paired subtree. -/
theorem resource_paired_subtree_exact_decomposition (H : MaximalHelix T) :
    pairedHelixSubtree T H =
      helixMemberNodes T H ∪ outgoingPairedHelixSubtreeUnion T H :=
  pairedHelixSubtree_decomposition H

/-- Direct unpaired children and the actual child subtrees cover exactly the
complete unpaired subtree. -/
theorem resource_unpaired_subtree_exact_decomposition (H : MaximalHelix T) :
    unpairedHelixSubtree T H =
      unpairedChildren T (some H.terminalNode) ∪
        outgoingUnpairedHelixSubtreeUnion T H :=
  unpairedHelixSubtree_decomposition H

/-- A certificate is stable in each total extension separately.  In the
recursive proof this is instantiated for the flattened parent assignment;
pairwise domain disjointness above ensures that installing another sibling is
just another such extension and cannot alter the certified child's result. -/
theorem ResourceSubtreeCertificate.sound_in_every_extension
    {hK : InTargetClassKLeTwo T} {H : MaximalHelix T}
    {xi entry : Parity} {first : Color} {sigma : SubtreeColoring H}
    (C : ResourceSubtreeCertificate hK H xi entry first sigma)
    (chi : Coloring T) (hext : ExtendsSubtree chi sigma)
    (hentry : entry = levelParity (entryLevel chi H.headNode)) :
    ResourceSubtreePostcondition hK chi H xi entry first C.endpoint
      C.transfer C.allocation :=
  C.sound chi hext hentry

end RNA
