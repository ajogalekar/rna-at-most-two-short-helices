# Milestone 3 assembly design

## Scope and fixed interfaces

This milestone constructs one value of the existing public type

```lean
Coloring T = PairedNode T → Color
```

and proves `ProperColoring` and `StrongTwoSeparatedWith` using the exact
integer-level definitions in `RNA/Coloring.lean`.  It does not alter any
Milestone 1 scientific definition or the meaning of a Milestone 2 theorem.

The base commit is
`bf6a7cefbe34c1d7dc44b21dd8bb031b9c66e68b`.

## Compared representations

### A. Proof-bearing partial assignments

In this representation a `SubtreeColoring H` is a function on the subtype of
paired nodes in the helix subtree rooted at `H`.  A recursive step installs a
local word on the members of `H`, obtains one partial assignment for each
actual outgoing child helix, and takes their disjoint union.  The attractive
feature is that coverage and non-overwrite are visible directly in the type of
the partial assignment.  The cost is that every recursive call must transport
dependent function domains through a finite disjoint union, and each local
postcondition must subsequently be repackaged with an arbitrary total
extension.

### B. Recursive proof plan followed by flattening

In this representation a plan at `H` records one proof-bearing
`LocalTransfer` on `H`, the endpoint classification and actual
`LoopAllocation` at `H.terminalNode`, and one child plan for every actual
outgoing child slot.  The child plan is indexed by the allocation's exact
entry residue and port.  A separate flattening operation interprets the plan
as a `SubtreeColoring H`, using the proved decomposition of the paired subtree
into the members of `H` and the pairwise-disjoint outgoing child subtrees.

Milestone 3 uses approach B.  It mirrors the manuscript's recursive proof and
keeps the local transfer and its allocation together.  The flattening proof is
the only place where dependent disjoint unions are handled.  After flattening,
the same extension-stable postcondition used by approach A is exposed, so no
later theorem depends on the internal plan representation.

## Helix subtrees and recursion measure

For a maximal helix `H`, the paired subtree is the finite set consisting of
`H.headNode` and all target pairs strictly nested in it.  The unpaired subtree
is the finite set of target-unpaired positions strictly nested in
`H.headNode`.  The implementation proves these are exactly the helix members
plus the corresponding subtrees of the actual paired children of
`H.terminalNode`.

The well-founded measure is

```lean
helixSubtreePairCount H = (pairedHelixSubtree T H).card
```

An outgoing child helix has its head strictly nested in `H.terminalNode`, so
its paired subtree is a strict subset of the parent's paired subtree; its head
is a concrete member witnessing strictness.  Therefore every recursive child
call has strictly smaller `helixSubtreePairCount`.

The subtree API proves:

- every member of `H` is in `pairedHelixSubtree T H`;
- every outgoing child subtree is a strict subset of the parent subtree;
- distinct outgoing child paired and unpaired subtrees are disjoint;
- helix members are disjoint from outgoing child subtrees;
- the exact parent-subtree decomposition;
- pairwise disjoint root-child subtrees and their exact union;
- the analogous root-unpaired complement statement.

These results are proved from interval containment, parent minimality, maximal
helix coverage, and the helix-chain theorem.  They do not assume a coloring.

## Recursive plan contract

For global residues `xi` and `eta = xi.opposite`, a plan rooted at `H` is
indexed by an entry residue, a fixed first color, and `Safe H.length entry eta
first`.  It records:

1. the endpoint type of `H.terminalNode`;
2. requested exit `xi` for E and L, and `eta` for M;
3. `transferForClassKHelix` for that request;
4. the actual closing color, proved to be the last transfer color;
5. the actual `LoopAllocation` constructed from that closing color;
6. one recursively constructed child plan for every actual outgoing slot,
   indexed by `allocation.entry` and `allocation.ports i`;
7. the `Safe` proof supplied by `LoopAllocation.safeOutgoing` for each child.

For L, the transfer's opposite-of-`eta` exit supplies the required non-grey
closing proof.  E has no outgoing slots.  L has zero or one, and M has two or
three, but the child family is indexed by the actual finite slot type, so the
ordinary, designated-short, and tight table rows are inherited directly from
the selected `LoopAllocation` rather than reimplemented in the recursion.

## Flattening and exact ownership

`SubtreeColoring H` assigns colors only to the subtype of paired nodes in
`pairedHelixSubtree T H`.  Flattening proceeds by the exact decomposition:

- a member of `H` receives the corresponding entry of the local transfer
  word;
- every other subtree pair belongs to exactly one outgoing child subtree and
  receives the color from that child plan.

Uniqueness of a helix offset and pairwise disjointness of child subtrees prove
that each pair receives exactly one color.  No last-update-wins convention is
used.  The following facts are proved about flattening:

- its restriction to `H` is precisely the selected transfer word;
- each child head has precisely its allocated port;
- it restricts to each child flattening on the entire child subtree;
- its domain covers the complete parent subtree.

At the root, the same construction takes the pairwise-disjoint union of the
flattened root-child plans.  The root partition theorem says this domain is
all of `PairedNode T`, so the result is a total `Coloring T` with no default or
arbitrary outside value.

## Extension-stable certificate

Although plans are flattened before root assembly, the public recursive
result is packaged as an extension-stable certificate.  `ExtendsSubtree chi
sigma` means pointwise agreement on the exact paired subtree domain.  A
`SubtreeCertificate` proves that for every such total extension whose actual
head entry level has the indexed entry residue:

- the head has the indexed first color and the local transfer word is
  installed on the real maximal helix;
- every paired exposure in the subtree is proper;
- every grey subtree pair has residue `eta`;
- every target-unpaired subtree position has residue `xi`;
- child heads have exactly the selected ports;
- the terminal residue is `xi` for E and L and `eta` for M;
- an L terminal closes non-grey.

The quantification over every total extension is essential.  Internal helix
exposures are proved from the installed internally proper word and the exact
helix-chain child shape.  Terminal exposures are proved from actual child-head
agreement with `LoopAllocation.ports`.  Thus colors outside the subtree cannot
silently enter a proof.

## Root assembly and global proof

The root construction first selects `completeRootAllocationCoverage hK`, sets
`xi := allocation.row.xi` and `eta := allocation.row.eta`, and constructs one
plan for each actual root-child helix from `RootAllocation.safeOutgoing`.
Flattening those plans gives the total coloring.

Root exposure properness follows from the actual root ports.  Every nonroot
paired node is either an internal member of one helix or its terminal, so its
proper exposure follows from the appropriate subtree certificate.  Installed
transfer bridges give every grey pair residue `eta`.  Nonroot unpaired
positions are children of an L terminal and hence have residue `xi`; root
unpaired positions have exact integer level zero.  Root allocation coverage
forces an xi row whenever root-unpaired positions exist, and xi rows have
`xi = 0`.

The resulting noncomputable `GlobalColoringCertificate` retains `xi`, the
total coloring, properness, and `StrongTwoSeparatedWith`.  The two existential
forms and the exact Theorem 12 declaration are projections of this one
witness; no finite search over global colorings is used.

## Dependency and safety notes

Classical choice is used only to select objects supplied by proved
existence/uniqueness theorems: maximal helices, child indices, endpoint types,
and finite disjoint-union branches.  Well-founded recursion is justified by
the strict subtree-cardinality theorem.  No local certificate assumes future
global properness, and no proof inspects arbitrary colors outside its exact
subtree domain.
