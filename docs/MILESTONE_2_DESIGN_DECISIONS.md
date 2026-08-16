# Milestone 2 design decisions

The frozen mathematical authority remains `CANONICAL_PROOF.md`.  These choices
only describe how its objects are represented in Lean.

## Colours and parity

`RNA.Color` is a three-constructor finite type (`black`, `white`, `grey`) with
decidable equality.  `Color.inv` and `Color.delta : Color -> Int` retain the
manuscript's exact signed algebra.  The two residue classes are represented by
`Parity`, an abbreviation for `ZMod 2`; `Parity.opposite r = r + 1` names the
other residue.  Thus no Boolean convention is hidden in theorem statements,
and the facts that black and white both contribute residue one while grey
contributes zero are explicit lemmas.

This split is deliberate.  Integer levels are needed by ordinary separation
and by the later prefix-balance argument.  `ZMod 2` is used only after an exact
integer level has been constructed, for strong two-separation and local helix
transfer.

## Colouring domain and exposed multisets

`Coloring T` is definitionally `PairedNode T -> Color`.  Consequently neither
the virtual root, an unpaired node, nor an arc outside `T.arcs` can be coloured
by accident.  Child colours are mapped from the actual finite set
`pairedChildren T p`; a nonroot exposure adds the singleton closing incidence
`inv (chi p)`, while the root exposure does not.

Properness is the manuscript's load-bearing multiset definition: black count
at most one, white count at most one, and grey count at most two.  The classical
child-rule reformulation is not used as a premise.

## Ancestor paths and exact levels

The entry level of a paired node is the finite integer sum of `delta` over all
strictly containing target pairs.  Laminarity makes this finite set exactly the
root-to-parent path.  Its inclusive level adds the node's own `delta`.

This representation avoids an arbitrary recursive traversal while retaining
the exact integer value.  A proved set decomposition at the computed parent
shows that the ancestor-sum entry level is zero at a root child and equals the
inclusive level of a paired parent.  An unpaired node is defined to have its
computed parent-interface level.  Therefore the usual parent recursion laws
are theorems about the existing interval tree, not a parallel informal model.

## Canonical maximal helices

Coverage is proved by extending only genuine consecutive target segments that
contain the selected arc.  Maximizing their length therefore cannot jump over
a missing offset.  The existing common-member uniqueness theorem then gives a
unique maximal helix for every target arc.  `maximalHelixContaining` packages
that unique witness, and the union/disjointness theorems expose the resulting
partition.

Heads, terminals, and ordered members are taken at canonical stack offsets.
The unique-container theorem is also what turns an actual paired child into the
head of one well-defined outgoing helix.  No allocation theorem is permitted
to choose an unrelated abstract helix.

## Assigning ports to actual children

Port assignments have the actual ordered outgoing children as their domain.
For a row with arity `d`, an order-preserving enumeration identifies those
children with `Fin d`; the row colour at an index is assigned to the child at
that index.  A designated row overrides the unique short child's index with
grey and enumerates the remaining long children over the remaining row
entries.  The assignment theorems record both the colour of each distinguished
child and equality between the resulting child-colour multiset and the
manuscript table row.  This makes exposure properness a consequence for the
real parent node, not only for an abstract multiset.

## Connecting local words to global levels

Local transfer uses a length-indexed word (or a list with a proved length) and
walks residues inclusively from an entry interface.  The global bridge
restricts an actual `Coloring T` to the canonical ordered members of a real
maximal helix.  Exact stacked-successor/parent lemmas and the global entry-level
recursion prove, offset by offset, that the local running residue equals the
mod-two image of the actual global `pairedLevel`.  Exit and grey-placement
corollaries are derived from that pointwise equality.

The abstract transfer construction is useful because it is finite and local;
the bridge is load-bearing because it prevents those local theorems from being
used as facts about an unrelated word.

## Recommendation for Milestone 3 recursion

The global colouring theorem should initially be an existence theorem proved
by well-founded structural induction on the number of paired nodes in a helix
subtree.  Each induction step can invoke the allocation witness and local
transfer witness, then combine colourings on proved-disjoint child subtrees.
This fits the current noncomputable canonical-helix and finite-enumeration APIs
without pretending that proof-bearing tree decomposition is definitionally
recursive.

After that theorem is stable, an executable recursive function returning a
colouring plus proof may be refined from the same lemmas if later extraction is
valuable.  Milestone 2 deliberately does not implement either global theorem.
