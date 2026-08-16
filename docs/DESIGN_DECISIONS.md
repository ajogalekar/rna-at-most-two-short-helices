# Representation and architecture decisions

This document was written before the foundational representation was implemented.
The mathematical specification is `CANONICAL_PROOF.md`; implementation convenience
does not override it.

## Representations considered

### 1. Normalized arcs with matching and noncrossing proofs

An arc is a pair of positions in `Fin n` whose left endpoint is strictly less
than its right endpoint. A structure is a finite set of arcs together with the
facts that distinct arcs share no endpoint and that no two arcs interleave.

This is the public representation. It is definitionally broad enough to contain
every noncrossing partial matching on the finite ordered backbone, including the
empty matching and matchings with adjacent paired positions. It states the
scientific model directly and makes the quantifier over competitors in
`UniqueDesigns` unambiguous.

The representation is finite and decidable. This makes exhaustive checks on
small backbones possible. It is less convenient for structural recursion than
an inductive tree, so the interval tree is derived from it.

### 2. Motzkin or dot-bracket words

A well-formed dot-bracket word gives a compact executable encoding of a
noncrossing partial matching. It would make parsing, enumeration, and examples
pleasant. However, making it the public type would put a grammar between the
theorem and the manuscript's direct definition. It would require a proved
bijection with all normalized noncrossing partial matchings before it could be
used in the public theorem.

Milestone 1 therefore does not use dot-bracket words as the public structure.
Human-readable strings such as `(())` are only names for explicitly constructed
matching-based examples. A future parser is optional and would need a proved
soundness/completeness theorem.

### 3. Ordered interval trees or forests

The interval tree is ideal for the motif degree, children, loop nodes, later
colouring recursion, and subtree induction. Used alone as the public type,
though, an inductive tree could silently exclude valid partial matchings or add
extra well-formedness conditions.

Milestone 1 derives a virtual-root interval tree from each matching-based
`SecondaryStructure`. Its nodes are exactly the target arcs and the target's
unmatched positions, plus one virtual root. The parent relation is the unique
smallest enclosing paired interval, or the root when no target pair encloses the
node. Children are ordered by their first backbone position. Thus no converse
tree-to-matching equivalence is needed for the public theorem: the tree is a
function of the already-public matching rather than a replacement for it.

## Chosen interface

- Public theorem interface: arbitrary matching-based `SecondaryStructure n`.
- Internal structural view: interval nodes and parent/child relations derived
  from a `SecondaryStructure n`.
- Helices: canonical maximal stacked runs in the original arc set, not arbitrary
  tree paths or arbitrary subchains.
- Competitors: every matching-based `SecondaryStructure n` compatible with the
  same complete sequence.

The full theorem proposition therefore quantifies over the original model. No
ordered-tree inhabitant, parser output, fixed topology, or saturated skeleton
appears in that quantifier.

## Consequences for later work

### Decidability

The backbone, nucleotide alphabet, normalized arcs, finite arc sets, node sets,
parent relation, helix descriptors, motif predicates, compatibility, and target
class are finite or propositionally decidable. This supports kernel-checked
exhaustion for the four-position examples.

### Recursion and colouring

Tree recursion is not implemented in Milestone 1. A later milestone may recurse
over a well-founded measure such as the number of descendant target pairs. It
must recurse on the tree derived from the public matching and prove that child
subtrees are smaller and disjoint.

### Helices

Helices are identified by an outer arc and a positive length. Membership
requires every exact stacked offset to occur, while maximality independently
forbids both an outward and an inward continuation in the target. This gives a
canonical object suitable for counting and prevents counting shorter subruns of
one maximal helix.

### Deletion and compression

The later no-tie argument deletes a common set of unpaired positions and
compresses the remaining ordered backbone. With `Fin n`, this will require an
explicit order-preserving equivalence between retained positions and a smaller
`Fin m`, plus proofs that arcs, noncrossingness, compatibility, and derived
paired parent-child relations are preserved. This work is deliberately deferred.

### Sequence indexing

Lean uses zero-based `Fin n`; the manuscript uses `[n] = {1, ..., n}`. The
translation is:

| Manuscript | Lean |
|---|---|
| position `k`, where `1 <= k <= n` | `i : Fin n` with `i.val = k - 1` |
| Lean position `i` | manuscript position `i.val + 1` |
| pair `(i,j)` | arc endpoints with values `(i-1,j-1)` |
| adjacent pair `(k,k+1)` | endpoint values `k-1` and `k` |
| virtual root `[0,n+1]` | a sentinel node, not two `Fin n` positions |

No minimum hairpin distance is introduced by this translation.
