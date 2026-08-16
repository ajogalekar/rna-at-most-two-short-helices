# Model-fidelity audit

## Plain-language restatement of the Lean model

For a fixed natural number `n`, the backbone positions are the ordered finite
type `Fin n`. A sequence is one jointly chosen nucleotide at every position.
The only nucleotides are A, C, G, and U. A pair is compatible exactly when its
right letter is the fixed Watson–Crick complement of its left letter: A–U,
U–A, C–G, or G–C.

An arc contains two distinct positions in increasing order. A secondary
structure is an arbitrary finite set of such arcs with two proofs: no position
is an endpoint of two distinct arcs, and no two arcs interleave. No additional
grammar, topology, saturation condition, or minimum loop length is imposed.

Compatibility of a structure with a sequence checks every target arc against
the sequence at that arc's two endpoints. `pairCount` is the number of arcs and
`energy w S` is the integer `-(pairCount S)`.

`UniqueDesigns w T` says both:

1. `T` is compatible with the complete sequence `w`; and
2. every distinct secondary structure `S` on the same `Fin n` and compatible
   with that same complete `w` has strictly fewer pairs than `T`.

The interval tree is derived after the matching is fixed. Its virtual root is a
sentinel, not a target pair. Its paired nodes are exactly the target arcs, and
its unpaired nodes are exactly positions incident to no target arc. The parent
is the unique smallest enclosing target pair, or the root if no pair encloses
the node. Paired degree counts paired children plus the parent incidence for a
nonroot pair; unpaired children never add to paired degree.

A maximal helix is an exact positive stacked run. Every required offset pair
must occur; an outward stacked predecessor and the next inward offset must both
be absent. Maximal helices with a common target pair are proved equal, so
distinct maximal helices have disjoint pair sets.

`InTargetClassK` explicitly selects one length-two maximal helix, proves every
length-two maximal helix equals it, forbids length one, requires every other
maximal helix to have length at least three, and negates both forbidden motif
predicates.

## Required questions

### Does a target begin as a shape without nucleotide identities?

Yes. `SecondaryStructure n` contains positions, arcs, and matching/noncrossing
proofs only. It contains no `Nucleotide` field.

### Are all sequence letters chosen jointly?

Yes. A witness has type `Sequence n`, definitionally `Fin n -> Nucleotide`, so
it assigns a letter to every position in one complete function.

### Do all competitors use the same sequence?

Yes. The single `w` bound by `UniqueDesigns w T` is passed unchanged to
`StructureCompatible w S` for every competitor `S`.

### Are all noncrossing partial matchings considered?

Yes. The competitor quantifier is `forall S : SecondaryStructure n`. That
public type is a raw finite arc set with exactly the partial-matching and
noncrossing requirements. It is not constructed from the target's interval
tree, stems, pair count, or topology.

### Are ties ruled out?

Yes. Every distinct compatible `S` must satisfy
`pairCount S < pairCount T`. The proved equivalent formulation separately says
that `T` is maximum-cardinality and equality in pair count implies `S = T`.
The checked `AUAU` example is rejected precisely because `()()` ties `(())`.

### Are adjacent pairs allowed?

Yes. An arc requires only `left < right`; it has no distance constraint. The
checked two-position example contains the adjacent arc with Lean endpoints
`0,1`, corresponding to manuscript positions `1,2`.

### Are pseudoknots excluded?

Yes. `IsNoncrossing` prohibits either strict interleaving orientation for every
two target arcs. Nesting and disjointness remain allowed.

### Are G–U pairs excluded?

Yes. Compatibility is equality with `comp`; `comp G = C` and `comp U = A`.
The four-pair characterization proves that only A–U, U–A, C–G, and G–C occur.

### Is the energy exactly minus pair count?

Yes. `energy w S = -(pairCount S : Int)` definitionally. The sequence argument
is present to match `E(w,S)` and is intentionally unused because this model
assigns the same energy to every compatible pair type. Lean proves that lower
energy is equivalent to greater pair count and that unique minimum energy is
equivalent to compatible unique maximum pair count.

## Public-theorem quantifier audit

`OneShortHelixDesignabilityStatement` starts with
`forall {n} (T : SecondaryStructure n)`. Neither its target nor its competitors
are quantified through an interval-tree or helix-tree type. The derived tree is
used only to define the target-class predicate on the already matching-based
`T`. Therefore the public statement has not narrowed the manuscript's class of
noncrossing partial matchings.
