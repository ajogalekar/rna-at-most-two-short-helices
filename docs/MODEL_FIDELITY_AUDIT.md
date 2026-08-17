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

## Milestone 2 local-colouring fidelity

Milestone 2 leaves every public scientific definition from Milestone 1
unchanged.  In particular, `SecondaryStructure`, `UniqueDesigns`,
`InTargetClassK`, and `OneShortHelixDesignabilityStatement` retain the same
types and definitions.

### Do maximal helices now cover every target pair?

Yes.  Coverage starts from an arbitrary proof `a ∈ T.arcs`, extends only exact
consecutive target segments containing `a`, and produces a maximal run.
Common-member uniqueness then gives exactly one such run.  The finite union of
all `helixMembers` is proved equal to `T.arcs`, and distinct maximal helices
have disjoint member sets.  This is a theorem about the original target arc
set; it is not a new helix-first target representation.

### Can a non-target arc or unpaired position be coloured?

No.  `Coloring T` has domain `PairedNode T`, whose values carry proofs of
membership in `T.arcs`.  The virtual root and `UnpairedPosition T` are absent
from that domain.  Root and unpaired levels exist, but neither object receives
a colour.

### Are levels exact integers or only parity labels?

Exact integers.  A paired entry level sums signed `Color.delta` values over its
strict target-pair ancestors, and its inclusive level adds its own delta.  The
ancestor set is proved to decompose at the existing computed interval-tree
parent.  An unpaired node takes that same parent-interface integer level.
Only `levelParity : Int -> ZMod 2` forgets information, and it is used solely
for strong two-separation and local transfer.

### Does local helix transfer describe real target levels?

Yes.  The local construction is first proved for a finite colour word because
its residue walk is independent of target geometry.  A separate load-bearing
bridge restricts an actual `Coloring T` to the canonical ordered members of an
actual `MaximalHelix T` and proves at every offset that the local running
residue equals the parity of the global inclusive integer level.  Terminal and
grey-placement facts are corollaries of this pointwise identification.

### Are allocation rows only anonymous multisets?

No.  Each table row is a finite function on ordered slots.  Actual paired
children are sorted in backbone order and indexed by those slots.  Designated
rows move a grey occurrence to the actual short child's slot while preserving
the row multiset.  Each loop/root child is connected to the unique maximal
helix whose head it is, so long-child and unique-short-child obligations refer
to the global class-K helices.

### What was deliberately unproved at the end of Milestone 2?

Milestone 2 stopped before the global recursive `COLOR` construction. It also
left the color-to-nucleotide assignment, cancellation/free-group argument,
saturated uniqueness theorem, prefix-balance argument, no-tie theorem, and
final designability proof for later milestones. Milestone 3 has now discharged
only the first of those deferred obligations.

## Milestone 3 global-colouring fidelity

Milestone 3 again leaves every public scientific definition from Milestone 1
unchanged. In particular, `SecondaryStructure`, `Coloring`, `ProperColoring`,
the exact integer level functions, `StrongTwoSeparated`, `InTargetClassK`,
`UniqueDesigns`, and `OneShortHelixDesignabilityStatement` retain their prior
meanings.

### Does the construction color every target pair exactly once?

Yes. A recursive `SubtreeColoring H` has the exact domain
`pairedHelixSubtree T H`. The local helix members and outgoing child domains
are proved disjoint before assembly, and distinct outgoing child subtrees are
proved pairwise disjoint. At the virtual root, root-child helix subtrees are
pairwise disjoint and their union is all of `PairedNode T`. Totalization
therefore has neither an arbitrary default on target pairs nor a
last-update-wins overlap convention.

### Can arbitrary colors outside a subtree affect its certificate?

No. `SubtreeCertificate.sound` quantifies over every total coloring extending
the exact-domain partial assignment and assumes only the indexed residue at
the subtree entry. Internal exposure is derived from the installed local word
and the actual helix-chain geometry. Terminal exposure is derived from the
actual child-head colors and the proved loop allocation. The certificate does
not assume global properness.

### Is the recursion genuinely structural and terminating?

Yes. `helixSubtreePairCount T H` is the cardinality of the actual paired helix
subtree. Every outgoing child's subtree is a strict subset, and
`helixSubtreePairCount_outgoing_lt` supplies the termination proof for each
recursive call. The construction does not enumerate global colorings.

### Are properness and separation proved with the existing global notions?

Yes. `assembledRootColoring_proper` proves `ProperExposure` at the virtual root
and every actual paired node using the existing `exposedMultiset` definition.
`assembledRootColoring_strongTwoSeparatedWith` uses the existing exact
`pairedLevel` and `unpairedLevel`, applying `levelParity` only at the final
residue comparison. Root-unpaired positions are handled explicitly through
their exact integer level zero and the root-allocation coverage theorem.

### What exact manuscript result is now implemented?

`targetClass_admits_proper_strongTwoSeparated` states that every original
matching-based target satisfying `InTargetClassK` admits one total
`Coloring T` that is both `ProperColoring` and `StrongTwoSeparated`. This is
Theorem 12 of `CANONICAL_PROOF.md`. It does not narrow targets to a parsed word
or an inductively generated tree and does not yet imply `UniqueDesigns`.

### What remains deliberately unproved after Milestone 3?

No color-to-nucleotide assignment, pairing-inventory theorem,
cancellation/free-group argument, saturated uniqueness theorem, prefix-balance
argument, no-tie theorem, or final designability proof is introduced in
Milestone 3. The exact final designability proposition remains unchanged and
unproved.

## Milestone 4 sequence, inventory, and balance fidelity

Milestone 4 leaves every public scientific definition from the preceding
milestones unchanged. In particular, `Sequence`, `SecondaryStructure`,
`StructureCompatible`, `pairCount`, the exact integer level functions,
`InTargetClassK`, `UniqueDesigns`, and
`OneShortHelixDesignabilityStatement` retain their established meanings.
Milestone 4 adds constructors, certificates, and theorems over those definitions;
it does not replace them with a restricted sequence or competitor model.

### Is one complete sequence constructed and retained throughout?

Yes. `sequenceOfProperColoring` uses the exact position-role partition to assign
one nucleotide to every element of `Fin n`, producing a complete `Sequence n`
without a default arc or an unassigned position. For a class-K target,
`globalSequenceCertificate` retains the Milestone 3 coloring certificate and
stores exactly one derived sequence. Its compatibility, local distinctness,
inventory, maximum-pair, equality-case, prefix-level, and obstruction fields all
refer to that same stored sequence; no theorem independently chooses a different
sequence witness.

### Do the target and every competitor use that same sequence?

Yes. The target-compatibility field is `StructureCompatible sequence T`, while
the maximum-pair, equality-saturation, and target-unpaired obstruction fields
quantify `S : SecondaryStructure n` and assume
`StructureCompatible sequence S` with the identical stored `sequence`. The
standalone maximum theorem likewise binds one `w : Sequence n` and uses it for
both `T` and every competitor.

### Are all matching-based competitors still quantified?

Yes. The competitor quantifier remains
`forall S : SecondaryStructure n`. It therefore ranges over every finite
noncrossing partial matching on the same `Fin n`, not merely structures sharing
the target tree, helices, paired positions, pair count, or topology. No
competitor is generated from the target or filtered by a target-derived grammar.

### What optimality result is proved, and are ties excluded?

Milestone 4 proves that the constructed target is compatible and has maximum
pair count: every compatible `S : SecondaryStructure n` satisfies
`pairCount S <= pairCount T`. This is the exact maximum-base-pair claim in the
fixed Watson--Crick model. Equality is deliberately still permitted. Neither the
maximum theorem nor `GlobalSequenceCertificate` asserts that a tying competitor
equals `T`.

### Is the nucleotide inventory exact, including its equality case?

Yes. The position-role equivalence prevents hidden nucleotide sources. For a
coloring with `g` grey target pairs, `q` non-grey target pairs, and `u`
target-unpaired positions, the constructed sequence proves exactly
`#U = g`, `#G = q`, `#C = q`, and `#A = g + u`. The arbitrary-compatible-fold
injection sends every competitor arc to a distinct limiting `U` or `C` position,
giving the universal upper bound. If a competitor ties the target pair count,
the proved equality case states that every `U`, every `C`, and every `G` position
of this same complete sequence is paired. It does not silently strengthen that
conclusion to equality of structures.

### Is prefix-balance indexing faithful to the manuscript?

Yes. Lean positions remain zero-indexed `Fin n`. The primary boundary function
uses `Fin (n + 1)` and sums positions `j` with `j.val < k.val`; boundary zero is
the empty prefix. The inclusive wrapper at `i : Fin n` uses the boundary after
`i`, whose value is `i.val + 1`. Thus manuscript position `k` corresponds to
Lean position value `k - 1`, and manuscript `Lambda(k)` is exactly
`prefixBalanceAt` at that Lean position. Strict-interval subtraction is proved
with the endpoint convention used by the imbalance argument, avoiding a hidden
off-by-one change.

The level correspondence uses the existing exact `pairedLevel` and
`unpairedLevel`, not parity or a surrogate level: paired left endpoints equal
their inclusive paired levels, target-unpaired positions equal their unpaired
levels, and a grey right endpoint has the same balance as its left endpoint and
grey paired level. Complete target subtrees and completed earlier sibling
subtrees are proved to have zero net `G`-minus-`C` balance.

### Is the noncrossing imbalance obstruction universal?

Yes. For an arbitrary compatible `S : SecondaryStructure n`, any A--U arc of
`S` whose endpoint prefix balances differ forces an explicit `G` or `C` position
to be unpaired in `S`. Interior closure is derived from the actual
`SecondaryStructure.isNoncrossing` and partial-matching properties, including
the shared-endpoint boundary cases; it is not a target-specific picture or a
finite enumeration. With ordinary exact-level separation, the same universal
argument proves that if `S` pairs a target-unpaired position, then `S` leaves an
explicit `G` or `C` position unpaired.

### What remains deliberately deferred to Milestone 5?

Milestone 4 does not claim the no-tie theorem, `UniqueDesigns`, or
`OneShortHelixDesignabilityStatement`. The following work remains deferred:

- adjacent complementary deletion and its preservation lemmas;
- free-group and suffix-cancellation machinery;
- saturable prefixes, atomic words, atomic designs, and their concatenation or
  wrapping results;
- saturated-skeleton/local-distinctness uniqueness;
- proving equality of the target and competitor unpaired-position sets in the
  tie case;
- deletion and order-preserving compression of common unpaired positions;
- the universal no-tie theorem;
- the final `UniqueDesigns` and one-short-helix designability theorems.

Accordingly, Milestone 4 establishes maximum pair count and the exact machinery
needed to exclude ties later, but makes no uniqueness or final-designability
claim.
