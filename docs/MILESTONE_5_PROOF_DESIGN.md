# Milestone 5 proof design

This document fixes the implementation architecture before the Milestone 5
proof modules are written.  The public model remains
`Sequence n = Fin n -> Nucleotide` and `SecondaryStructure n`; the auxiliary
representations below are bridges, not replacements for that model.

## 1. Finite words and subwords

### Alternative A: `List Nucleotide`

A list has native length, empty word, append, `take`, `drop`, prefixes,
suffixes, and one-letter wrapping.  Its exact public-sequence view is

```lean
wordSequence (z : List Nucleotide) : Sequence z.length := z.get
```

so conversion does not choose, pad, truncate, or alter a nucleotide.  Every
matching on a word is still an ordinary `SecondaryStructure z.length`.
Restrictions, concatenations, and wrapping use explicit strictly monotone
maps between the corresponding `Fin` backbones and map every arc in both
directions when an order equivalence is available.

The main cost is dependent length arithmetic while shifting and joining
structures.  This cost is localized in reusable transport operations.  It is
smaller than continually rebuilding list operations on functions.

### Alternative B: length-indexed vectors or `Fin n -> Nucleotide`

This keeps every intermediate word in the public index type.  It makes a
single nucleotide lookup immediate, but prefix, suffix, append, insertion,
deletion, and wrapping all change indices and therefore require casts and
explicit reindexing even before a matching is considered.  `Vector` also
ultimately exposes list operations through an equality of lengths.  The
free-group reduction used for Lemma 15 is list-based, so this alternative
would additionally require repeated vector/list conversions.

### Choice

Milestone 5 uses **Alternative A**, with

```lean
abbrev Word := List Nucleotide
```

internally.  The bridge theorem for every `i : Fin z.length` is definitionally
`wordSequence z i = z.get i`.  `SaturatedStructure S` means that every member
of `Fin n` is incident to an arc of the existing structure, and

```lean
Saturable z :=
  exists S : SecondaryStructure z.length,
    StructureCompatible (wordSequence z) S /\ SaturatedStructure S
```

Thus the internal word representation does not restrict the competitor set:
all compatible noncrossing perfect matchings in the public matching model are
quantified over.

## 2. Adjacent cancellation

The cancellation proof uses Mathlib's `FreeGroup (Fin 2)`, not a new group
implementation.  Nucleotides are encoded as signed generators:

```text
A -> (0,true)    U -> (0,false)
C -> (1,true)    G -> (1,false)
```

Complementation toggles exactly the Boolean sign.  Mathlib's
`FreeGroup.Red.Step` is deletion of adjacent inverse symbols and
`FreeGroup.Red` is its reflexive-transitive closure.  The project relation
`DeletesComplementaryPair` is stated on nucleotide lists and is proved to map
exactly to `FreeGroup.Red.Step`; the nucleotide encoding is injective, so the
map also reflects steps and histories.

The matching side of
`saturable_iff_reducesToEmpty` is independent of coloring and class K.
Forward induction selects a minimum-span arc, proves it adjacent using
saturation and noncrossingness, deletes its endpoints, and transports every
remaining arc through the order isomorphism of the complement.  Reverse
induction reinserts the deleted adjacent complementary positions, transports
the shorter matching, and adds the adjacent arc.  Strict monotonicity proves
that compatibility, partial matching, noncrossingness, and saturation are
preserved.

Mathlib's quotient characterization (`FreeGroup.Red.exact`), together with
the fact that the empty word cannot reduce further, then gives

```text
Saturable z <-> encodedProduct z = 1.
```

`FreeGroup.mul_mk` gives the append law.  The suffix theorem is the group
calculation

```text
Phi(x ++ y) = Phi(x) * Phi(y),  Phi(x ++ y) = 1,  Phi(x) = 1
```

and hence `Phi(y) = 1`, followed by the characterization.  No finite
enumeration is used.

## 3. Atomic blocks

An atomic word is explicitly nonempty, saturable, and has no saturable prefix
of length `k` with `1 <= k < z.length`.  An atomic design packages a word, a
target `SecondaryStructure z.length`, target saturation and compatibility,
and uniqueness against **every** compatible saturated secondary structure on
that word.

Lists of dependently sized atomic-design blocks are packaged as records.  The
concatenated word is `flatMap` of their words; the concatenated target maps
each target arc through its block offset.  Wrapping maps all child arcs
through the one-position shift and adds the outer arc.  These constructors
come with membership and restriction characterizations, so later proofs do
not appeal informally to an isolated block.

Lemma 16 uses interval restriction at the partner of the first position and
the suffix-cancellation theorem.  Lemmas 17 and 18 follow the manuscript's
leftmost-bad-block and shortest-prefix arguments.  All block offsets are
natural-number sums exposed through the package API, including the empty
prefix of blocks in Lemma 18.

Theorem 19 is proved over the actual saturated target interval tree.  Each
paired child supplies its exact closed-interval subword and restricted target.
Saturation proves that the parent's interior is precisely the consecutive
concatenation of these child blocks.  Induction turns children into atomic
designs; Lemma 18 handles a paired node and Lemma 17 handles the virtual root.
The empty saturated target is handled separately.

## 4. Restriction to the target-paired skeleton

### Alternative A: explicit compression to `Fin m`

Let

```text
retained(T) = { i : Fin n | T.positionPaired i }.
```

Its filtered `Finset` has cardinality `m`.  Mathlib's
`Finset.orderIsoOfFin` supplies an increasing equivalence

```text
Fin m ~=o retained(T).
```

The forward map embeds compressed positions in the original backbone; the
inverse ranks retained positions.  The restricted sequence is composition
with the forward map.  A structure whose every arc endpoint is retained is
compressed by mapping both endpoints through the inverse; conversely a
compressed arc lifts through the forward map.

This makes order preservation a named theorem.  Arc membership is an exact
if-and-only-if, from which partial matching, noncrossingness, compatibility,
pair count, saturation, and faithful lifting are proved.

### Alternative B: stay on the retained ordered subtype

The retained subtype already carries the correct order and avoids choosing a
rank.  However, the project's `Arc`, `SecondaryStructure`, interval-tree
nodes, `LocallyDistinct`, and saturated-uniqueness conclusion are all indexed
specifically by `Fin n`.  Using the subtype throughout would require a second
generic matching and tree hierarchy plus a final equivalence theorem.  That
duplicates more trusted surface than explicit compression and obscures the
public competitor model.

### Choice

Milestone 5 uses **Alternative A**.  The retained set is determined only by
the target.  In the tied-competitor application, a separate theorem first
proves that target and competitor have exactly the same unpaired set, so every
arc of both structures has retained endpoints.

The target-tree preservation proof uses the independent `IsParent`
specification already present in `RNA.IntervalTree`, rather than unfolding the
executable maximum operation.  Strict containment is reflected by the order
equivalence.  Therefore enclosing arcs, paired parent-child relations, root
children, and child order are preserved and reflected.  These equivalences
transfer `LocallyDistinct` to the compressed target.  Exact arc-membership
reflection proves that equality after compression lifts to equality before
compression when all deleted positions are unpaired in both structures.

## 5. No-tie dependency chain

For a proper separated coloring and its existing deterministic sequence, the
general theorem uses the following chain without a class-K hypothesis:

1. `equality_uses_all_limiting_nucleotides` pairs every `U`, `C`, and `G` in a
   tied competitor.
2. `targetUnpaired_pairing_obstruction` contradicts that equality case if a
   target-unpaired position is paired by the competitor.
3. An explicit endpoint equivalence shows that a structure has
   `n - 2 * pairCount` unpaired positions.
4. Inclusion plus equal finite cardinality gives equality of unpaired sets.
5. Both structures are compressed along the common retained set.
6. The restrictions are compatible noncrossing saturated structures on the
   same restricted word, and target local distinctness transfers.
7. The saturated local-distinctness theorem makes the restrictions equal.
8. Faithful lifting gives equality of the original structures.

The strict unique-design theorem then combines target compatibility, the
Milestone 4 universal pair-count upper bound, and this equality case.  The
class-K theorem instantiates it with exactly
`globalSequenceCertificate hK`; no new sequence witness is selected.

## 6. Kernel and model checks

All new source files continue to set `autoImplicit` to false.  The proof uses
only Lean/Mathlib definitions, explicit finite equivalences, and classical
choice from previously proved existence.  It does not invoke an external RNA
theorem, a solver, enumeration, `unsafe`, a custom axiom, or a placeholder.
The final public theorem remains a proof of the unchanged
`OneShortHelixDesignabilityStatement` over arbitrary compatible noncrossing
partial matchings on one shared complete sequence.
