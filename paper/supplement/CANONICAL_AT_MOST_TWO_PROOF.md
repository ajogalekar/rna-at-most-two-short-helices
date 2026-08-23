# Canonical proof specification: at most two length-two helices

Status: this document specifies the proof to be reconstructed in Lean. Until
`atMostTwoShortHelixDesignability` compiles and its axiom audit is clean,
unique designability below is the intended corollary, not a machine-checked
claim of this downstream repository.

## 1. Locked model and theorem

The public RNA model is inherited without modification from frozen commit
`c37eac40ef5a28bf5733fd576ce6d4c44091ee6a`. A competitor is any compatible,
noncrossing partial matching on the same complete four-letter sequence. The
only complementary pairs are Watson--Crick A--U and G--C pairs. Adjacent pairs
remain permitted. Energy is minus pair count, and `UniqueDesigns` forbids ties.

For a target `T`, let `k(T)` be the number of maximal helices of length two.
The new target predicate states exactly:

1. `k(T) <= 2`;
2. no maximal helix has length one;
3. each maximal helix whose length is not two has length at least three;
4. `T` has no `m5` motif; and
5. `T` has no `m3dot` motif.

The intended final theorem is

```lean
forall {n : Nat} (T : SecondaryStructure n),
  InTargetClassKLeTwo T -> exists w : Sequence n, UniqueDesigns w T
```

The single resource induction below covers short count zero, one, and two. It
must not invoke separate zero-short, one-short, or exact-two designability
theorems. The all-unpaired target is included and is the root-degree-zero base
case.

## 2. Short-resource accounting

`lengthTwoHelices T` is the finite set of all maximal helices `H` satisfying
`H.length = 2`, and `shortHelixCount T` is its cardinality. For a maximal helix
`H`, `s(H)` is the number of length-two maximal helices whose heads lie in
`pairedHelixSubtree T H`. Using the exact maximal-helix partition,

```text
s(H) = indicator(H.length = 2) + sum_K s(K),
```

where `K` ranges over the actual ordered outgoing child helices of `H`.
Consequently every child count is at most its parent count. In the target
class every subtree has count at most two, and at most two outgoing child
subtrees have positive count. If two child subtrees have positive count, then
`H` itself is not short; the target-class length clauses therefore give
`3 <= H.length`. The same support-cardinality bound holds for actual root
children.

## 3. Interfaces F and Q

Fix a residue `xi` and write `eta = xi.opposite`. An interface records the
entry residue and the first helix color. Define

```text
F = {xi-B, xi-W, eta-B, eta-W, eta-G}
Q = {xi-B, xi-W,                 eta-G}.
```

Equivalently, `InF xi entry first` is existing admissibility at `entry` with
gray residue `eta`, while

```text
InQ xi entry first :=
  (entry = xi and first is non-gray) or
  (entry = eta and first = gray).
```

Then `Q` is a subset of `F`. At `xi`, both sets allow black and white and
forbid gray. At `eta`, `F` allows all three colors and `Q` only gray. Every Q
interface satisfies the old local `Safe` condition for an allowed helix;
every F interface satisfies it when the helix is long.

The required resource interface for subtree `H` is F if `s(H)=0`, and Q if
`s(H)>0`.

## 4. Extension-stable acceptance invariant

`AcceptsInterface T H xi entry first` means there is an exact-domain partial
coloring of the complete helix subtree at `H` whose certificate remains true
under every total coloring extending that partial coloring. It records:

- the actual entry residue and actual first color;
- proper exposure at every paired node in the subtree;
- every gray pair at `eta`;
- every target-unpaired position at `xi`;
- exact agreement between actual child heads and assigned ports; and
- the required terminal residue and any strengthened close property.

The induction invariant proves only guaranteed inclusions:

```text
s(H) = 0                 -> every F interface is accepted;
1 <= s(H) and s(H) <= 2  -> every Q interface is accepted.
```

It does not claim equality between the full accepted-interface relation and
F or Q, and it has no logical dependency on the Python automaton.

The gluing invariant is explicit. The parent helix-member domain is disjoint
from every outgoing child subtree domain; child domains are pairwise disjoint;
and their union is exactly the parent helix subtree. Each child certificate
preserves its assigned first color, so the parent sees precisely the proved
port multiset. This actual parent exposure is the sole common interface among
siblings. A root-to-node ancestor path inside one child subtree cannot enter a
different sibling subtree, so extending or changing a sibling does not change
the first child's paired or unpaired levels. Parent local properness together
with all child certificates therefore yields global properness, gray parity,
unpaired parity, and strong two-separation throughout the assembled subtree.

## 5. Helix transfers

For a helix with `H.length = 2` or `3 <= H.length`, an old-style `Safe`
interface transfers to either requested exit: use `twoPairTransferOfSafe` at
length two and the existing long-transfer theorem at length at least three.

One additive strengthening is needed. For `3 <= h` and a Q interface, build a
transfer that exits at `eta` and also closes non-gray. Because the existing
`LocalTransfer.closesNonGrey` field is conditional on exiting at
`eta.opposite`, this strengthened fact must be returned separately and bridged
to the installed actual terminal color.

Choose a deterministic non-gray `a`: retain the prescribed non-gray first
color at a `xi` entry; at an `eta` entry, whose prescribed first color is gray,
choose black (or white only where a fixed first-color constraint requires it).
Use these four words directly:

```text
xi entry,  non-gray first, odd h:   a^h
xi entry,  non-gray first, even h:  a G a^(h-2)
eta entry, gray first,     odd h:   G a^(h-1)
eta entry, gray first,     even h:  G G a^(h-2)
```

Prove preservation of the first color, length, internal properness, all grays
at eta, eta exit, and non-gray close. Treat `h=3`, `h=4`, odd `h>=5`, and even
`h>=6` explicitly. In particular, do not state that the exact transition
relation at `h=4` equals the stabilized larger-even relation. Kernel-checked
examples include `GBB`, `GWW`, the even `h=4` word, and xi-entry odd and even
words.

## 6. M-loop resource allocation

Let `r` be the number of actual outgoing child subtrees with positive short
count. The accounting lemma gives `r <= 2`. An M terminal has paired-child
degree two or three.

For `r=0`, use the ordinary rows:

```text
close B: d=2 -> B,G       d=3 -> B,G,G
close W: d=2 -> W,G       d=3 -> W,G,G
close G: d=2 -> B,W       d=3 -> B,W,G
```

For `r=1`, give the unique positive child gray and fill the remaining slots:

```text
close B: d=2 -> G,B       d=3 -> G,B,G
close W: d=2 -> G,W       d=3 -> G,W,G
close G: d=2 -> G,B       d=3 -> G,B,W
```

The displayed order is schematic: the gray is installed at the actual unique
positive slot and fillers are installed deterministically at the remaining
ordered slots.

For `r=2`, the incoming helix is long. Request the strengthened eta-exit
transfer, whose actual closing color `a` is black or white. Give both actual
positive children gray. At degree three give the remaining short-free child
`a`. Thus the actual exposure is a permutation of `W,G,G` or `W,G,G,B`, or
the black/white-swapped counterpart. It has at most one black, at most one
white, and at most two gray colors.

Every positive child receives eta-gray, hence Q. Every remaining child is
short-free and receives an F port. The theorem returns a function on actual
ordered child slots; no overwrite-based map is permitted.

E has no outgoing child. L exits at xi and closes non-gray; its optional child
receives the same non-gray color at xi, which belongs to both F and Q.

## 7. Root allocation

If root degree is zero, choose `xi=0`, the empty coloring, and prove root
properness, zero level for every root-unpaired position, absence of gray pairs,
and strong two-separation. This explicitly covers the all-unpaired target.

If the root has an unpaired child, motif-freeness bounds paired degree by two;
choose `xi=0` and use B for degree one and B,W for degree two. Use the same
rows when there is no root-unpaired child and degree is at most two.

With no root-unpaired child and degree three or four, choose `eta=0` and
`xi=1`. Give every positive-short child gray and fill actual remaining slots:

```text
d=3: r=0 -> B,W,G   r=1 -> G,B,W   r=2 -> G,G,B
d=4: r=0 -> B,W,G,G r=1 -> G,B,W,G r=2 -> G,G,B,W.
```

Again these are multiset rows installed at actual positive slots followed by
deterministic filling of remaining ordered slots. Positive children receive Q;
short-free children receive F; each actual root exposure is proper.

## 8. Well-founded construction and global theorem

Recurse on the existing exact measure `helixSubtreePairCount T H`. At each
helix, classify E/L/M, obtain the actual positive-child support and its bound,
select the requested exit, choose the ordinary transfer except at M with
`r=2`, allocate actual ports, recurse on every actual child with its required
F/Q proof, and assemble via the exact disjoint subtree machinery. The existing
strict decrease theorem justifies every recursive call.

At the virtual root, use the direct degree-zero base or the resource-aware root
allocation. Merge root-child subtree assignments using the root partition and
derive a total proper coloring with witness residue `xi`. Root-unpaired nodes
are handled explicitly at level zero. Gray pairs lie at `xi.opposite` and all
target-unpaired positions lie at `xi`, yielding strong two-separation.

Finally derive ordinary separation, use the existing deterministic
`sequenceOfProperColoring`, and apply the already kernel-checked generic no-tie
theorem. Exact-two, old exact-one, all-long, and all-unpaired statements are
corollaries of this one new construction; none is a premise of it.

## 9. Excluded claims

The proof does not formalize the frozen legacy policy, the claimed `n=26`
minimum, its compression lemma, finite K2 enumeration counts, exact automaton
fixed-point equality, or any Python certificate. These remain external
diagnostic artifacts and have no logical role in the Lean theorem.
