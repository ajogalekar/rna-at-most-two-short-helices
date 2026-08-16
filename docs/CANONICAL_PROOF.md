# Designability of RNA targets with exactly one length-2 helix

## Abstract

Consider the four-letter Watson–Crick model in which an RNA structure is an
arbitrary noncrossing partial matching, adjacent positions may pair, the only
compatible pairs are A–U and C–G, and energy is minus the number of base pairs.
We prove that every target avoiding the motifs `m₅` and `m₃•`, with exactly one
maximal helix of length 2, no maximal helix of length 1, and every other maximal
helix of length at least 3, is uniquely designable. The proof constructs a proper
strong 2-separated colouring, converts it to a nucleotide sequence, and proves
from first principles that no distinct compatible noncrossing matching can tie
the target.

## 1. Model

Fix `n ≥ 0`. An RNA sequence is a word `w ∈ {A,C,G,U}ⁿ`. Two letters are
compatible exactly when they form one of

```text
A–U, U–A, C–G, G–C.
```

A structure on `[n]={1,…,n}` is a partial matching `P` with no crossing pairs:
there do not exist `(i,j),(k,l)∈P` with `i<k<j<l`. Adjacent positions may pair.
A structure is compatible with `w` if every matched pair contains compatible
letters. Its energy is

```text
E(w,P) = −|P|.
```

A target `T` is uniquely designable if some compatible sequence `w` makes `T`
the unique maximum-cardinality compatible noncrossing matching.

Write `comp(A)=U`, `comp(U)=A`, `comp(C)=G`, and `comp(G)=C`.

## 2. Interval tree and forbidden motifs

The interval tree `T_P` has:

- a virtual root `r=[0,n+1]`, regarded as paired;
- one paired node `[i,j]` for every `(i,j)∈P`;
- one unpaired node `[k,k]` for every unmatched position `k`;
- as children of an interval, its maximal proper subintervals in backbone order.

The paired degree `deg(v)` is the number of adjacent paired vertices, including
the parent of a nonroot paired node. If `d(v)` is the number of paired children,

```text
deg(v) = 1+d(v)  for a nonroot paired node,
deg(r) = d(r).
```

The forbidden motifs are:

- `m₅`: some node has paired degree greater than 4;
- `m₃•`: some node has an unpaired child and paired degree greater than 2.

**Lemma 1 (motif bounds).** In an `m₅`- and `m₃•`-free structure:

| node | has an unpaired child? | maximum paired children |
|---|---|---:|
| nonroot paired | yes | 1 |
| nonroot paired | no | 3 |
| root | yes | 2 |
| root | no | 4 |

*Proof.* A nonroot paired node has degree `1+d`. If it has an unpaired child,
avoidance of `m₃•` gives `1+d≤2`; otherwise avoidance of `m₅` gives `1+d≤4`.
For the root the degree is `d`, giving the two remaining bounds. ∎

## 3. Colourings, levels, and separation

Colour every nonroot paired node black `B`, white `W`, or grey `G`. Define

```text
inv(B)=W,  inv(W)=B,  inv(G)=G,
δ(B)=+1,   δ(W)=−1,   δ(G)=0.
```

For a nonroot paired node `v`, define its exposed multiset by

```text
X(v) = {inv(c(v))} ⊎ {c(u): u is a paired child of v}.
```

At the root,

```text
X(r) = {c(u): u is a paired child of r}.
```

A colouring is proper if every exposed multiset contains at most one `B`, at
most one `W`, and at most two `G` entries.

**Remark (equivalent properness rules; not used below).** The definition of
properness is equivalent to the following three rules:

1. every node has at most one black child, at most one white child, and at most
   two grey children;
2. a coloured nonroot paired node has at most one child of its own colour;
3. a black node has no white child, and a white node has no black child.

*Proof.* If `c(v)=B`, then `X(v)={W}⊎children`; the capacities say that `v` has
no white child, at most one black child, and at most two grey children. The white
case is symmetric. If `c(v)=G`, then `X(v)={G}⊎children`, so there is at most one
grey child, one black child, and one white child. At the root the exposed multiset
consists only of child colours. ∎

The level of a paired node is the inclusive path sum

```text
ℓ(v) = Σ δ(c(u)),
```

where the sum runs over the coloured nonroot paired nodes on the root-to-`v`
path; `ℓ(r)=0`. An unpaired child of a paired node `v` has level `ℓ(v)`, and an
unpaired child of the root has level 0. The entry level of a nonroot paired node is

```text
e(v)=ℓ(parent(v))=ℓ(v)−δ(c(v)).
```

A proper colouring is separated if the integer levels occupied by grey paired
nodes are disjoint from the integer levels occupied by unpaired nodes.

A proper colouring is strong 2-separated if there are residues `ξ,η∈{0,1}` with
`η=1−ξ` such that

- every unpaired node has level congruent to `ξ` modulo 2;
- every grey paired node has level congruent to `η` modulo 2.

**Lemma 3.** Every strong 2-separated colouring is separated.

*Proof.* The two level sets lie in different residue classes modulo 2. ∎

If no grey node exists, ordinary separation is vacuous. Strong 2-separation still
requires all unpaired-node levels to have one common parity.

## 4. Helices and the target class

A helix of length `h` is a maximal run

```text
(i,j),(i+1,j−1),…,(i+h−1,j−h+1).
```

**Lemma 4 (helices are chains).** Paired nodes `[i,j]` and `[i+1,j−1]` are
consecutive pairs in a helix if and only if `[i,j]` has exactly one paired child,
namely `[i+1,j−1]`, and no unpaired child.

*Proof.* In one direction there is no position between the corresponding left or
right endpoints, so `[i+1,j−1]` is the only child. Conversely, if `[i,j]` has one
paired child `[k,l]` and no unpaired child, its children must cover every position
strictly inside `(i,j)`, forcing `k=i+1` and `l=j−1`. ∎

Let `K` be the class of targets satisfying all of the following:

1. exactly one maximal helix has length 2;
2. no maximal helix has length 1;
3. every other maximal helix has length at least 3;
4. `m₅` is absent;
5. `m₃•` is absent.

## 5. Endpoint classification

Call the innermost paired node of a maximal helix a loop node.

**Lemma 5 (complete endpoint taxonomy).** Every nonroot loop node belongs to
exactly one of the following classes:

- `L`: it has at least one unpaired child and `d∈{0,1}`;
- `M`: it has no unpaired child and `d∈{2,3}`;
- `E`: it has no child at all.

The parent of the outer pair of a maximal helix is either the root, an `L` node
with `d=1`, or an `M` node. It is never an `E` node.

*Proof.* An innermost helix node cannot have no unpaired child and exactly one
paired child, because Lemma 4 would continue the same helix. If it has an
unpaired child, Lemma 1 gives `d≤1`, yielding `L`. Otherwise `d∈{0,2,3}`, yielding
`E` or `M`.

Now let `p` be the nonroot parent of the outer pair of a maximal helix. If `p`
had one paired child and no unpaired child, Lemma 4 would place `p` in that same
helix, contradicting maximality. Since `p` has a paired child, it is not `E`.
Thus it is `L` with `d=1`, or `M`. ∎

For parents of helices, call an `L` parent a `ξ`-entry interface and an `M`
parent an `η`-entry interface. The analogous root interfaces are specified below.
A terminal `E` node has no forced residue.

## 6. Forced residues

**Lemma 6.** In any proper strong 2-separated colouring:

1. an `L` loop lies at residue `ξ`; its colour and the colours of its paired
   children are non-grey;
2. an `M` loop lies at residue `η`.

*Proof.* An unpaired child of an `L` loop `v` has level `ℓ(v)`, so
`ℓ(v)≡ξ`. If `v` were grey, or if a paired child of `v` were grey, that grey node
would also lie at residue `ξ`, contradicting strong separation.

For an `M` loop, `|X(v)|=1+d(v)≥3`. A proper exposed multiset contains at most
one `B` and one `W`, so some entry is grey. If the grey entry is `inv(c(v))`, then
`c(v)=G` and `ℓ(v)=e(v)≡η`. If it is a grey child `u`, then
`ℓ(u)=ℓ(v)≡η`. ∎

Thus an `L` terminal is grey-forbidden at residue `ξ`, an `M` terminal is
grey-forcing at residue `η`, and an `E` terminal is residue-free.

## 7. Root and loop capacities

**Lemma 7 (root choices).** Let the root have `u` unpaired children and `d`
paired children. For a target in `K`, `d≥1`, and the following choices are
proper:

| condition | residue choice | child colours | interface |
|---|---|---|---|
| `u≥1`, hence `d≤2` | `ξ=0` | `B` if `d=1`; `B,W` if `d=2` | `ξ` |
| `u=0`, `d≤2` | choose `ξ=0` | `B` if `d=1`; `B,W` if `d=2` | `ξ` |
| `u=0`, `d∈{3,4}` | `η=0`, hence `ξ=1` | `B,W,G`; or `B,W,G,G` | `η` |

*Proof.* A target in `K` contains a base pair, so `d≥1`. Lemma 1 gives the stated
degree ranges. If `u≥1`, root-unpaired nodes have level 0, forcing `ξ=0`. If
`u=0` and `d≤2`, choose `ξ=0`. If `u=0` and `d≥3`, properness forces a grey child;
its level is 0, so `η=0`. Each displayed multiset respects the capacities. ∎

**Lemma 8 (sufficient nonroot allocations).** Let `a=c(v)` be the closing colour
of a loop and let `d` be its number of outgoing helices.

For an `L` loop, `a` is non-grey. If `d=0`, then `X(v)={inv(a)}` is proper. If
`d=1`, give the outgoing first pair colour `a`; then
`X(v)={inv(a),a}` is proper. The other non-grey colour would duplicate
`inv(a)`, while grey would lie at residue `ξ`, so this child colour is forced.

For an `E` loop, `X(v)={inv(a)}` is proper and there is no outgoing child.

For an `M` loop, the following child allocations are proper:

| closing `a` | `d=2` children | exposed multiset | `d=3` children | exposed multiset |
|---|---|---|---|---|
| `B` | `B,G` | `{W,B,G}` | `B,G,G` | `{W,B,G,G}` |
| `W` | `W,G` | `{B,W,G}` | `W,G,G` | `{B,W,G,G}` |
| `G` | `B,W` | `{G,B,W}` | `B,W,G` | `{G,B,W,G}` |

If one outgoing child must receive a designated grey port, assign that child
`G` and use the following colours for the other children:

| closing `a` | others for `d=2` | exposed multiset | others for `d=3` | exposed multiset |
|---|---|---|---|---|
| `B` | `B` | `{W,G,B}` | `B,G` | `{W,G,B,G}` |
| `W` | `W` | `{B,G,W}` | `W,G` | `{B,G,W,G}` |
| `G` | `B` | `{G,G,B}` | `B,W` | `{G,G,B,W}` |

The child-colour entries in both tables are multisets of ports for the actual
outgoing helices. In a designated row, give the unique length-2 child the
distinguished `G` port and assign the other displayed colours to the remaining
children in any order. In an ordinary row, all outgoing children are long and
the displayed colours may be assigned to them in any order. Every long child
accepts any displayed port that is admissible at its entry residue.

Every displayed multiset is proper. ∎

For later use, a first colour is *admissible* at entry residue `ε` if it is
non-grey, or if it is grey and `ε=η`.

**Lemma 9 (complete allocation coverage).** Suppose a terminal loop has reached
its requested construction residue, with an `L` terminal at `ξ` and a non-grey
closing colour, and an `M` terminal at `η`. Every nonroot recursive situation
arising from a target in `K` is then covered by Lemma 8, and every allocated
child port is admissible. If the child is the unique length-2 helix, the
allocation also satisfies the short-child clause of `Safe` in Section 10.

*Proof.* Lemma 5 exhausts the loop types.

- If the terminal is `E`, then `d=0`; there is no outgoing child and no allocation
  is required.
- If it is `L`, then `d∈{0,1}`. By hypothesis the terminal lies at `ξ` and its
  closing colour `a` is non-grey. For `d=0`, the singleton exposure
  `{inv(a)}` is proper. For `d=1`, Lemma 8 assigns the child colour `a`, giving
  `{inv(a),a}`. That child enters at `ξ` with a non-grey port, so the port is
  admissible whether the child helix is short or long.
- If it is `M`, then `d∈{2,3}`. By hypothesis its child interface is at `η`, and
  its closing colour lies in `{B,W,G}`. The whole target has exactly one
  length-2 helix, so the
  outgoing children include either no length-2 helix or exactly one; they can
  never include two.

When no outgoing child is short, all children are long and the six ordinary
cases are:

| closing `a` | `d` | `X(v)` | `(#B,#W,#G)` |
|---|---:|---|---|
| `B` | 2 | `{W,B,G}` | `(1,1,1)` |
| `B` | 3 | `{W,B,G,G}` | `(1,1,2)` |
| `W` | 2 | `{B,W,G}` | `(1,1,1)` |
| `W` | 3 | `{B,W,G,G}` | `(1,1,2)` |
| `G` | 2 | `{G,B,W}` | `(1,1,1)` |
| `G` | 3 | `{G,B,W,G}` | `(1,1,2)` |

Each count vector is componentwise at most `(1,1,2)`. All non-grey child ports
are admissible at any entry, and all grey ports are admissible because an `M`
child interface is at `η`.

When one outgoing child is short, assign that child the designated `G` port.
The six designated cases are:

| closing `a` | `d` | `X(v)` | `(#B,#W,#G)` |
|---|---:|---|---|
| `B` | 2 | `{W,G,B}` | `(1,1,1)` |
| `B` | 3 | `{W,G,B,G}` | `(1,1,2)` |
| `W` | 2 | `{B,G,W}` | `(1,1,1)` |
| `W` | 3 | `{B,G,W,G}` | `(1,1,2)` |
| `G` | 2 | `{G,G,B}` | `(1,0,2)` |
| `G` | 3 | `{G,G,B,W}` | `(1,1,2)` |

Again every count vector is componentwise at most `(1,1,2)`. The short child
enters at `η` with first colour `G`; every other child is long and receives an
admissible port. The case `a=G,d=2` is tight: the closing incidence and the short
child consume both grey entries, but no capacity is exceeded.

The root is not a nonroot loop allocation and is handled separately by Lemma 7.
These cases exhaust the taxonomy, both possible `M` arities, every closing
colour, and both possible short-child counts. ∎

## 8. Transfer through a long helix

The following transfer is the modulus-2 specialization of the helix-colouring
lemma in [2, Lemma 7]; a proof is included.

**Lemma 10 (long-helix transfer).** Let `H=x₁⋯x_h` be a helix of length `h≥3`,
entered at residue `ε`, meaning `e(x₁)≡ε (mod 2)`, with first colour `c₁`
satisfying

```text
c₁∈{B,W}, or c₁=G and ε=η.
```

For either requested exit residue `τ∈{ξ,η}`, meaning a requirement
`ℓ(x_h)≡τ (mod 2)`, the remaining pairs can be coloured so that:

1. every internal exposure is proper;
2. every grey pair of `H` lies at residue `η`;
3. `ℓ(x_h)≡τ (mod 2)`;
4. if `τ=ξ`, then `c(x_h)` is non-grey.

*Proof.* Fix `a∈{B,W}`. Modulo 2,

```text
δ(B)≡δ(W)≡1,
```

because `δ(B)=+1` and `δ(W)=−1`. Thus every occurrence of a repeated non-grey
colour contributes `1` modulo 2, which justifies the exit-residue counts below.
The adjacent patterns

```text
(a,a), (a,G), (G,a), (G,G)
```

give exposed multisets `{inv(a),a}`, `{inv(a),G}`, `{G,a}`, and `{G,G}`, all
proper. The pattern `(a,inv(a))` is improper.

First suppose `c₁=a`. Let `l∈{0,1}` be the inclusive residue of `x₁`, so
`l≡ε+δ(a) (mod 2)`.

- Option A colours the helix `a^h`. It is proper, contains no grey pair, has exit
  residue congruent to `ε+h` modulo 2, and closes non-grey.
- Option B colours it `a^{p−1}Ga^{h−p}`, where `p=2` if `l=η` and `p=3` if
  `l=ξ`. The inserted grey pair is at residue `η`, all adjacencies are proper,
  and its exit residue is congruent to `ε+h−1` modulo 2.

Since `h≥3`, position `p` exists. The two options have opposite exit parities.
If Option B closes grey, then `h=p=3`, `l=ξ`, and `ε=η`; its exit residue is
then `η`, not `ξ`. Hence an exit at `ξ` always has a non-grey closing pair.

Now suppose `c₁=G`. Then `ε=η`. The colouring `G^h` is proper and exits at
`η`. The colouring `G^{h−1}a` is proper, keeps every grey at `η`, exits at `ξ`,
and closes non-grey. ∎

## 9. The two-pair bridge

Let `H=x₁x₂` be a helix of length 2, entered at residue `ε` so that
`e(x₁)≡ε (mod 2)`, with requested exit residue `τ` so that
`ℓ(x₂)≡τ (mod 2)`.

**Lemma 11 (two-pair bridge).** The complete valid colour pairs are:

| `ε→τ` | valid `(c₁,c₂)` |
|---|---|
| `ξ→ξ` | `BB`, `WW` |
| `ξ→η` | `BG`, `WG` |
| `η→ξ` | `GB`, `GW` |
| `η→η` | `BB`, `WW`, `GG` |

*Proof.* The level residues satisfy

```text
ℓ(x₁)≡ε+δ(c₁)       (mod 2),
ℓ(x₂)≡ℓ(x₁)+δ(c₂)  (mod 2).
```

Require every grey occurrence to lie at `η`, require `ℓ(x₂)≡τ`, and require
`{inv(c₁),c₂}` to be proper.

- For `ξ→ξ`, the two colours have the same greyness status. `GG` would put grey
  at `ξ`; two non-grey colours must agree because `(a,inv(a))` is improper.
- For `ξ→η`, exactly one colour is grey. It cannot be first, so the possibilities
  are `BG` and `WG`.
- For `η→ξ`, exactly one colour is grey. It cannot be second, so the possibilities
  are `GB` and `GW`.
- For `η→η`, either both are grey or both are non-grey; properness gives
  `GG`, `BB`, and `WW`.

These cases exhaust `{B,W,G}²`. ∎

In the construction below, an `L` terminal requests exit `ξ`, an `M` terminal
requests exit `η`, and an `E` terminal freely requests exit `ξ`. The last choice
is convenient but not forced. In particular, a length-2 helix entered at `η` and
requested to exit at `ξ` must receive a grey first port.

Under the `Safe` construction, every length-2 helix whose terminal is an `M`
loop closes grey. At entry `ξ`, the `ξ→η` rows are `BG` and `WG`. At entry `η`,
`Safe` forces the first colour to be `G`, so the applicable `η→η` row is `GG`.
Thus grey-closing `M` terminals cannot be omitted from the construction. The
designated rows with closing colour `G` are load-bearing in the distinct
configuration where the incoming helix is long, closes grey at an `M` loop, and
the unique length-2 helix is an outgoing child. For example, a length-3 incoming
helix entered at `η` with non-grey first colour `a` and requested exit `η` uses
the row `aaG` from Lemma 10. If its `M` terminal has `d=2` and the short outgoing
child receives the designated `G` port, the tight row has
`X(v)={G,G,B}`: the closing incidence and the short-child port use both grey
slots, and the row is still proper.

## 10. Global colouring theorem

For a helix `H` with fixed first colour `c₁`, define

```text
Safe(H,ε,c₁)  iff
  [c₁∈{B,W}, or c₁=G and ε=η],
  and [|H|=2 and ε=η implies c₁=G].
```

The second conjunct is a deliberate uniform construction choice. For a
length-2 helix with transition `η→ξ`, Lemma 11 shows that a grey first port is
necessary. For `η→η`, the non-grey choices `BB` and `WW` are also valid, so a
grey first port is not necessary. `Safe` nevertheless reserves one for every
length-2 helix entered at `η`. This stronger condition is sufficient for both
possible exits and simplifies the induction. It costs one grey port at the
parent; Lemmas 7–9 show that the unique short helix can always be given that
port.

Consider a recursive call `COLOR(H,ε,c₁)` with the following preconditions:

1. `ε` is the actual residue of the interface at the parent of `H`;
2. the parent has assigned `c₁` and included it in a proper exposed multiset;
3. `Safe(H,ε,c₁)` holds.

The desired postcondition is a colouring of the complete helix-subtree rooted at
`H` that preserves `c₁`, makes every exposure in that subtree proper, places
every grey pair at residue `η`, and places every unpaired node at residue `ξ`.

**Theorem 12.** Every target in `K` admits a proper strong 2-separated colouring.

*Proof.* Choose `ξ` and the root ports using Lemma 7. If the unique length-2
helix is a direct root child, assign it a non-grey port in a `ξ`-entry row and a
grey port in the `η`-entry row. Thus every initial call satisfies `Safe`. If the
short helix is not a root child, every root child is long and every displayed
root port is admissible. The root exposure is proper.

We prove the recursive postcondition by structural induction on the number of
helices in the subtree of `H`. Let `Q` be the terminal loop of `H`. By Lemma 5,
`Q` has type `L`, `M`, or `E`. Request

```text
τ=ξ  if Q is L,
τ=η  if Q is M,
τ=ξ  if Q is E.
```

The first two requests are forced by Lemma 6. The third is a free choice.

If `|H|=2`, `Safe` and Lemma 11 give a valid row respecting the fixed first
colour:

| entry | requested exit | colours used |
|---|---|---|
| `ξ` | `ξ` | `c₁c₁` |
| `ξ` | `η` | `c₁G` |
| `η` | `ξ` | `Ga`, `a∈{B,W}` |
| `η` | `η` | `GG` |

If `|H|≥3`, apply Lemma 10. Therefore the helix interior is proper, every grey
pair in `H` lies at `η`, the exit is `τ`, and an exit at `ξ` closes non-grey.

Let `a` be the closing colour.

- If `Q` is `E`, then `X(Q)={inv(a)}` is proper and recursion stops.
- If `Q` is `L`, then `a` is non-grey. If `d(Q)=0`, its singleton exposure is
  proper and recursion stops. If `d(Q)=1`, Lemma 8 assigns its outgoing helix
  the first colour `a`.
- If `Q` is `M`, inspect the fixed lengths of its outgoing helices. If one is the
  unique length-2 helix, assign that edge the designated grey port and use the
  designated row of Lemma 8 for the other children. Otherwise use an ordinary
  row of Lemma 8.

Lemma 9 proves that this case split is exhaustive, that the chosen loop row is
proper, and that every resulting recursive call satisfies `Safe`. By the
induction hypothesis, each strictly smaller child subtree satisfies the required
postcondition and preserves its allocated first colour.

The child subtrees are disjoint. Siblings interact only through the parent's
exposed multiset, which was fixed before recursion. Thus their colourings glue
without further constraints. Unpaired children occur only at `L` loops and at
the root; their levels are `ξ`. All grey pairs lie at `η`.

The helix tree is finite, so the recursion terminates. Combining the root with
the postconditions of its child subtrees gives a proper strong 2-separated
colouring of the entire target. ∎

## 11. From a colouring to a sequence

Given the colouring, assign letters top-down:

1. every unpaired position receives `A`;
2. a black pair `[i,j]` receives `(w_i,w_j)=(G,C)`;
3. a white pair receives `(w_i,w_j)=(C,G)`;
4. at the root or below a non-grey parent, grey siblings receive distinct left
   letters from `{A,U}`; below a grey parent, its at most one grey child copies
   the parent's left letter; each right endpoint receives the Watson–Crick
   complement of its left endpoint.

The orientation procedure is always well-defined. Properness gives:

- at most two grey children at the root or below a non-grey parent;
- at most one grey child below a grey parent, because the parent's grey closing
  incidence already occupies one of the two grey slots in its exposed multiset.

Hence the two orientations in `{A,U}` suffice in the first case, and copying the
parent's orientation is unambiguous in the second.

**Lemma 13 (local distinctness).** At every nonroot paired node, the paired
children's left letters are pairwise distinct and differ from the parent's right
letter. At the root, the child left letters are pairwise distinct.

*Proof.* For a black parent, properness permits at most one black child and no
white child; the possible child left letters are therefore `G`, `A`, and `U`,
while the parent right letter is `C`. The white case is symmetric. For a grey
parent with left letter `L∈{A,U}`, properness permits at most one black child,
one white child, and one grey child. Their possible left letters are `G`, `C`,
and `L`, while the parent right letter is `comp(L)`. At the root the possible
child left letters are `G`, `C`, `A`, and `U`, all distinct. ∎

The top-down grey orientation is essential. For example, the all-grey colouring
of `(())` must give the nested grey child the same orientation as its parent;
otherwise `AUAU` admits the co-optimal structure `()()`.

**Lemma 14 (pairing inventory and equality case).** Let `g` be the number of
grey target pairs, `q` the number of non-grey target pairs, and `u` the number of
target-unpaired positions. The assigned sequence satisfies

```text
#U=g,  #G=#C=q,  #A=g+u.
```

Every compatible noncrossing matching `S` satisfies `|S|≤g+q`.
If equality holds, every `U`, `C`, and `G` position is paired in `S`.

*Proof.* Each grey target pair contributes one `A` and one `U`; each non-grey
target pair contributes one `G` and one `C`; and each target-unpaired position
contributes one `A`. Every A–U pair consumes one `U`, and every C–G pair
consumes one `C`. Hence

```text
|S| ≤ #U + #C = g+q = |T|.
```

If equality holds, all `U` and all `C` positions must be used. Each used `C`
has a distinct `G` partner, and `#G=#C`, so every `G` position is used as well.
The target attains equality. ∎

## 12. Uniqueness for the saturated paired skeleton

A word is *saturable* if it admits a compatible noncrossing perfect matching;
the empty word is saturable. A nonempty saturable word is *atomic* if none of
its nonempty proper prefixes is saturable. An *atomic design* for a saturated
target is an atomic word for which that target is the unique compatible
noncrossing perfect matching.

**Lemma 15 (adjacent cancellation and suffix cancellation).** A word is
saturable if and only if it can be reduced to the empty word by repeatedly
deleting adjacent complementary letters. Consequently, if the concatenated
word `xy` is saturable and `x` is saturable, then `y` is saturable.

*Proof.* We first prove the reduction characterization. Suppose that a word `z`
has a compatible noncrossing perfect matching. Induct on `|z|`. The empty case
is immediate. In the nonempty case, choose a matched pair `(i,j)`, with `i<j`,
of minimum span. If `j>i+1`, the mate of position `i+1` must lie strictly between
`i+1` and `j`: a mate outside `(i,j)` would cross `(i,j)`. This produces a
matched pair of smaller span, a contradiction. Hence `j=i+1`. The two adjacent
letters are complementary. Delete them and compress the remaining positions;
the remaining pairs form a compatible noncrossing perfect matching of the
shorter word. Induction reduces that word, and therefore `z`, to the empty word.

Conversely, suppose that `z` reduces to the empty word by a finite sequence of
adjacent complementary deletions. Induct on the number of deletions. The
zero-deletion case is the empty word. For the inductive step, perform the first
deletion and give the shortened word the compatible noncrossing perfect matching
provided by induction. Reinsert the deleted adjacent positions and match them
to one another. The new pair is compatible and cannot cross an old pair: it is
either disjoint from that pair or nested inside it. Reversing the deletion
history in this way reconstructs a compatible noncrossing perfect matching of
`z`.

We now express this characterization in the free group on two generators. Let

```text
Γ = {a,a⁻¹,c,c⁻¹}
```

with the fixed-point-free inverse involution. A word over `Γ` is *reduced* if it
has no adjacent inverse pair. Define its reduced form `R(v)` by a left-to-right
stack scan: when the next symbol is inverse to the top symbol, pop the top;
otherwise push the new symbol. Induction on the number of scanned symbols shows
that `R(v)` is reduced and that `v` can be reduced to `R(v)` by adjacent inverse
deletions. Indeed, after a prefix has been reduced to its current stack, a new
symbol either extends that reduced stack or is inverse to its last symbol, in
which case deleting the new final inverse pair produces the next stack.

For completeness, this normal form is invariant under every such deletion. Let
`r` be a reduced stack and let `s∈Γ`. Reading `s` followed by `s⁻¹` returns the
stack to `r`. If `r` ends in `s⁻¹`, reading `s` first pops that symbol; reducedness
ensures that the shortened stack does not end in `s`, so reading `s⁻¹` restores
the popped symbol. Otherwise reading `s` pushes it and reading `s⁻¹` immediately
pops it. Taking `r=R(p)` and then continuing the same scan through a suffix `q`
therefore gives

```text
R(p s s⁻¹ q) = R(pq).
```

Thus a word over `Γ` reduces to the empty word if and only if its reduced form is
empty.

Define `F(a,c)` to be the set of reduced words over `Γ`, with

```text
r·s = R(rs),     1 = the empty word,
r⁻¹ = the reversal of r with every symbol inverted.
```

The stack definition and deletion invariance give

```text
R(R(p)q)=R(pq)=R(pR(q)).
```

These identities give associativity of `·`; the empty word is an identity; and
successive cancellation from the middle of `rr⁻¹` and `r⁻¹r` gives a two-sided
inverse. This is the reduced-word construction of the free group on `a` and `c`.
Indeed, assigning arbitrary group elements to `a` and `c`, and their inverses to
the inverse symbols, evaluates reduced words to the unique homomorphism with
those generator values: inverse-pair deletion does not change the evaluation,
so evaluation respects the product `r·s=R(rs)`.

Encode nucleotide letters by

```text
A ↦ a,     U ↦ a⁻¹,     C ↦ c,     G ↦ c⁻¹,
```

and let `Φ(z)∈F(a,c)` be the group element represented by the encoded word.
Complementary nucleotide letters encode exactly as inverse symbols. The first
part of the proof and the normal-form characterization therefore give

```text
z is saturable  ⇔  Φ(z)=1.
```

Also `Φ(xy)=Φ(x)·Φ(y)`. If `x` and `xy` are saturable, then

```text
Φ(y) = Φ(x)⁻¹·Φ(xy) = 1⁻¹·1 = 1.
```

Hence `y` is saturable. This adjacent-cancellation/free-group formulation is the
route intended for formalization. ∎

**Lemma 16 (atomic endpoint characterization).** A nonempty saturable word `z`
is atomic if and only if every compatible noncrossing perfect matching of `z`
contains the pair `(1,|z|)`.

*Proof.* Suppose `z` is atomic. If a perfect matching paired position 1 to
`j<|z|`, noncrossing and saturation would make `z[1,j]` a nonempty proper
saturable prefix, a contradiction.

Conversely, suppose a nonempty proper prefix `p` of `z` were saturable. Write
`z=ps`. Lemma 15 makes `s` saturable. Concatenating perfect matchings of the two
consecutive blocks gives a perfect matching of `z` that omits `(1,|z|)`. ∎

**Lemma 17 (concatenating atomic designs).** Let `z₁,…,z_t`, with `t≥1`, be
atomic designs for saturated targets `R₁,…,R_t`. If their first letters are
pairwise distinct, then `z₁⋯z_t` has `R₁⋯R_t` as its unique compatible
noncrossing perfect matching.

*Proof.* Let `P` be any compatible noncrossing perfect matching of the
concatenation. If `P` contains the outer pair of every block, those pairs isolate
the blocks. The restriction of `P` to each block is therefore `R_i`, by the
unique-design property.

Otherwise choose the leftmost block `z_i` whose first position is not paired to
its own last position. Earlier blocks are isolated by their outer pairs. The first
position of `z_i` is paired by `P` to a position `k` in some block `z_j`, with
`j≥i`.

If `k` is the last position of `z_j`, then `j>i`. Lemma 16 applied to the target
matching `R_j` shows that the first and last letters of `z_j` are complementary.
The `P` pair also makes the first letter of `z_i` complementary to the last
letter of `z_j`. Unique complementation would make the first letters of `z_i`
and `z_j` equal, contradicting their pairwise distinctness.

If `k` is not the last position of `z_j`, the `P` pair from the first position of
`z_i` through `k` encloses a perfect matching. Hence

```text
z_i z_{i+1} ⋯ z_{j−1} z_j[1,k]
```

is saturable, where `k` now denotes the offset within `z_j`. Repeatedly apply
Lemma 15 to remove the complete saturable blocks `z_i,…,z_{j−1}`. The remaining
word `z_j[1,k]` is a nonempty proper saturable prefix of the atomic word `z_j`,
a contradiction. Thus every block has its outer pair in `P`, and `P` equals the
concatenated target. ∎

**Lemma 18 (wrapping atomic designs).** Let `t≥0`. For every `i∈{1,…,t}`,
let `z_i` be an atomic design for a saturated target `R_i`. Let `a,b` be
complementary letters, and suppose that the first letters of the `z_i` are
pairwise distinct and none equals `b`. Then

```text
W = a z₁⋯z_t b
```

is an atomic design for the target consisting of the positional outer pair
`(1,|W|)`, whose endpoint letters are `a,b`, around the concatenated targets.

*Proof.* For `t=0`, the two-letter word `ab` has the stated property. Assume
henceforth that `t≥1`. The displayed target proves that `W` is saturable.

Suppose that `W` has a nonempty proper saturable prefix, and choose one of
minimum length. Its length cannot be

```text
1 + Σ_{r=1}^i |z_r|
```

for any `i∈{0,…,t}`, because every `z_r` has even length and every perfect
matching covers an even number of positions. Here `i=0` is allowed, with the
empty sum equal to zero, so the length-one prefix is included. Since the prefix
omits the final `b`, it therefore ends at an offset `k` strictly inside some
`z_j`, with
`1≤k<|z_j|`.

In a perfect matching of this shortest prefix, the initial `a` must pair to the
last position. Otherwise the prefix ending at its partner would be a shorter
nonempty saturable prefix. The last letter is consequently `b`. Removing this
outer pair leaves

```text
z₁⋯z_{j−1} z_j[1,k−1]
```

saturable. Repeated cancellation of the complete blocks by Lemma 15 makes
`z_j[1,k−1]` saturable. Atomicity forces `k−1=0`; hence the first letter of
`z_j` is `b`, contrary to the hypothesis. Thus `W` is atomic.

By Lemma 16, every compatible perfect matching of `W` contains the outer pair.
Its interior matching is the unique concatenation supplied by Lemma 17. The
displayed target is therefore unique. ∎

**Theorem 19 (saturated local-distinctness theorem).** Let `R` be a saturated
target and let `z` be a compatible sequence. Suppose that:

1. at the root, the paired children's left letters are pairwise distinct;
2. at every nonroot pair `[i,j]`, the paired children's left letters are pairwise
   distinct and none equals `z_j`.

Then `R` is the unique compatible noncrossing perfect matching of `z`.

*Proof.* If `z` is empty, the empty matching is the only matching. Assume `z` is
nonempty and induct upward through the interval tree. A leaf pair is the case `t=0`
of Lemma 18. At a nonroot pair `[i,j]`, saturation means that its interior is the
concatenation of its paired-child subwords. By induction those child words are
atomic designs. The local hypotheses are exactly those of Lemma 18, with
`a=z_i` and `b=z_j`; hence the whole `[i,j]` subword is an atomic design.

At the root, saturation makes the whole word the concatenation of the root-child
subwords. They are atomic designs, and their first letters are pairwise distinct.
Lemma 17 gives uniqueness. ∎

## 13. Excluding a tied unsaturated competitor

For the sequence `w` from Section 11, define the prefix balance

```text
Λ(k) = #G in w[1,k] − #C in w[1,k],   Λ(0)=0.
```

**Lemma 20 (tree levels equal prefix balances).** For the Section 11 sequence
assigned from the target colouring, every paired target node `v=[i,j]` satisfies
`Λ(i)=ℓ(v)`. For every target-unpaired position `k`, `Λ(k)` equals the level of
its unpaired interval-tree node. If `v=[i,j]` is grey, then also
`Λ(j)=Λ(i)=ℓ(v)`.

*Proof.* Every complete target subtree contains equally many `G` and `C`
letters: each black or white pair contributes one of each, while grey pairs and
unpaired `A` letters contribute neither. Thus a completed earlier-sibling subtree
has zero net effect on `Λ`.

At the left endpoint of a paired node, the only nonzero contributions not yet
cancelled are the left endpoints on its root path. A black endpoint contributes
`+1`, a white endpoint `−1`, and a grey endpoint `0`, so their sum is `ℓ(v)`.
At an unpaired `A`, the open ancestors contribute the level of its parent and
the `A` changes nothing. Finally, both endpoints of a grey pair lie in `{A,U}`
and its interior is a concatenation of balanced subtrees and unpaired `A`
positions, so its right endpoint has the same balance as its left endpoint. ∎

**Lemma 21 (level-imbalance obstruction).** Let `P` be a compatible noncrossing
matching of the sequence `w` fixed at the start of this section. If `P` contains
an A–U pair between positions `a<b` with `Λ(a)≠Λ(b)`, then `P` leaves at least
one `G` or `C` position unpaired.

*Proof.* No position strictly between `a` and `b` can pair outside that interval
without crossing `(a,b)`. Since the two endpoints contribute neither `G` nor
`C`,

```text
#G in w[a+1,b−1] − #C in w[a+1,b−1] = Λ(b)−Λ(a) ≠ 0.
```

Every paired `G` in the interval needs a distinct `C` there and conversely.
The unequal inventory therefore leaves at least one `G` or `C` unpaired. ∎

**Theorem 22 (no-tie theorem).** Let `T` have a proper separated colouring and
let `w` be assigned by the rule in Section 11. If a compatible noncrossing
structure `S` satisfies `|S|=|T|`, then `S=T`.

*Proof.* Lemma 14 shows that a tie uses every `U`, `C`, and `G` position.

Suppose a position `i` that is unpaired in `T` were paired to `j` in `S`. Then
`w_i=A` and compatibility gives `w_j=U`. Every `U` belongs to a grey target pair
`v`. By Lemma 20, `Λ(i)` is the level of the target-unpaired node and `Λ(j)` is
the level of `v`, regardless of which endpoint of `v` contains the `U`.
Separation says these two integer levels differ. Define

```text
a=min(i,j),   b=max(i,j).
```

Then `a<b`, `(a,b)` is the same A–U pair of `S`, and `Λ(a)≠Λ(b)`. Lemma 21
would force `S` to leave a `G` or `C` unpaired, contradicting the equality case
of Lemma 14.
Therefore every target-unpaired position remains unpaired in `S`.

The two structures have the same number of pairs, hence the same number of
unpaired positions. Their unpaired-position sets are therefore equal. Delete
that common set and compress the remaining positions in backbone order. The
paired restrictions of `T` and `S` become saturated compatible noncrossing
matchings of the paired-restriction word.

Deleting unpaired singleton nodes does not change any paired parent-child
relation. Lemma 13 therefore gives the paired-restriction word exactly the local
distinctness properties of Theorem 19 for the saturated paired restriction of
`T`. Theorem 19 makes that target restriction the unique compatible perfect
matching, so the restrictions of `S` and `T` agree. Since their common deleted
positions are unpaired in both, `S=T`. ∎

**Theorem 23 (one-short-helix designability).** Every pseudoknot-free target
secondary structure avoiding `m₅` and `m₃•`, with exactly one maximal helix of
length 2, no maximal helix of length 1, and every other maximal helix of length
at least 3, is uniquely designable in the four-letter Watson–Crick model with
energy `E=−#base pairs`.

*Proof.* Such a target belongs to `K`. Theorem 12 constructs a proper strong
2-separated colouring, and Lemma 3 makes it separated. Apply the sequence
assignment of Section 11. Lemma 14 proves that no compatible structure has more
pairs than the target, while Theorem 22 proves that no distinct compatible
noncrossing structure ties it. Thus the target is the unique maximum-cardinality
compatible noncrossing matching. ∎

The target uses all available limiting pairing material. Lemma 14 prevents an
alternative from using more. The separated-colouring argument prevents any
different noncrossing geometry from using all of it equally well. Consequently
every alternative fold leaves at least one limiting `U`, `C`, or `G` position
unmatched.

The proof strategy in Sections 12–13 specializes the arguments behind Claims
4.1–4.3 and Theorems 4 and 8 of Haleš et al. [1]. All implications needed here,
including saturated-skeleton uniqueness, are proved above; [1] is cited for prior
art and provenance, not used as a logical premise.

## 14. Scope

The theorem is stated in the exact maximum-base-pair Watson–Crick model of
Section 1. It makes no assertion for G–U wobble, pseudoknots, Turner energies, or
ensemble objectives.

The requirements of exactly one length-2 helix and no length-1 helix are
limitations of this colouring construction and theorem. They are not assertions
that targets outside the class are undesignable. With multiple length-2 helices,
one loop can demand more designated grey child ports than the tables provide,
so this construction can fail.

Computational negative controls, not used anywhere in the proof, also show why
construction failure must not be confused with undesignability. For example,
the targets with multiple length-2 helices `(((())(())))` and `(())(())(())`
defeat the uniform designated-port construction in the supplied harness, yet
exact folding verifies the respective designs `AAAAUUCAUGUU` and
`AAUUCAUGGAUC`.

## References

1. Haleš, J., Héliou, A., Maňuch, J., Ponty, Y., and Stacho, L.
   “Combinatorial RNA Design: Designability and Structure-Approximating
   Algorithm in Watson-Crick and Nussinov-Jacobson Energy Models.”
   *Algorithmica* **79** (2017), 835–856.
   <https://doi.org/10.1007/s00453-016-0196-x>.
2. Boury, T., Bulteau, L., and Ponty, Y. “RNA Inverse Folding Can Be Solved
   in Linear Time for Structures Without Isolated Stacks or Base Pairs.”
   *WABI 2024*, LIPIcs **312**, Article 19, 19:1–19:23.
   <https://doi.org/10.4230/LIPIcs.WABI.2024.19>.
