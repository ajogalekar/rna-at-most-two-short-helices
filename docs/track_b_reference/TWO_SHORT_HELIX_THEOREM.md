# A universal two-short-helix theorem

## Statement

In the exact model of `docs/MODEL_LOCK.md`, every target in `K2` admits a
proper strong 2-separated coloring. Consequently, every target in `K2` is
uniquely designable in the four-letter Watson–Crick maximum-base-pair model.

The proof below is structural and does not infer a theorem from a nucleotide-
length cutoff. Computation is used elsewhere to audit the finite relations,
not as the logical basis of the induction.

## 1. Compact helix tree and endpoint bounds

Compact every maximal helix to one helix-subtree edge. Its terminal loop is
exactly one of:

- `E`: no children;
- `L`: at least one unpaired child and zero or one outgoing helix;
- `M`: no unpaired child and two or three outgoing helices.

Indeed, an innermost helix pair with exactly one paired child and no unpaired
child would continue the helix. Avoiding `m3•` gives at most one paired child
at a nonroot node that has an unpaired child; avoiding `m5` gives at most three
paired children otherwise. At the root the corresponding bounds are two when
an unpaired child is present and four otherwise.

Fix residues `xi` and `eta=1-xi`. At an `L` loop, the inclusive level is `xi`,
its closing color is non-gray, and its outgoing first color (if any) is also
non-gray. At an `M` loop, properness of an exposure of size at least three
forces a gray incidence, so its inclusive level is `eta`. These are necessary,
not construction conventions.

## 2. The resource invariant

For a helix-subtree `H`, let `s(H)` be its number of length-2 maximal helices.
Write `Accept(H)` for the entry-residue/first-color interfaces that can be
extended to a proper strong 2-separated coloring of all of `H`.

Define the two interface sets

```text
F = {xi-B, xi-W, eta-B, eta-W, eta-G},
Q = {xi-B, xi-W,                 eta-G}.
```

The missing interface `xi-G` is intrinsically invalid: a gray first pair does
not change the entry residue, so it would itself lie at `xi` rather than at
`eta`.

We prove by induction on the number of helices in `H` the explicit predicate

```text
P(H):
  if s(H)=0, then F is a subset of Accept(H);
  if 1 <= s(H) <= 2, then Q is a subset of Accept(H).
```

Thus a short-free subtree is flexible at an `eta` entry; a subtree consuming
one or two short-helix resources is guaranteed a gray port at an `eta` entry.
At a `xi` entry every relevant subtree accepts either non-gray port.

## 3. Helix transfers needed by the induction

The exact length-2 relation is

| entry to exit | valid words |
|---|---|
| `xi -> xi` | `BB`, `WW` |
| `xi -> eta` | `BG`, `WG` |
| `eta -> xi` | `GB`, `GW` |
| `eta -> eta` | `BB`, `WW`, `GG` |

Every word in the table is internally proper and every gray occurrence lies
at `eta`; exhaustive inspection of the nine two-letter words proves the
converse.

For every length `h>=3`, any admissible first color can reach either requested
exit residue while keeping internal exposures proper and all gray pairs at
`eta`; an exit at `xi` can be chosen to close non-gray. This is the standard
long-helix transfer.

One additional transfer is load-bearing here. Suppose an `M` terminal must
close non-gray at `eta` because it has two short-containing child branches.
The current helix is then long. Under `P(H)` its possible guaranteed interfaces
are handled as follows, where `a` is either `B` or `W`:

- entry `xi`, first `a`, odd `h`: use `a^h`;
- entry `xi`, first `a`, even `h`: use `a G a^(h-2)`;
- entry `eta`, first `G`, odd `h`: use `G a^(h-1)`;
- entry `eta`, first `G`, even `h`: use `G G a^(h-2)`.

In each case the number of non-gray contributions has the required parity,
every displayed gray lies at `eta`, all adjacencies are proper, and the last
pair is non-gray. The odd `eta`-entry case at `h=3` is exactly `GBB` or `GWW`.
Those two rows are why the two-short extension closes.

For clarity, these transfers cover every boundary demanded by `P`, not only a
convenient subset.  The complete check is as follows.

| current helix | boundary that `P` requires | terminal requirement | reason it is realizable |
|---|---|---|---|
| long, `s(H)=0` | every member of `F` | none at `E`; `xi` with non-gray close at `L`; `eta` at `M` | the exhaustive `h>=3` relation |
| short, `s(H)>0` | every member of `Q` | the same three endpoint requirements | the exhaustive length-2 table above |
| long, `s(H)>0`, at most one short-containing child | every member of `Q` | the same three endpoint requirements | the exhaustive `h>=3` relation |
| long, two short-containing children | every member of `Q` | `eta` with non-gray close at `M` | the four parity constructions just displayed |

The last row can occur only at `M`: two distinct child subtrees already contain
both short helices, so the current helix is long.  In all other `M` rows, the
loop allocations below work for every closing color that the exact transfer
relation can produce.  This table is the finite transfer case split used in
the induction.

## 4. Inductive loop allocation

Assume `P` for every child helix-subtree of `H`. At an `E` terminal no exit
residue is forced. At an `L` terminal color the current helix to exit at `xi`
and close non-gray; at an `M` terminal color it to exit at `eta`. Use the
complete transfer case split in Section 3, requesting its strengthened
non-gray-closing transfer in the one case identified below.

### E terminal

There is no child. Its exposure contains only the inverse of its closing
color, hence is proper.

### L terminal

The transfer exits at `xi` and closes in a non-gray color `a`. If there is an
outgoing helix, give it first color `a`. The exposure is
`{inv(a),a}`, hence proper. The child enters at `xi`; `xi-a` belongs to `Q`
and therefore to either inductive guarantee.

### M terminal

Let `d in {2,3}` be the number of outgoing helices, and let `r` be the number
of child subtrees containing at least one short helix. Globally there are at
most two, so `r<=2`.

If `r=0`, use the following exact proper port rows:

| closing color | `d=2` | `d=3` |
|---|---|---|
| `B` | `B,G` | `B,G,G` |
| `W` | `W,G` | `W,G,G` |
| `G` | `B,W` | `B,W,G` |

Every child is short-free and accepts every displayed `eta` port by its `F`
guarantee.

If `r=1`, give the unique short-containing child the port `G`. Allocate the
remaining ports by

| closing color | other ports for `d=2` | other ports for `d=3` |
|---|---|---|
| `B` | `B` | `B,G` |
| `W` | `W` | `W,G` |
| `G` | `B` | `B,W` |

The designated child accepts `eta-G` by `Q`; all other children are
short-free and accept their `F` ports. Every exposure respects capacities
`(1 B, 1 W, 2 G)`.

If `r=2`, the current helix cannot itself have length 2, since the two child
branches already contain both global short helices. Request the strengthened
long-helix transfer of Section 3, so the terminal closes non-gray. If it closes
`B`, give the two short-containing children `G,G` and, when `d=3`, give the
remaining short-free child `B`. For a `W` closing use `G,G` and optionally
`W`. The resulting exposures are `{W,G,G}` or `{W,G,G,B}`, and their
black/white inverses, all proper. This is the only new allocation beyond the
one-short proof.

All recursive calls therefore satisfy `P`. Children have disjoint node sets
and meet only in the already checked exposure at their parent, so the child
colorings glue. This completes the induction.

## 5. Root allocation

The target contains pairs, so the root has `d>=1` paired children.

If the root has an unpaired child, its level forces `xi=0`, and motif avoidance
gives `d<=2`. Give the paired children `B` when `d=1`, or `B,W` when `d=2`.
Every child enters at `xi` and accepts its port by `Q`.

If the root has no unpaired child and `d<=2`, make the same choice with
`xi=0`.

If it has no unpaired child and `d in {3,4}`, set `eta=0` and `xi=1`. Let `r`
be the number of root-child subtrees that contain a short helix; `r<=2`. Give
each such child a `G` port. Fill the remaining ports, all leading to short-free
children, from `B,W,G` so that the total multiset is:

| degree | `r=0` | `r=1` | `r=2` |
|---:|---|---|---|
| 3 | `B,W,G` | `G,B,W` | `G,G,B` (or `G,G,W`) |
| 4 | `B,W,G,G` | `G,B,W,G` | `G,G,B,W` |

This explicitly includes the critical `BWG`, `BGG`, and `WGG` rows. Positive-
short children accept `eta-G` by `Q`; zero-short children accept every other
port by `F`. Root properness follows immediately.

## 6. Global conclusion

All internal helix adjacencies, terminal-loop exposures, and the root exposure
are proper. Every unpaired child is either at the root or at an `L` terminal,
and hence has residue `xi`. Every gray paired node was placed at residue `eta`.
The constructed coloring is therefore proper and strong 2-separated.

Strong 2-separation implies ordinary separation because the two kinds of
levels occupy disjoint parity classes. The generic, already Lean-verified
theorem
`uniqueDesigns_sequenceOfProperSeparatedColoring` in the immutable one-short
project depends only on a proper separated coloring, not on the one-short
target class. Applying it constructs a complete four-letter sequence whose
unique maximum-pair noncrossing fold is the target.

Hence every `K2` target is strongly 2-separable, separated, and uniquely
designable. Together with the published/previously verified zero-short and
completed Lean-verified one-short cases, this gives the stated `K<=2`
designability corollary.
