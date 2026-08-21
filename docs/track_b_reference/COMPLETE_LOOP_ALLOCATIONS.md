# Complete root and loop allocations

Status: exact local theorem, conditional on the exact acceptance states of the
actual ordered children.  This replaces the old ordinary/designated tables,
which were sufficient choices rather than an exhaustive relation.

## 1. Exposure and child-interface conventions

For a nonroot loop whose incoming helix closes in colour `a`, the exposed
multiset is

```text
{inv(a)} + {p1,...,pd},
```

where `pi` is the first colour of the actual ordered child helix.  At the root
there is no closing incidence.  Proper means at most one `B`, one `W`, and two
`G` entries.

The exact subtree closure has only two states when the subtree contains at most
two short helices:

```text
F = {xi:B, xi:W, eta:B, eta:W, eta:G}
Q = {xi:B, xi:W, eta:G}.
```

Thus, at a `xi` entry, both states accept exactly the usable ports `B,W`.  At an
`eta` entry, `F` accepts `B,W,G`, while `Q` forces `G`.  A `Q` state always
contains at least one short helix; consequently at most two siblings can be
`Q` in a K2 target.

This is why the CSV is indexed by the ordered `F/Q` signature rather than only
by whether the child helix itself has length two.  Direct shortness alone is
not an exact interface: a short child can have state `F` or `Q`, and a long
child can have state `Q` because a short helix occurs deeper in its subtree.
The column `short_outgoing_count` explicitly covers zero, one, and two direct
short children whenever structurally consistent; the allocation is unchanged
after the exact child state is known.

For completeness, the actual-child short masks covered by that column are:

| child count | 0 short | 1 short | 2 short |
|---:|---|---|---|
| 0 | empty | -- | -- |
| 1 | `0` | `1` | -- |
| 2 | `00` | `10`, `01` | `11` |
| 3 | `000` | `100`, `010`, `001` | `110`, `101`, `011` |
| 4 | `0000` | `1000`, `0100`, `0010`, `0001` | `1100`, `1010`, `1001`, `0110`, `0101`, `0011` |

Here bit `i=1` means that actual ordered child helix `i` itself has length two.
Every ordered assignment in a CSV row applies to every listed mask consistent
with the row's child acceptance states and with the global counter.  This is an
explicit factorization of the full enumeration, not an omission: local
properness reads only the accepted first-colour set, while the recurrence
separately adds the exact short counter.

Every positive CSV row is **necessary and sufficient** for local properness and
child acceptance, and the listed ordered assignments are **exhaustive**.
`NONE` rows are exact impossibility rows.  No row is merely a chosen
construction.

## 2. Root allocations

### Root entered at `xi`

Every child offers `B,W` and no child offers `G`.  Hence:

| paired children | exact multisets | exact ordered assignments |
|---:|---|---|
| 1 | `B`; `W` | `B`; `W` |
| 2 | `BW` | `BW`; `WB` |

Three or four children cannot be proper at `xi`.  This covers both a root with
an unpaired child (where `xi=0` is forced and motif avoidance gives `d<=2`) and
an unpaired-free root for which we choose `xi=0`.

### Unpaired-free root entered at `eta`

An `F` child offers any colour and a `Q` child is forced to `G`.  Filtering all
`3^d` ordered vectors by these offers and the `(1,1,2)` capacity gives the CSV.
Ignoring the `F/Q` positional filter, the complete degree-3 multisets are

```text
BWG, BGG, WGG,
```

and the complete degree-4 multiset is

```text
BWGG.
```

These are exact, not guessed rows.  In particular:

- `BWG` handles zero or one forced-grey child;
- `BGG` and `WGG` are indispensable alternatives when two children force
  grey;
- all permutations compatible with the actual ordered child states are listed
  in the CSV;
- three `Q` children are impossible, since they force `GGG`.

For K2 there are at most two `Q` children, so every degree-3 or degree-4 root
tuple is accepted at `eta`.  This is the reason the universal root policy
chooses `eta=0` (equivalently `xi=1`) for an unpaired-free root of degree 3 or
4.

## 3. E and L allocations

An `E` endpoint has no child.  For every closing colour `a`, the singleton
exposure `{inv(a)}` is proper.  Its exit residue is free.

An `L` endpoint lies at `xi`.  A grey closing colour is therefore impossible.
For `a in {B,W}`:

| endpoint | exact child assignment | exposure |
|---|---|---|
| `L0` | none | `{inv(a)}` |
| `L1` | `a` | `{inv(a),a}` |

For `L1`, the other non-grey port duplicates `inv(a)`, while `G` is unavailable
at a `xi` entry.  Thus the port `a` is forced, not merely convenient.  The
argument is independent of whether the child state is `F` or `Q` and of
whether zero, one, or two short helices occur in that child subtree.

## 4. Exact M allocations

An `M` endpoint lies at `eta`.  The following table first ignores which child
positions are `Q`; the positional filter then requires each `Q` position to be
`G`.

| closing `a` | child count | complete child multisets |
|---|---:|---|
| `B` | 2 | `BG`, `GG` |
| `W` | 2 | `WG`, `GG` |
| `G` | 2 | `BW`, `BG`, `WG` |
| `B` | 3 | `BGG` |
| `W` | 3 | `WGG` |
| `G` | 3 | `BWG` |

All compatible permutations are in the CSV.  The table follows immediately by
subtracting the closing incidence from the capacity vector:

- closing `B` contributes `W`, leaving child capacities `(1,0,2)`;
- closing `W` contributes `B`, leaving `(0,1,2)`;
- closing `G` contributes `G`, leaving `(1,1,1)`.

This proves necessity as well as sufficiency.

### Exact grey-capacity obstructions

- With closing `G`, two `Q` children force two additional greys.  Together
  with the closing incidence this gives three greys, so both `M2(G;QQ)` and
  every `M3(G;...QQ...)` row are impossible.
- With non-grey closing and three children, three `Q` children force `GGG`,
  already beyond the grey capacity.

The first obstruction is avoidable in K2 composition because an incoming
helix can often choose a non-grey closing colour: `M2(B;QQ)` and `M2(W;QQ)`
both use child multiset `GG`.  For degree 3 with two `Q` children, choose closing
`B` or `W` and use `BGG` or `WGG`.  The exact helix relation and bottom-up
acceptance recurrence track this choice; a table that fixes the closing colour
too early would create a spurious obstruction.

The old tight designated exposure `{G,G,B}` is the ordered case “closing `G`,
one `Q` child receives `G`, and the other child receives `B`.”  It is proper and
is one of the exact `M2(G;FQ/QF)` rows.  Its white analogue `{G,G,W}` is also
exact and must not be omitted from a complete table.

## 5. Exhaustiveness proof

The Haleš endpoint taxonomy leaves exactly `E`, `L0`, `L1`, `M2`, and `M3` for
the terminal pair of a maximal helix.  Root motif bounds leave degrees 1--2
when an unpaired root child exists and degrees 1--4 otherwise.  These are all
rows considered above.

For any one row, there are only `3^d` ordered port vectors with `d<=4`.
Retaining a vector exactly when

1. every position is in the corresponding child's `Accept` state, and
2. its root or loop exposure respects `(1,1,2)`,

is both the definition of a locally completable assignment and the procedure
used to produce the CSV.  This proves both directions.  The verifier repeats
the enumeration independently.

## 6. Consequences and logical scope

The exact root and loop relation, combined with the exact helix relation, closes
the finite subtree automaton for zero, one, and two short helices.  It proves a
Question-B strong-2 colouring theorem once grammar completeness and root
acceptance are supplied in `automaton/STATE_DEFINITION.md`.

It does not claim that the original deterministic row choice (Question A) is
the only construction, and it does not independently decide Questions C or D.
