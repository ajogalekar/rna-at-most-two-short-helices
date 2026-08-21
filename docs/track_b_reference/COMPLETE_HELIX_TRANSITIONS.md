# Complete helix-transition algebra

Status: exact local theorem.  This file is a re-derivation from the immutable
definitions in `reference/Lean_Definitions/Color.lean` and
`reference/Lean_Definitions/HelixTransfer.lean`; it does not assume that the
old sufficient long-helix constructor was exhaustive.

## 1. Locked conventions

Write `xi` for the unpaired residue and `eta = xi + 1` for the grey residue.
For parity calculations,

```text
delta(B) = delta(W) = 1,   delta(G) = 0.
inv(B) = W, inv(W) = B, inv(G) = G.
```

The equality for `W` is only modulo two: its exact integer delta remains `-1`.
A word `w=c1...ch` entered at residue `r0` is valid exactly when all of the
following hold.

1. Its first colour is the requested `c1`.
2. The running residues obey `ri = r(i-1) + delta(ci)`.
3. If `ci=G`, then `ri=eta`.
4. For each adjacency, `{inv(ci),c(i+1)}` has capacities at most `(1,1,2)`.

Condition 4 is equivalent to forbidding only `BW` and `WB` as adjacent
subwords.  The transition records `(r0,c1) -> (rh,ch)`.  A grey closing colour
automatically has exit `eta`; hence the `LocalTransfer.closesNonGrey` clause for
an exit at `xi` adds no further words.

Every assertion in the transition tables below is **necessary and
sufficient**, and each table is **exhaustive** for its stated length.  An
individual displayed word is a sufficient witness; no individual witness is
claimed necessary when another word has the same boundary data.

## 2. Exact word automaton

The following deterministic scan is an exact finite description of *all*
valid words, including arbitrary lengths not printed in the CSV.

- State: `(current residue, previous colour)` plus a start state.
- On `B` or `W`: reject if the previous colour is the opposite non-grey
  colour; otherwise toggle the residue and remember the new colour.
- On `G`: require the current residue to be `eta`; leave it unchanged and
  remember `G`.
- At the end: accept exactly the requested exit residue and closing colour.

Necessity follows directly from `GreysAt`, `exitResidue`, and
`InternallyProper`.  Sufficiency follows by reading those definitions in the
other direction.  Thus this is not a one-directional construction automaton.
The complete finite slices for `h=2,3,4,5,6` are in
`results/complete_helix_transitions.csv`; the certificate verifier regenerates
all 219 words rather than trusting the CSV.

## 3. Exact boundary relations

In the tables, a cell lists all possible `(exit,closing)` values.  `--` means
that no valid word exists.

### Length 2

| entry, first | exact outcomes | exact words |
|---|---|---|
| `xi,B` | `xi,B`; `eta,G` | `BB`; `BG` |
| `xi,W` | `xi,W`; `eta,G` | `WW`; `WG` |
| `xi,G` | -- | -- |
| `eta,B` | `eta,B` | `BB` |
| `eta,W` | `eta,W` | `WW` |
| `eta,G` | `xi,B`; `xi,W`; `eta,G` | `GB`; `GW`; `GG` |

Regrouping by entry and exit gives exactly the four Lean-verified bridge rows:

```text
xi  -> xi  : BB, WW
xi  -> eta : BG, WG
eta -> xi  : GB, GW
eta -> eta : BB, WW, GG
```

The additional old `Safe` rule selecting `GG` for an `eta -> eta` short helix
is sufficient but not necessary: `BB` and `WW` are exact alternatives.

### Length 3

| entry, first | exact outcomes | exact words |
|---|---|---|
| `xi,B` | `xi,B`; `xi,W`; `eta,B`; `eta,G` | `BGB`; `BGW`; `BBB`; `BGG` |
| `xi,W` | `xi,B`; `xi,W`; `eta,W`; `eta,G` | `WGB`; `WGW`; `WWW`; `WGG` |
| `xi,G` | -- | -- |
| `eta,B` | `xi,B`; `eta,G` | `BBB`; `BBG` |
| `eta,W` | `xi,W`; `eta,G` | `WWW`; `WWG` |
| `eta,G` | `xi,B`; `xi,W`; `eta,B`; `eta,W`; `eta,G` | `GGB`; `GGW`; `GBB`; `GWW`; `GGG` |

In particular, the referee-reported rows are correct and load-bearing entries
of the *exact* relation:

```text
GBB : (eta,G) -> (eta,B)
GWW : (eta,G) -> (eta,W)
```

For `GBB`, the leading grey is inclusively at `eta`; the two black pairs
toggle `eta -> xi -> eta`; and both adjacencies `GB` and `BB` are proper.
`GWW` is symmetric.  Neither row appeared in the old chosen constructor
`G^(h-1)B`, which is why treating that constructor as exhaustive would be
incorrect.

### Length 4 (the exceptional even base)

Let

```text
U = { (xi,B), (xi,W), (eta,B), (eta,W), (eta,G) }.
```

The exact relation is:

| entry, first | exact outcomes |
|---|---|
| `xi,B` | `U` |
| `xi,W` | `U` |
| `xi,G` | -- |
| `eta,B` | `U \ {(eta,W)}` |
| `eta,W` | `U \ {(eta,B)}` |
| `eta,G` | `U` |

So `h=4` must not be silently merged with all larger even lengths.  For
example, an `eta`-entered word starting `B`, exiting `eta`, and closing `W`
needs at least five positions (`BBGWW`).

### Odd `h >= 5` and even `h >= 6`

For every such length, the exact relation has stabilized:

| entry, first | exact outcomes |
|---|---|
| `xi,B` | `U` |
| `xi,W` | `U` |
| `xi,G` | -- |
| `eta,B` | `U` |
| `eta,W` | `U` |
| `eta,G` | `U` |

This removes a tempting but false parity-only simplification: `h=4` is an
exception, while every `h>=5` has the same boundary relation.  Length 5 is the
odd seed and length 6 the even seed.  The CSV enumerates every seed word, not
only one chosen construction.

## 4. Proof of stabilization

There are two universal impossibilities at every positive length.

- `(xi,G)` cannot be an entry/first pair, because a leading grey would have
  inclusive residue `xi`.
- `(xi,G)` cannot be an exit/closing pair, because a closing grey has inclusive
  residue `eta`.

These are the only boundary-level impossibilities once `h>=5`: direct
enumeration by the exact word automaton shows that every member of `U` is
realized from every admissible source at `h=5` and at `h=6`.

For the induction step, let a valid word end in `a` and append `aa`.

- If `a` is non-grey, both new adjacencies are `(a,a)`, hence proper, and two
  parity toggles restore the old exit residue.
- If `a=G`, validity of the old closing occurrence says that the exit is
  already `eta`; the two new greys stay at `eta`, and `GG` is proper.

The first colour, exit residue, and closing colour are unchanged.  Therefore
each odd seed extends to all odd `h>=5`, and each even seed extends to all even
`h>=6`.  Combined with the universal upper bound, this proves equality of the
relations, not merely inclusion.

The same append-two operation is checked on every valid finite seed word by
`automaton/verify_certificate.py`.

## 5. Relation to A/B/C/D

- The exact relation is construction-neutral and is used for Question B.
- It strictly contains the old deterministic long-helix choices, so a failure
  of those choices would concern Question A only.
- Nothing in this local table by itself decides ordinary separation (C) or
  designability (D).

The subtree closure using this relation is given in
`automaton/STATE_DEFINITION.md` and `automaton/REACHABILITY_CERTIFICATE.json`.
