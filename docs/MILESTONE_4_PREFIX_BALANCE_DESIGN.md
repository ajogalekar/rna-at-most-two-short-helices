# Milestone 4 prefix-balance design

## Indexing convention

The primary definition is the boundary form

```text
prefixBalanceBoundary (w : Sequence n) (k : Fin (n + 1)) : Int
```

which sums nucleotide weights at positions `j` satisfying `j.val < k.val`.
Weights are `G -> +1`, `C -> -1`, and `A,U -> 0`.  Boundary zero is the empty
prefix and boundary `n` is the whole sequence.

The manuscript's inclusive function is retained as

```text
prefixBalanceAt (w : Sequence n) (i : Fin n) : Int :=
  prefixBalanceBoundary w (boundaryAfter i)
```

where `boundaryAfter i` has value `i.val + 1`.

The exact translation is:

- manuscript position `k` in `{1,...,n}` is Lean position `i : Fin n` with
  `i.val = k - 1`;
- manuscript `Lambda(k)` is `prefixBalanceAt w i`;
- equivalently it is `prefixBalanceBoundary w` at boundary value `k`;
- manuscript `Lambda(0)` is boundary value zero.

For a four-position word, the positions have Lean values `0,1,2,3` and the
five boundaries have values `0,1,2,3,4`.  For example, the weights of `GAUC`
are `+1,0,0,-1`; its boundary balances are `0,1,1,1,0`, while its inclusive
balances are `1,1,1,0`.  Thus the inclusive value at Lean position zero is the
boundary value one, not boundary zero.

## Alternative A: inclusive prefixes only

An inclusive-only definition mirrors the displayed manuscript formula and is
convenient at a target endpoint.  Interval subtraction is awkward, however:
one repeatedly needs a predecessor boundary, including a special case at the
first position.  That increases the risk of accidentally including or
excluding an arc endpoint.

## Alternative B: boundaries, with an inclusive wrapper

Boundaries make half-open intervals uniform:

```text
balance on positions lo <= j < hi = boundary(hi) - boundary(lo).
```

They also support a scan invariant.  Immediately after a boundary, the active
target pairs are exactly those whose left endpoint has occurred and whose
right endpoint has not.  Inclusive endpoint statements remain readable through
the proved `prefixBalanceAt` conversion.

## Choice

Architecture B is selected, while exposing both public functions.  All
interval arithmetic is proved first for boundaries; manuscript Lemma 20 is
then stated with `prefixBalanceAt`.

## Proof invariant

For the constructed sequence, a black/white/grey left endpoint has weight
`Color.delta`, the matching right endpoint has its negation, and every
target-unpaired position has weight zero.  Scanning a boundary therefore gives

```text
prefix balance = sum of Color.delta over target pairs open at that boundary.
```

The scan proof uses the unique position-role partition.  At an unpaired
position the open set is unchanged; at a left endpoint its unique pair is
inserted; at a right endpoint its unique pair is erased.  This is also the
formal completed-subtree/cancellation mechanism.

At a paired left endpoint, the open pairs are the node and its strict paired
ancestors, so the sum is exactly the existing `pairedLevel`.  At a target-
unpaired position, the open pairs are its enclosing ancestors, whose sum is
the existing `unpairedLevel`.  At a grey right endpoint, the node has closed
but has delta zero, leaving the same value.  No surrogate level definition is
introduced.

A complete target interval has zero balance because the open-pair sum is the
same immediately before its left endpoint and immediately after its right
endpoint.  The same statement applied to an earlier sibling is the explicit
completed-sibling balance lemma.

For a competitor arc `(a,b)`,
`prefixBalanceAt w b - prefixBalanceAt w a` sums positions `a < j <= b`.
When both endpoints are A/U, the endpoint weights vanish, so this is exactly
the strict-interior G-minus-C balance.  This convention is the one used by the
level-imbalance obstruction.
