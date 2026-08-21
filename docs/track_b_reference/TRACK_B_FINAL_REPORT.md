# Track B final report

**Cutoff:** 2026-08-19  
**Locked model:** `docs/MODEL_LOCK.md`

## Primary verdict

**UNIVERSAL TWO-SHORT THEOREM PROVED**

Every target in `K2` admits a proper strong 2-separated coloring. Consequently
it admits a proper ordinary separated coloring and is uniquely designable in
the locked four-letter Watson--Crick maximum-base-pair model.

The combined result is also established: every motif-free target with no
length-1 helix, all non-short helices of length at least 3, and at most two
length-2 helices is uniquely designable. The zero-, one-, and two-short cases
use distinct dependencies: the prior all-long theorem, the completed
Lean-verified exact-one theorem, and the new Track B theorem, respectively.

## A/B/C/D verdicts

| question | verdict | basis |
|---|---|---|
| A. Does the explicitly frozen legacy/direct-short deterministic extension always work? | **No.** | A minimum Type-I failure occurs at `n=26`; the policy is defined independently in `src/rna2short/legacy.py`. |
| B. Does every `K2` target have some proper strong 2-separated coloring? | **Yes.** | Universal structural induction and exact finite-state grammar closure. |
| C. Does every `K2` target have some proper separated coloring? | **Yes.** | Strong 2-separation implies exact integer separation. |
| D. Is every `K2` target uniquely designable? | **Yes.** | The generic Lean-verified theorem `uniqueDesigns_sequenceOfProperSeparatedColoring` has no helix-count premise. |

The A failure does not refute B, C, or D. Indeed, its witness has an explicit
alternative strong coloring and an exact unique-design sequence. Conversely,
the adaptive choices in the new proof constitute a successful constructor;
only the named literal legacy-style policy is refuted.

## Why the universal theorem is proved

Contracting maximal helices gives a complete bounded-degree ordered grammar:
terminal types `E`, `L0`, `L1`, `M2`, and `M3`; roots of degree at most two
when an unpaired root child exists and at most four otherwise. Every grammar
tree has a concrete noncrossing realization, and every target in the locked
class contracts to one such tree.

For a helix-subtree `H`, the exact boundary state records which of the six
pairs `(entry residue, first color)` extend to a proper strong coloring. The
least closure with at most two short helices contains only

```text
F = {xi:B, xi:W, eta:B, eta:W, eta:G}
Q = {xi:B, xi:W,                 eta:G}.
```

Short-free subtrees have state `F`; one- or two-short subtrees have `F` or
`Q`; a `Q` subtree consumes at least one short helix. Thus at most two sibling
subtrees can force gray ports. If two do so below an M loop, they have already
used the global short budget, so the incoming helix is long. The exact
length-3 transfers `GBB/GWW`, and their arbitrary-length parity extensions,
let that helix exit at `eta` while closing non-gray. The resulting exposure
uses two gray child ports without exceeding the gray capacity. At the root,
the indispensable degree-3 rows are `BWG`, `BGG`, and `WGG`; degree 4 uses
`BWGG`.

The structural proof states the explicit induction predicate

```text
s(H)=0       => F is contained in Accept(H)
1<=s(H)<=2  => Q is contained in Accept(H).
```

It handles every transfer, endpoint, child count, and root degree, then proves
that child colorings glue because siblings interact only through their common
parent exposure. Independently, the executable verifier regenerates all valid
helix words, all local allocations, the least grammar fixed point, and every
total-two-short root multiset. Both arguments are universal; neither depends
on a nucleotide cutoff. The full human proof is in
`proofs/TWO_SHORT_HELIX_THEOREM.md`, and the exactness/grammar proof is in
`automaton/STATE_DEFINITION.md`.

## Smallest failure found

The smallest failure is Type I only: failure of the frozen deterministic
policy. Under the requested ordering its representative is

```text
dot bracket: (((((((())(()))))((())))))
n:           26
pairs:       13
helices:     5
profile:     (2,2,3,3,3)
compact tree: Root(3:M2(3:M2(2:E,2:E),3:E))
```

The policy colors the outer length-3 helix `BBB`, enters the critical
length-3 M helix at `eta` with `B`, and chooses `BBG`. Its gray closing
incidence plus the two Safe-required gray short-child ports creates `GGG`,
exceeding capacity two. The exact solver instead supplies a proper strong
coloring. Its constructed sequence

```text
GGGGGAGGCCCCGGUCCAGGCCUCCC
```

has exact Nussinov optimum score 13 and optimum count 1, with the target as
the unique optimum.

The minimum is established relative to the precisely frozen policy by a
complete reduced-grammar scan through `n=25`, a compression lemma preserving
policy behavior, and a direct 13-pair lower bound for the three-gray collision.
At `n=26` exactly five reduced representatives fail; all have 13 pairs and five
helices, and the displayed target is lexicographically first. The full trace,
certificate, and independent verifier are in `counterexamples/`.

No Type-II, Type-III, or Type-IV `K2` failure exists, by the universal theorem.

## Exhaustive finite ranges

The literal E/L/M grammar includes every number and placement of unpaired
positions and was independently matched to raw Motzkin generation through
`n=12`. It then exhaustively processed every `K2` target through `n=20`:

| `n` | targets |
|---:|---:|
| 8 | 1 |
| 9 | 7 |
| 10 | 24 |
| 11 | 60 |
| 12 | 125 |
| 13 | 231 |
| 14 | 398 |
| 15 | 657 |
| 16 | 1,089 |
| 17 | 1,864 |
| 18 | 3,325 |
| 19 | 6,081 |
| 20 | 11,178 |
| **total** | **25,040** |

For every row, `results/exhaustive_k2.csv` records the dot-bracket target,
reversal orbit, helix and short-placement data, policy result, exact strong and
ordinary results, explicit colorings, constructed sequence, and exact optimum
score/count. All 25,040 rows are B/C/D positive. All are also A positive,
consistent with the separately established first A failure at `n=26`.

A second exhaustive computation covered 9,527 compact paired-tree
representatives through reduced `n=28`. It found no strong-2 failure. Policy A
failed 5, 20, and 42 times at reduced lengths 26, 27, and 28 respectively.

## Directed, random, and negative-control coverage

The directed instrumentation hit every endpoint type, root and internal paired
degree 4, degree-3 M loops, unpaired degree-2 interfaces, two short root
children, two short children of one M loop, nested shorts, separate deep
branches, gray-closing M helices, and both parities of long helices. Across the
reduced run it covered every short endpoint pair `E/E`, `E/L`, `E/M`, `L/L`,
`L/M`, and `M/M`, with compact depth through 4.

The seeded large-target run checked 2,000 distinct `K2` targets (`seed
20260819`) with lengths 31--311 and compact depths 2--11. It hit every short
placement class and both maximum legal root and internal degrees. Every target
was accepted by the exact strong solver. Exact folding was also run for 200
selected targets of length at most 80; all 200 constructed sequences had the
target as their unique optimum.

For out-of-class falsification, the exact search processed all 15,702
motif-free targets with exactly three short helices through `n=20` and found no
ordinary-separation failure. This is finite evidence only. The smaller directed
target `((.))((.))((.))` is nevertheless an exact strong-2 NO: three `Q`
branches fit neither the two non-gray root slots nor the two gray slots. It is
ordinary-separated YES and uniquely designed by `GGACCACAGUUCAGA` (score 6,
count 1), demonstrating that B failure must not be reported as C or D failure.
It therefore does not make two a sharp boundary for ordinary separability or
designability.
The `m5` five-root-helix control is a NO instance for proper colorability,
strong-2, and ordinary separation.

Four mutation tests each fail on a concrete `K2` forcing witness when one
load-bearing item is corrupted: `GBB/GWW`, `BGG/WGG`, a tight two-gray M row,
or the length-2 `BG` parity transition.

## What is proof and what is computation

| claim | status |
|---|---|
| Exact helix and local-allocation relations | Exhaustive finite local proof, regenerated by verifier |
| Exactness of the six-bit subtree recurrence | Mathematical soundness/completeness proof |
| Reachable closure `F/Q` and acceptance of all `K2` roots | Complete finite-state proof |
| Universal B theorem | Structural induction plus exact closure |
| Universal C theorem | Logical consequence of B |
| Universal D theorem | B/C plus generic existing Lean theorem |
| Minimum A failure at `n=26` | Policy-specific structural lower bound and exhaustive reduced computation |
| Literal, reduced, random, folding, and three-short results | Computation only |
| Absence of a previously published exact `K2` result | Dated qualified literature-search result only |

The Nussinov score/count recurrence was checked against a structurally
independent all-matchings oracle on all sequences through length 5 and 200
seeded sequences at lengths 6--7. The strong and ordinary tree solvers were
checked against raw `3^p` coloring enumeration on every noncrossing structure
through `n=7`.

## Literature and novelty status

The dated audit found that Boury, Bulteau, and Ponty's 2024 theorem, retained
as Theorem 12 in the 2025 journal expansion, covers motif-free targets only
when every helix has length at least 3. Their exact `h_min=2` nonseparable
construction contains many length-2 helices, not exactly two. The shorter-
helix experiments are empirical and unfiltered for `K2`. The later
biseparability result proves a certificate-to-design implication but no
universal bounded-stack existence theorem.

No exact-two, at-most-two, placement, finite-tree-automaton, or exact `K2`
counterexample theorem was located in the documented primary-source, thesis,
preprint, and citation searches through 2026-08-19. This is a qualified dated
negative search, not a proof of novelty. `literature/REPORT.md` keeps proved
theorems, implied specializations, empirical evidence, and search absence
separate.

## Preservation, reproducibility, and residual uncertainty

The completed one-short repository remained unmodified and clean at commit
`c37eac40ef5a28bf5733fd576ce6d4c44091ee6a`. All copied reference files are
read-only and hash-checked. Runtime code was written from scratch in this
separate repository. The certificate, mutation suite, 26-test suite, Type-I
independent verifier, reference hashes, and release-file hashes pass from a
clean checkout. Exact commands, versions, timings, seed, and hashes are in
`REPRODUCIBILITY.md` and `results/SHA256SUMS.txt`.

Residual uncertainty is limited to the usual risk of an unformalized new
human proof, transcription between the proof and a future formalization, and
the unavoidable incompleteness of a negative literature search. It is not a
finite-enumeration gap in the universal argument: the theorem rests on a
complete grammar induction and exact closure. Track B itself contains no new
Lean code.

## Exact next step

Formalize, in a new downstream Lean project pinned to the immutable one-short
commit, the `F/Q` resource invariant, the `GBB/GWW` non-gray-closing transfer,
the two-gray M allocation, and the complete root cases. Then compose the new
strong-2 theorem with the already checked generic no-tie theorem. The staged
obligations and required axiom audit are specified in
`reports/LEAN_FORMALIZATION_PLAN.md`.
