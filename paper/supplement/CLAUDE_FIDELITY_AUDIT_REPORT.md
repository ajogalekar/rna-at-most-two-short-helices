# FAITHFUL AND COMPLETE

Blinded adversarial fidelity audit of the at-most-two-short-helices RNA Lean
formalization. Independent, hostile review: the working assumption throughout
was that a substantive mismatch or hidden weakening existed and had to be found.
It was not found — after the falsification attempts listed in §1 and §15 below.

---

## 1. Earliest substantive problem

**None.** No mismatch, no incomplete proof, no hidden premise, no unsound
dependency, and no weakened definition was found at any point in the chain.

The following were the most promising attack lines. Each was pursued to a
definite negative conclusion rather than left unexamined:

| Attack | Outcome |
|---|---|
| Restrict competitors in `UniqueDesigns` to the target's topology / helices / a grammar | **Failed.** The `∀` binds the full `SecondaryStructure n`. Kernel control 7 confirms a *disjoint* competitor can defeat a target. |
| Weaken the tie condition from `<` to `≤` | **Failed.** Strict `<`; control 7 rejects a genuine tie. |
| Admit G-U wobble, or make `Compatible` non-symmetric | **Failed.** All 16 letter pairs decided exhaustively. |
| Impose a minimum hairpin length, forbidding adjacent pairs | **Failed.** No such constraint exists; exhibited a legal `(0,1)` arc. |
| Strengthen `HasM5`/`HasM3Dot` to narrow the target class | **Failed.** Both thresholds are literally `4 <` and `2 <` — confirmed by `Iff.rfl`. |
| Sneak a nonemptiness hypothesis in to exclude the all-unpaired target | **Failed.** Control 1 puts the empty structure in the class and derives its designability. |
| Find two `MaximalHelix` values denoting the same run (double-counting `k(T)`) | **Failed, provably.** Proof irrelevance plus `length_eq_of_outer_eq` force `H = K ↔ H.outer = K.outer`. |
| Make the short-count decomposition rest on an assumed grammar | **Failed.** It is derived from a real `Finset` partition with explicit disjointness lemmas. |
| Find the `h = 4` even case extrapolated from larger even lengths | **Failed.** Every branch word carries only `3 ≤ h`; `h = 4` words are kernel-checked by `rfl`. |
| Find the r=2 allocation proved only about an anonymous multiset | **Failed.** Ports are a function on actual ordered slots; grey lands at the actual positive slots via a permutation. |
| Find the old exact-one theorem used as a premise | **Failed.** Absent from the transitive closure; it appears only as a corollary. |
| Find a proof escape (`sorry`, custom axiom, `native_decide`, IO) | **Failed.** Zero code-position hits; axiom set is the standard three. |
| Find a cross-branch gluing gap (sibling invalidating a sibling) | **Failed.** Certificates are quantified over *every* total extension, and levels are ancestor-sums, so siblings cannot interact except through the parent exposure. |

Non-substantive observations (dead case split, legacy package name, redundant
class clause, three style-linter warnings) are listed in
`RESIDUAL_LIMITATIONS.md` §6. None affects the verdict.

---

## 2. Exact final theorem type

From `lake env lean` on a temporary file **outside** the extracted source tree:

```
RNA.atMostTwoShortHelixDesignability : AtMostTwoShortHelixDesignabilityStatement

def RNA.AtMostTwoShortHelixDesignabilityStatement : Prop :=
∀ {n : ℕ} (T : SecondaryStructure n), InTargetClassKLeTwo T → ∃ w, UniqueDesigns w T

theorem RNA.atMostTwoShortHelixDesignability : AtMostTwoShortHelixDesignabilityStatement :=
fun {n} T hK =>
  Exists.intro
    (sequenceOfProperColoring (globalColoringCertificateLeTwo hK).coloring
                              (globalColoringCertificateLeTwo hK).proper)
    (atMostTwoShortHelices_uniqueDesigns hK)
```

This is character-for-character the statement in `SPECIFICATION.md` §1:

```lean
forall {n : Nat} (T : SecondaryStructure n),
  InTargetClassKLeTwo T -> exists w : Sequence n, UniqueDesigns w T
```

The proof term is a direct existential introduction of the deterministic
sequence built from the new global certificate — not an appeal to an older
theorem.

---

## 3. Exact axiom set

```
'RNA.atMostTwoShortHelixDesignability' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three standard axioms of classical Lean 4 / Mathlib. No `sorryAx`, no
project-defined axiom, no `opaque`, no `Lean.ofReduceBool` (which `native_decide`
would introduce). The hand-built dependency closure independently reports
**zero** project-defined axioms.

Because Lean 4.34 seals theorem bodies from plain importers, `#print axioms` was
first validated in this exact setup: a deliberately `sorry`-ed control reported
`[sorryAx]`, an axiom-free control reported none, and a Mathlib theorem needing
choice only in its *proof* reported choice. The tool sees proofs here.

---

## 4. Bundle SHA-256

```
observed  bfd2c8d90f5666ccb2dda6a3e9c2f81b84419ae84cc25beb3f880c80b5c66b8b
expected  bfd2c8d90f5666ccb2dda6a3e9c2f81b84419ae84cc25beb3f880c80b5c66b8b   MATCH
```

188,321 bytes. The full-source hash `b077b611…` was **not** observed, so this is
the blinded bundle, not the canonical source archive.

Gate results: `unzip -t` clean; 51 members; 50 manifest entries (the manifest
does not list itself); all 50 recomputed SHA-256 values **OK**; every manifested
file present; no unmanifested source file; zero symlinks; no absolute or `..`
paths; no `.git`, `.lake`, `.olean`, `.ilean`; **no `docs/` report directory**;
`SPECIFICATION.md`, `MANIFEST.sha256`, `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json` all present. A blinding scan for verdicts, reviewer
language, prior audit outcomes, and author identity returned zero hits. The
manifest was re-verified **after** the build: all 50 still OK, so the build did
not modify the source. Full detail in `BUNDLE_INTEGRITY.txt`.

---

## 5. Build outcomes

Pinned, no `lake update`:

- toolchain `leanprover/lean4:v4.34.0-rc1` (as specified in `lean-toolchain`);
- Mathlib pinned at `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` (as in `lake-manifest.json`), plus the eight pinned transitive dependencies;
- `lake clean` → exit 0;
- dependency resolution from the existing manifest → exit 0;
- `lake exe cache get` → exit 0;
- **`lake build RNA.AtMostTwoShort.Designability` → exit 0, 3053/3053 jobs, 38 s.**

Only three Mathlib style-linter warnings (`unnecessarySimpa`, in
`RNA/PairedRestriction.lean:214,221,521`). No errors. The final module and the
final theorem compile. Full log in `BUILD_LOG.txt`.

---

## 6. Model-fidelity assessment

**Faithful.** Full table in `MODEL_TO_LEAN_MAPPING.md`; definitions were read,
not inferred from names.

- **Alphabet.** Exactly four nucleotides `A, C, G, U`. `comp` is A↔U, C↔G, is an
  involution, and no letter is its own complement.
- **Compatibility.** `Compatible x y := y = x.comp`, i.e. exactly the four
  ordered pairs A-U, U-A, C-G, G-C. Symmetric. **G-U wobble excluded.** The
  auditor re-decided the entire 4×4 table; no extra or missing pair.
- **Structure.** One finite ordered backbone `Fin n`. An `Arc` carries
  `ordered : left < right`, so endpoints are distinct and increasing.
  `IsPartialMatching` gives at most one pair per position; `IsNoncrossing`
  excludes crossings and pseudoknots. A `SecondaryStructure` is an **arbitrary**
  such matching — a `Finset (Arc n)` with two proofs, explicitly *not* an
  inductively generated tree language. **No minimum arc or hairpin length**:
  adjacent positions may pair, confirmed by exhibiting one.
- **Energy.** `energy _w S = -(pairCount S : Int)` — exactly minus the pair
  count, with the sequence argument genuinely unused;
  `uniqueDesigns_iff_uniqueMinimumEnergy` gives the equivalent energy form.

---

## 7. Target-class assessment

**Exact match to `SPECIFICATION.md` §1.** `InTargetClassKLeTwo T` is precisely
the five-fold conjunction:

1. `shortHelixCount T ≤ 2`;
2. `∀ H : MaximalHelix T, H.length ≠ 1`;
3. `∀ H : MaximalHelix T, H.length ≠ 2 → 3 ≤ H.length`;
4. `¬ HasM5 T`;
5. `¬ HasM3Dot T`.

`shortHelixCount` counts exactly the maximal helices of length two, and
`lengthTwoHelixOuters_card` proves the count is presentation-free (counting
descriptors = counting canonical outer arcs).

Interval tree: virtual root `none`; one node per target pair; one singleton node
per unpaired position; parent = smallest enclosing paired interval or the root,
proved well-defined and **unique** (`parent_wellDefined_unique`) against an
independent specification `IsParent` via laminarity. Paired degree is
`pairedChildCount` at the root (no parent contribution) and
`1 + pairedChildCount` at a nonroot paired node (paired parent + paired
children); unpaired children never contribute.

Motifs are exactly as specified and **not** stronger: `HasM5 := ∃ p, 4 <
pairedDegree T p`; `HasM3Dot := ∃ p, HasUnpairedChild T p ∧ 2 < pairedDegree T p`.
Both confirmed by `Iff.rfl` against the specification's wording.

Maximal helices: a consecutive nested run with maximality genuinely enforced at
**both** ends (no outward stacked predecessor; no pair at the next inward
offset), positive length, and `.length` proved equal to the actual number of
pairs. Distinct maximal helices are disjoint, and each target pair lies in
exactly one. Equality of `MaximalHelix T` is equality of the actual helix: the
attempted representation-level counterexample is provably impossible.

Coverage, kernel-confirmed: **zero** short helices (all-unpaired, and the
all-long case), **one** (`(())`), and **two** are all in the class. Excluded:
**three** length-two helices, and any target with a **length-one** maximal helix.
**No hidden nonemptiness hypothesis** — the all-unpaired target is in.

---

## 8. Short-resource assessment

**Correct, and load-bearing.** `AtMostTwoShort/ShortCount.lean` proves

```
shortHelixSubtreeCount T H
  = (if H.length = 2 then 1 else 0)
  + ∑ i, shortHelixSubtreeCount T (outgoingHelix T H i)
```

exactly matching `SPECIFICATION.md` §2. It is derived from a genuine finite-set
decomposition (`shortHelicesInSubtree_decomposition`) proved by `ext` in both
directions on top of the real interval-containment subtree — **not** from an
assumed grammar. Each of the audit's four counting requirements has its own
lemma: nothing omitted (the `←` direction), nothing counted twice across
children (`outgoingShortHelices_pairwiseDisjoint`), and the current helix not
double-counted with its children (`currentShortHelix_disjoint_outgoing`).

Consequences, each proved and each individually attacked without success:

- every subtree has short count ≤ 2 under the class hypothesis
  (`shortHelixSubtreeCount_le_two`);
- at most two outgoing child subtrees have positive count
  (`loopShortSupport_card_le_two`), and likewise at the root
  (`rootShortSupport_card_le_two`);
- if two child subtrees have positive count then the incoming helix is **not**
  short (`two_positive_outgoing_implies_length_ne_two` — because `1 + 2 > 2`
  would break the global budget), hence has length ≥ 3
  (`two_positive_outgoing_implies_length_at_least_three`).

The root decomposition `shortHelixCount_root_decomposition` degenerates to the
empty sum for the all-unpaired target, exactly as specified.

---

## 9. F/Q invariant assessment

**Exact.** `InF xi entry first := first.AdmissibleAt entry xi.opposite` and
`InQ xi entry first := (entry = xi ∧ first.NonGrey) ∨ (entry = xi.opposite ∧ first = grey)`.
Decided exhaustively over all `Parity × Parity × Color`:

- `F = {ξ-B, ξ-W, η-B, η-W, η-G}` — exactly five;
- `Q = {ξ-B, ξ-W, η-G}` — exactly three;
- `Q ⊊ F`; at ξ both allow only black and white; at η, F allows all three and Q
  only grey; **ξ-G is invalid in both**.

`RequiredInterface` gives F to a zero-short subtree and Q to a positive-short
subtree, as specified. `constructResourceSubtree_resourceInvariant` states the
guaranteed inclusions — `s(H)=0 → every F accepted`, `1 ≤ s(H) ≤ 2 → every Q
accepted` — and correctly does **not** claim these are exact.

**`(entry residue, first colour)` is genuinely sufficient.** This was the
audit's sharpest question, and the answer is structural: `entryLevel` is defined
as the sum of `Color.delta` over `pairedAncestors v = {p | p strictly contains
v}`. Everything outside the subtree that could matter is therefore aggregated
into the single value `entryLevel chi H.headNode`, whose parity is exactly the
certificate's `entry` hypothesis. Searched for and did **not** find dependence
on: absolute integer level (every postcondition clause is stated through
`levelParity`, never the integer), ancestor history beyond the entry residue,
sibling colouring, number of unpaired nodes, terminal type, an uncarried closing
colour, or extra short-placement state. The two closing facts that *are* needed
beyond the interface — the L case and the two-demand M case — are carried
explicitly as fields (`lTerminalNonGrey`, `twoDemandTerminalNonGrey`) rather than
assumed.

---

## 10. Long-transfer assessment

**Correct, including the `h = 4` boundary.** `longTransfer_eta_closesNonGrey_of_Q`
returns a `LongEtaTransfer` — a *subtype* bundling the transfer with
`ClosesNonGrey` — precisely because the built-in `LocalTransfer.closesNonGrey`
field is conditional on exiting at `eta.opposite` and is therefore useless when
the requested exit is `eta`. This matches `SPECIFICATION.md` §5.

The four branch words are exactly as specified, each constructed under `3 ≤ h`
plus a parity hypothesis, dispatched on `(h : Parity)`:

| Entry | First | Parity | Word | Lean |
|---|---|---|---|---|
| ξ | non-grey `a` | odd | `a^h` | `xiOddEtaTransfer` |
| ξ | non-grey `a` | even | `a G a^(h-2)` | `xiEvenEtaTransfer` |
| η | grey | odd | `G a^(h-1)` | `etaGreyOddEtaTransfer` |
| η | grey | even | `G G a^(h-2)` | `etaGreyEvenEtaTransfer` |

For each: the fixed first colour is preserved (`first_eq`), the exit residue is
`eta` (`exit_eq`), every grey occurrence is at `eta` (`greysAtEta`), internal
exposure is proper (`internallyProper`), and the close is non-grey (the subtype's
second component). `h = 3`, `h = 4`, odd `h ≥ 5` and even `h ≥ 6` are all covered
by the *same* uniform constructions.

**On the `h = 4` warning specifically.** There is no illicit extrapolation. The
supporting lemmas carry at most `3 ≤ h` — `internallyProper_twoGreysThenRepeatWord`
and `closesNonGrey_oneGreyAtTwo` both take exactly `3 ≤ h`, and nothing anywhere
requires `h ≥ 6` or appeals to a stabilized transition table. `SPECIFICATION.md`'s
instruction not to equate the `h=4` relation with the larger-even relation is
honoured: no such equation is stated.

Concrete boundary witnesses, all proved by `rfl` and hence kernel-checked:

```
gbbTransfer          = [G, B, B]          -- GBB
gwwTransfer          = [G, W, W]          -- GWW
etaEvenFourTransfer  = [G, G, B, B]       -- the valid length-4 η word
xiOddThreeTransfer   = [B, B, B]
xiEvenFourTransfer   = [B, G, B, B]       -- the length-4 ξ word, a G a^(h-2)
```

---

## 11. Loop / root allocation assessment

**Correct.** Ports are a **function on actual ordered child slots**
(`ChildPortAssignment`), installed through a permutation (`twoSlotPerm`, built
from `Equiv.swap`), never an overwrite-based map — exactly as
`SPECIFICATION.md` §6 requires. Capacity `ProperExposure` is `≤1` black, `≤1`
white, `≤2` grey.

- **Endpoints.** `E` = no child at all; `L` = has an unpaired child with 0 or 1
  paired children, exits at ξ; `M` = no unpaired child with 2 or 3 paired
  children, exits at η. `requestedExit` gives `L ↦ xi`, `M ↦ eta`, `E ↦ xi`.
  Exhaustiveness of E/L/M follows from motif-freeness.
- **r = 0.** Ordinary rows, all closing colours and degrees 2 and 3.
- **r = 1.** The unique positive child gets grey at its *actual* slot
  (`onePositiveMActualPorts_positive`); the remaining slots are filled
  deterministically; every child receives an interface its `RequiredInterface`
  accepts; exposure is proper.
- **r = 2.** All five demands are discharged and are visible as *fields* of
  `ResourceLoopAllocation`, so Lean could not have accepted the definition
  without them: both actual positive children get grey
  (`twoPositiveMActualPorts_left/right`); the incoming helix is **formally proved
  long** (`twoSupportIncomingLong`, from the accounting lemma); the strengthened
  non-grey-closing transfer is **actually used** — `chooseResourceTransfer` takes
  its `M`/`card = 2` branch and calls `longTransfer_eta_closesNonGrey_of_Q`, and
  the allocation consumes the resulting `a.NonGrey`; at degree 3 the remaining
  child is short-free and receives `a` (`twoPositiveMActualPorts_other_three`).
  Positive children receive η-grey, hence Q; short-free children receive an F
  port at η.
- **Exposed multisets.** `twoPositiveMExposure a .two = {a.inv, G, G}` and
  `.three = {a.inv, G, G, a}` — i.e. `{W,G,G}` and `{W,G,G,B}` for `a = B`, and
  the black/white-swapped `{B,G,G}`, `{B,G,G,W}` for `a = W`. All four decided
  proper; capacity bounds confirmed.
- **Root, degree zero.** Handled separately and explicitly: the root partition
  proves there is **no** paired node at all, so `rootDegreeZeroColoring` is
  genuinely the empty function; properness, absence of grey pairs, every
  unpaired position at exact level zero, and strong 2-separation with `xi = 0`
  are all proved. This is the all-unpaired target.
- **Root with unpaired positions.** Motif-freeness bounds paired degree by 2
  (`root_pairedChildren_le_two_of_unpaired`), forcing `entry = xi` and `xi = 0`;
  positive-short children then receive ξ non-grey ports, which lie in Q.
  Symmetrically, when degree ≥ 3 there can be no root-unpaired position at all,
  so the `eta = 0`, `xi = 1` choice cannot strand one.
- **Root degree 3 or 4.** `eta = 0`, `xi = 1`; at most two root children have
  positive short count (`rootShortSupport_card_le_two`); each gets grey; the rest
  are short-free. The two-demand rows are exactly `G,G,B` (d=3) and `G,G,B,W`
  (d=4), verified slotwise, installed at the actual positive slots, with the
  degree-3 remainder proved black.

---

## 12. Gluing and global-assembly assessment

**Sound; no local-to-global gap found.**

**Extension stability is real.** `ResourceSubtreeCertificate.sound` is
`∀ chi : Coloring T, ExtendsSubtree chi sigma → entry = levelParity (entryLevel chi H.headNode) → ResourceSubtreePostcondition …`.
The conclusions hold for **every** total colouring agreeing with the exact
subtree assignment — the formal content of "a later sibling cannot invalidate an
already-constructed child". The postcondition records all eight facts the audit
demanded: head colour, installation of the local helix word, proper exposure at
every paired node of the subtree, every grey pair at η, every target-unpaired
position at ξ, exact child-head port colours, the required terminal residue, and
the non-grey terminal colour in the L and two-demand cases.

**Domain ownership.** `helixMemberNodes_disjoint_outgoing` (local word ⟂ child
subtrees); `pairedHelixSubtree_outgoing_disjoint` (children pairwise disjoint);
`helixColoringComponentDomain_eq_subtree` (their union is *exactly*
`pairedHelixSubtree T H`, so every paired node in the parent subtree is covered
and no uncovered pair can receive a default colour). Merging uses
`flattenPartialColoringFamily`, whose "owner" index is proved unique under
pairwise disjointness (`partialColoringFamilyOwner_eq_of_mem`) — so **merge order
cannot overwrite a colour**. The unpaired side has its own exact decomposition
(`unpairedHelixSubtree_decomposition`), which is what formally rules out unpaired
children hanging off non-terminal helix members.

**Level independence is structural, not asserted.** `entryLevel` sums
`Color.delta` over `pairedAncestors v = {p | p strictly contains v}`. A sibling
subtree never strictly contains a node of another sibling, so it is never on that
node's root-to-node path and its colours simply do not appear in the sum. The
audit's requirement not to accept informal "siblings interact only at the parent"
language is met by construction: the only sibling interaction possible is the
parent's exposed multiset, which is itself pinned by `ChildPortsInstalled`.

**Termination.** Measure `helixSubtreePairCount T H = (pairedHelixSubtree T H).card`,
declared via `termination_by` / `decreasing_by`, with strict decrease at every
recursive child call proved by `helixSubtreePairCount_outgoing_lt` (the child's
paired subtree is a *strict* subset, since the parent's head node is in the
parent but not the child).

**Global assembly.** `rootPairedHelixSubtreeUnion_eq_univ` proves the root-child
subtrees cover **all** paired nodes; `rootSubtreeDomains_pairwiseDisjoint` proves
they are pairwise disjoint; so every target pair belongs to exactly one root-child
subtree — vacuously when the target has no pairs, which is the separate
degree-zero branch. `coloringOfRootSubtrees` converts the flattened family into a
**total** `Coloring T` via `toColoringOfDomainEqUniv`, using the domain-equals-univ
proof, so no default colour is ever assigned. `ProperColoring` and
`StrongTwoSeparatedWith` are then established globally, with root-unpaired
positions handled separately at exact level zero. No paired or unpaired position
escapes the global postcondition.

---

## 13. Final designability-composition assessment

**Correct, and the new construction is genuinely load-bearing.** The
machine-verified chain is

```
atMostTwoShortHelixDesignability
  → atMostTwoShortHelices_uniqueDesigns
      → globalColoringCertificateLeTwo
          → completeResourceRootAllocation / rootDegreeZeroColoring
              → constructedResourceSubtreeColoring
                  → constructResourceSubtree          ← the new resource recursion
      → uniqueDesigns_sequenceOfProperSeparatedColoring
```

All required nodes are **PRESENT** in the transitive closure.

**The old exact-one theorem is not a premise.** Every name on the old route —
`OneShortHelixDesignabilityStatement`, `globalColoringCertificate`,
`targetClass_admits_proper_strongTwoSeparated`, `assembledRootColoring`,
`rootForestAssembly`, `InTargetClassK`, `InTargetClassK2` — is **absent** from
the closure. The old proposition appears only as
`oneShortHelixDesignability_from_atMostTwo`, proved *after* and *from* the new
theorem through the hypothesis-level inclusion
`inTargetClassKLeTwo_of_inTargetClassK`. Exact-two, all-long and all-unpaired are
likewise corollaries, never premises. Short counts zero, one and two are all
handled by the one induction, as `SPECIFICATION.md` §1 demands.

**The generic no-tie theorem is unconditional.**

```lean
theorem uniqueDesigns_sequenceOfProperSeparatedColoring
    (χ : Coloring T) (hProper : ProperColoring χ) (hSeparated : Separated χ) :
    UniqueDesigns (sequenceOfProperColoring χ hProper) T
```

Hypotheses: a colouring, its properness, its separation. **No** helix-count
assumption, **no** target-class assumption, **no** saturation assumption on the
public competitor, **no** restriction on competitors. (`SaturatedStructure` occurs
inside the proof only on *constructed* paired restrictions, whose saturation is
proved.) It concludes exactly the public `UniqueDesigns` definition audited in
§6 of the mapping.

---

## 14. Proof-escape scan

Token-aware scan over the 46 bundled `RNA/**/*.lean` files, distinguishing code
from comments, strings, and English words:

| Token | Raw hits | Code-position hits |
|---|---|---|
| `sorry` | 0 | 0 |
| `admit` | 8 | **0** |
| `axiom` | 0 | 0 |
| `unsafe` | 0 | 0 |
| `sorryAx` | 0 | 0 |
| `native_decide` | 0 | 0 |

All eight `admit` hits are the ordinary English word "admits" in doc-comments or
in theorem names such as `targetClassLeTwo_admits_proper_strongTwoSeparated` —
classified individually, none is a tactic.

Also absent: `opaque`, `@[extern]`, `@[implemented_by]`, shell execution, network
calls, filesystem-dependent theorem bodies, external executables, foreign-function
proof oracles, hidden generated theorem source, `#eval`/`run_cmd`/macro or elab
metaprogramming, and custom axioms. `lakefile.toml` declares no `extern_lib`, no
`precompileModules`, no scripts, no custom targets. The bundle contains no
non-`.lean` file other than the five configuration/manifest/spec files. Imports
are only pinned Mathlib modules and sibling `RNA.*` modules — no circular or
foreign import. The only `set_option` anywhere is `autoImplicit false` (all 46
files), which tightens rather than weakens elaboration.

`#print axioms` gives `[propext, Classical.choice, Quot.sound]`. **Any unexplained
project-defined axiom would be a substantive failure; there are none.**

---

## 15. Non-vacuity controls

All seven required controls **PASS**, each kernel-decided (`decide`/`rfl`, never
`native_decide`), in temporary files outside the source tree. Detail and source
in `NONVACUITY_CHECKS.md`.

| # | Control | Result |
|---|---|---|
| 1 | all-unpaired target ∈ `InTargetClassKLeTwo` (and designable) | PASS |
| 2 | `(())` ∈ class (and designable) | PASS |
| 3 | exactly two length-two helices ∈ class (also `InTargetClassK2`, designable) | PASS |
| 4 | three length-two helices **rejected** | PASS |
| 5 | a length-one maximal helix **rejected** | PASS |
| 6 | nontrivial branching two-short target invokes the new resource theorem | PASS |
| 7 | `UniqueDesigns` **rejects** nested `(())` on `AUAU` because `()()` ties it | PASS |

Control 6 is the substantive one: `T14` = `(0,13)(1,12)(2,11)` enclosing
`(3,6)(4,5)` and `(7,10)(8,9)`, with no unpaired positions. Its terminal node
`(2,11)` is an **M endpoint of degree two whose two child subtrees both carry a
short helix** — exactly the two-demand `r = 2` configuration. The kernel confirms
`∃ H, H.length = 3 ∧ shortHelixSubtreeCount T14 H = 2`, so the parent is provably
long and the strengthened non-grey-closing transfer branch is the one that must
fire. `atMostTwoShortHelixDesignability` then yields a uniquely designing
sequence for it.

Control 7 is the sharpest fidelity check on the public definition: on `AUAU` the
*disjoint* fold `()()` is a distinct compatible noncrossing competitor with the
same pair count, so it ties the nested target and `UniqueDesigns` is false. A
definition that silently restricted competitors, or that used `≤` instead of `<`,
would have failed to reject here.

Beyond the seven, ~25 further exhaustive definitional controls were decided
(alphabet cardinality, the full compatibility table, F and Q as exact sets,
capacity bounds, every two-demand row, root rows, the `h=3` and `h=4` transfer
words, motif thresholds by `Iff.rfl`, adjacency admitted, crossings excluded).
All PASS.

---

## 16. Residual limitations

Full text in `RESIDUAL_LIMITATIONS.md`. In brief:

1. **Isolation deviation, disclosed:** the already-present pinned toolchain in
   the user's shared `~/.elan` was reused instead of re-downloaded into a private
   `ELAN_HOME`. That store holds only official `leanprover` binaries, not project
   source. `~/.elan/known-projects`, which does list prior project paths, was
   deliberately not read. No previous RNA repository, sibling project, Track A
   material, Track B computational report, or prior audit outcome was opened.
2. **Machine-checked vs. read:** the build, theorem type and term, axioms,
   `RNA.*` dependency closure, and all controls are kernel-checked. The
   *interiors* of the two long allocation case analyses (~765 lines total) were
   read rather than independently re-proved — but their fields are proof-carrying,
   so Lean would reject the definitions if any branch failed to discharge them.
3. **Tooling caveat:** Lean 4.34 seals theorem bodies from plain importers and
   `ConstantInfo.value?` returns `none` for theorems; the first dependency scan
   was therefore blind and gave false "absent" results. Diagnosed and corrected
   (`.thmInfo` destructuring plus `import all` for all 46 modules). Anyone
   reproducing this must apply both fixes.
4. **Trust base:** the pinned Lean toolchain, Mathlib and eight transitive
   dependencies were trusted as upstream; Mathlib `.olean`s came from the standard
   build cache. The Lean kernel itself was not audited. The textual escape scan
   covers only the bundled files; dependencies are covered instead by the
   kernel-level axiom result.
5. **Scope:** this audit concerns only logical completeness and fidelity of the
   Lean theorem to `SPECIFICATION.md`. It says nothing about the externally
   excluded claims (`SPECIFICATION.md` §9: the frozen legacy policy, the `n = 26`
   minimum and its compression lemma, K2 enumeration counts, automaton
   fixed-point equality, any Python certificate) — all confirmed absent from the
   dependency closure — and, by instruction, nothing about novelty, authorship,
   publication value, or scientific impact.

---

# VERDICT: FAITHFUL AND COMPLETE

Bundle integrity passes; the target module builds under the exact pinned
toolchain; the final theorem compiles; the specification and the Lean scientific
model match; the at-most-two target class matches exactly; zero, one and two
short helices are all covered by the single induction; the all-unpaired target is
covered; the F/Q resource proof is genuinely used; the strengthened long transfer
is correct including the `h = 4` boundary; the two-demand loop and root
allocations are correct on actual ordered slots; subtree certificates glue
without hidden cross-branch dependencies; the generic no-tie theorem applies
without a helix-count premise; and no proof escape or unexplained axiom occurs.
