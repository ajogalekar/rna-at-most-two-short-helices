# RNA targets with at most two short helices — Lean formalization

This repository machine-checks universal unique designability for the strict
four-letter Watson–Crick maximum-base-pair model when a pseudoknot-free target
avoids `m5` and `m3dot`, has no maximal helix of length one, and has at most two
maximal helices of length two. Every other maximal helix has length at least
three.

The final public declaration is:

```lean
RNA.atMostTwoShortHelixDesignability :
  RNA.AtMostTwoShortHelixDesignabilityStatement
```

Unfolding the statement gives:

```lean
∀ {n : Nat} (T : SecondaryStructure n),
  InTargetClassKLeTwo T →
    ∃ w : Sequence n, UniqueDesigns w T
```

`UniqueDesigns w T` compares `T` with every compatible noncrossing partial
matching on the same complete sequence `w` and requires every distinct
competitor to have strictly fewer pairs. Energy remains exactly
`-pairCount`, so `atMostTwoShortHelices_uniqueMinimumEnergy` provides the
equivalent unique-minimum-energy formulation.

## Scope and proof architecture

The at-most-two theorem directly includes short-helix counts zero, one, and
two, including the all-unpaired target. It is not proved by dispatching to old
zero- or exact-one designability theorems. Instead, the new resource induction
uses:

- `shortHelixCount` and the exact subtree decomposition
  `shortHelixSubtreeCount_decomposition`;
- full and restricted interface resources `InF` and `InQ`;
- the explicit strengthened transfer
  `longTransfer_eta_closesNonGrey_of_Q`;
- actual child-slot allocations for zero, one, or two resource-positive
  subtrees;
- `constructResourceSubtree`, an exact-domain extension-stable recursion on
  `helixSubtreePairCount`;
- an explicit root-degree-zero empty-coloring branch and resource-aware
  positive-degree root assembly; and
- the previously kernel-checked generic theorem
  `uniqueDesigns_sequenceOfProperSeparatedColoring`.

The completed exact-one theorem and every original public model declaration
remain unchanged. The downstream class inclusion is used only to recover
`oneShortHelixDesignability_from_atMostTwo` as a corollary of the new theorem.

The corrected frozen proof specification is
[`docs/CANONICAL_AT_MOST_TWO_PROOF.md`](docs/CANONICAL_AT_MOST_TWO_PROOF.md),
with SHA-256 recorded in
[`docs/CANONICAL_AT_MOST_TWO_PROOF_SHA256.txt`](docs/CANONICAL_AT_MOST_TWO_PROOF_SHA256.txt).
The implementation report, statement audit, and axiom audit are:

- [`docs/AT_MOST_TWO_FORMALIZATION_REPORT.md`](docs/AT_MOST_TWO_FORMALIZATION_REPORT.md)
- [`docs/AT_MOST_TWO_FINAL_STATEMENT_AUDIT.md`](docs/AT_MOST_TWO_FINAL_STATEMENT_AUDIT.md)
- [`docs/AT_MOST_TWO_AXIOM_AUDIT.md`](docs/AT_MOST_TWO_AXIOM_AUDIT.md)
- [`docs/AT_MOST_TWO_RELEASE_MANIFEST.md`](docs/AT_MOST_TWO_RELEASE_MANIFEST.md)

## Main modules

The additive implementation is under `RNA/AtMostTwoShort/`:

- `TargetClass.lean` — presentation-independent short count and target class;
- `ShortCount.lean` — exact subtree/root decompositions and support bounds;
- `Interface.lean` — F/Q resources and `RequiredInterface`;
- `Transfers.lean` — allowed-length dispatch and strengthened long transfer;
- `ResourceAllocations.lean` — actual E/L/M child-slot allocations;
- `ResourceRoot.lean` — root rows, degree-zero certificate, and `G,G,B` case;
- `ResourceCertificate.lean` — exact-domain extension-stable invariant;
- `SubtreeConstruction.lean` — well-founded resource recursion;
- `GlobalColoring.lean` — total proper strongly two-separated coloring;
- `Designability.lean` — final theorem and requested corollaries;
- `Examples.lean` — positive constructions and negative class controls; and
- `AxiomAudit.lean` — transitive kernel dependency inspection.

## Pinned toolchain and provenance

- Downstream base commit:
  `c37eac40ef5a28bf5733fd576ce6d4c44091ee6a`
- Corrected specification commit:
  `020fa8cd54f64c3e7264fd9dcab7ac11e6b671bc`
- Working branch: `at-most-two-short-helices`
- Lean: `4.34.0-rc1`
- Mathlib requirement: `v4.34.0-rc1`
- Mathlib resolved revision:
  `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`

The exact-one source repository is the immutable upstream baseline. This
repository was cloned without hard links and adds the new development
downstream.

## Build and audit

From the repository root:

```bash
source /Users/ashujo/.elan/env
lake clean
lake build
lake build RNA.AtMostTwoShort.AxiomAudit
```

The final theorem's kernel-reported transitive axiom set is:

```text
[propext, Classical.choice, Quot.sound]
```

No project-defined axiom, admission, `sorry`, unsafe mathematical proof,
`native_decide`, or external proof oracle is used. Ordinary kernel-checked
`decide`, finite case analysis, well-founded recursion, and classical choice
are used where appropriate.

Useful final checks are:

```bash
rg -n --glob '*.lean' '\b(sorry|admit|axiom|unsafe|sorryAx|native_decide)\b' RNA RNA.lean
git diff --check
git status --short
```

The raw substring `admit` also occurs inside English “admits” and theorem
identifiers, while `axiom` occurs in audit comments and `#print axioms`;
[`docs/AT_MOST_TWO_AXIOM_AUDIT.md`](docs/AT_MOST_TWO_AXIOM_AUDIT.md)
classifies those non-code matches.
