# Designability of RNA Targets with Up to Two Length-2 Helices

This repository contains the Lean 4 formalization, manuscript source,
DOI-bearing publication PDF, executable examples, and reproducibility records for a
universal unique-designability theorem in the strict four-letter
Watson–Crick maximum-base-pair model.

## Publication status

- Canonical repository: <https://github.com/ajogalekar/rna-at-most-two-short-helices>
- Publication branch: `final-publication-release`
- Qualified Lean-source commit (before publication-only additions):
  `f8076891735ff7bff07e785c37aad63855c6745a`
- Version: `1.0.0`
- Archival DOI: [10.5281/zenodo.22075874](https://doi.org/10.5281/zenodo.22075874)
- Current paper: qualified DOI-bearing publication artifact
- Human expert review: the manuscript and formal proof have not yet been
  reviewed by an independent human subject-matter expert

The canonical GitHub repository is public. The immutable Zenodo Software
record for version `1.0.0` is published under the archival DOI above.

## Main theorem

The public declaration is:

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

The target is a pseudoknot-free secondary structure that avoids `m5` and
`m3dot`, has no maximal helix of length one, and has at most two maximal
helices of length two; every other maximal helix has length at least three.
`UniqueDesigns w T` compares `T` with every compatible noncrossing partial
matching on the same complete sequence `w` and requires every distinct
competitor to have strictly fewer pairs. Energy is exactly `-pairCount`.

The theorem directly covers zero, one, or two length-2 helices, including the
all-unpaired target. The exact theorem type and formal-model audit are recorded
in [the statement audit](docs/AT_MOST_TWO_FINAL_STATEMENT_AUDIT.md).

## Repository map

- `RNA.lean` and `RNA/` — complete handwritten Lean project; the additive
  at-most-two construction is under `RNA/AtMostTwoShort/`.
- `paper/` — manuscript TeX and qualified PDF, source-derived Lean listings,
  example verifier, STIX fonts, supplements, and paper-specific audits.
- `scripts/` — theorem-source token, integrity, and formalization-metrics
  checks.
- `docs/` — proof specification, theorem-closure hashes, build evidence,
  formalization reports, and model-fidelity audits.
- `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` — pinned Lean,
  Lake, and Mathlib environment.
- `CITATION.cff` and `.zenodo.json` — synchronized version `1.0.0` software
  metadata carrying the published version DOI.

The frozen proof specification is
[docs/CANONICAL_AT_MOST_TWO_PROOF.md](docs/CANONICAL_AT_MOST_TWO_PROOF.md).
Its hash and the complete 46-file dependency closure are pinned in `docs/`.

## Reproduce the formal checks

With the pinned Lean toolchain available through Elan, run from the repository
root:

```bash
lake build
lake build RNA.AtMostTwoShort.AxiomAudit
lake build RNA.AtMostTwoShort.PublicationExamples
lake build RNA.AtMostTwoShort.PublicationExamplesAxiomAudit

python3 scripts/audit_handwritten_lean_tokens.py
python3 scripts/audit_source_integrity.py
python3 scripts/measure_formalization.py
python3 paper/verify_examples.py
```

Check the 46-file theorem-closure identity with one of:

```bash
# macOS
shasum -a 256 -c docs/THEOREM_CLOSURE_BASELINE.sha256

# GNU/Linux
sha256sum -c docs/THEOREM_CLOSURE_BASELINE.sha256
```

For the coupled paper-source check (including regenerated Lean listings and a
fresh Tectonic PDF build), install Tectonic and run:

```bash
bash paper/scripts/validate_manuscript_sources.sh .
```

The final theorem's kernel-reported transitive axiom set is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No project-defined axiom, admission, `sorry`, unsafe mathematical proof,
`native_decide`, or external proof oracle is used. Ordinary kernel-checked
`decide`, finite case analysis, well-founded recursion, and classical choice
are used where appropriate.

## Pinned environment and provenance

- Lean: `4.34.0-rc1`
- Mathlib requirement: `v4.34.0-rc1`
- Mathlib resolved revision:
  `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`
- Immutable exact-one upstream baseline:
  `c37eac40ef5a28bf5733fd576ce6d4c44091ee6a`
- Theorem-closure baseline:
  `28070dd0032f417b1eed03a1fa23f81a260eaff7`

See [docs/THEOREM_CLOSURE_IDENTITY_REPORT.md](docs/THEOREM_CLOSURE_IDENTITY_REPORT.md)
and [docs/AT_MOST_TWO_RELEASE_MANIFEST.md](docs/AT_MOST_TWO_RELEASE_MANIFEST.md)
for the qualified-source identity and audit trail.

## Licensing and citation

The repository uses a required path-based license split:

- Lean source and software tools: Apache License 2.0;
- manuscript text, original TikZ figures, and project documentation:
  Creative Commons Attribution 4.0 International; and
- bundled STIX fonts: STIX Font License / SIL Open Font License 1.1 terms.

The root [LICENSE](LICENSE) is the exact Apache-2.0 text so GitHub and Zenodo
identify the software license correctly. [LICENSES.md](LICENSES.md) gives the
authoritative file-by-file scope and links to all license texts.

Use [CITATION.cff](CITATION.cff) to cite version `1.0.0` of the formal artifact
at DOI [10.5281/zenodo.22075874](https://doi.org/10.5281/zenodo.22075874).
For exact source identity, also record the Git commit used.

Redundant source ZIPs and frozen qualification bundles are intentionally not
duplicated in Git history. The canonical version `1.0.0` archive and its
evidence packages are deposited through Zenodo; any GitHub release remains a
separate action.
