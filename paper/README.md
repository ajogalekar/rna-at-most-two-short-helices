# Manuscript source package

This directory contains the revised manuscript source, its rendered DOI-bearing
PDF, reproducible source-derived Lean material, and the review and verification
records used to qualify the publication files.

## Main files

- `Designability_of_RNA_Targets_with_Up_to_Two_Length_2_Helices.tex` is the
  LaTeX source. All figures are drawn in TikZ.
- `Designability_of_RNA_Targets_with_Up_to_Two_Length_2_Helices.pdf` is the
  rendered manuscript.
- `verify_examples.py` is a standard-library exact Nussinov optimum-and-count
  checker for all worked examples and negative controls reported in the paper.
- `EXAMPLE_VERIFICATION.txt` is the pinned expected checker output.
- `check_dot_bracket_literals.py` extracts every dot-bracket literal from the
  manuscript and validates it with the same exact parser; its pinned output is
  `DOT_BRACKET_LITERAL_AUDIT.txt`.
- `generated/publication_example_literals.tex` is emitted from the actual Lean
  values of `w1` and `w2` by `scripts/ExportPublicationExampleLiterals.lean`;
  the manuscript imports those macros instead of retyping the sequences.
- `ARXIV_METADATA.md` records the prepared categories, trimmed abstract,
  comments field, and confirmed endorsement status. It is preparation only and
  does not authorize an arXiv submission.
- `FINAL_CLAUDE_REVIEW.md`, `RESPONSE_TO_FINAL_CLAUDE_REVIEW.md`, and
  `FINAL_REVISION_CHANGELOG.md` preserve the review and point-by-point response.
- `SHA256SUMS.txt` records final digests for every distributed file except
  itself.

The `paper_listings/` directory contains 42 exact Unicode declaration blocks,
their source map, and a Lean `#check` audit. The `scripts/` directory contains
the deterministic extractor and the end-to-end manuscript validator. The
`supplement/` and `docs/` directories contain the theorem, citation, example,
and provenance audits. The bundled STIX fonts and their license are in
`fonts/` so the Unicode listings render reproducibly.

## Reproduction

The manuscript uses `fontspec`; build it with Tectonic (or another XeTeX-based
engine), from this directory:

```bash
SOURCE_DATE_EPOCH=1787529600 tectonic --keep-logs \
  Designability_of_RNA_Targets_with_Up_to_Two_Length_2_Helices.tex
```

Run and compare the computational checks with:

```bash
python3 verify_examples.py
python3 verify_examples.py > /tmp/example-verification.txt
diff -u EXAMPLE_VERIFICATION.txt /tmp/example-verification.txt
python3 check_dot_bracket_literals.py
python3 check_dot_bracket_literals.py > /tmp/dot-bracket-literals.txt
diff -u DOT_BRACKET_LITERAL_AUDIT.txt /tmp/dot-bracket-literals.txt
```

The manuscript directory is `paper/` inside the canonical Lean repository.
Regenerate and semantically check the displayed Lean declarations from this
directory with:

```bash
LEAN_REPO=..
python3 scripts/extract_paper_lean_listings.py \
  --repo "$LEAN_REPO" \
  --output paper_listings

MANUSCRIPT_DIR="$PWD"
(cd "$LEAN_REPO" && \
  lake build RNA.AtMostTwoShort.Designability && \
  lake env lean "$MANUSCRIPT_DIR/paper_listings/PaperLeanListingAudit.lean")
```

Regenerate the publication-example sequence macros from the actual Lean
definitions with:

```bash
MANUSCRIPT_DIR="$PWD"
(cd .. && lake env lean --run \
  "$MANUSCRIPT_DIR/scripts/ExportPublicationExampleLiterals.lean") \
  > generated/publication_example_literals.tex
```

The coupled release validation runs extraction, all 42 Lean checks, the exact
example-output comparison, terminology and cross-reference scans, and the
Tectonic manuscript build in one command:

```bash
bash scripts/validate_manuscript_sources.sh ..
```

The validator also accepts the Lean tree through `RNA_LEAN_REPO`; without an
argument or environment variable it defaults to the repository parent of this
`paper/` directory.

## Release status

Published version `1.0.2` is fixed in the canonical repository at
<https://github.com/ajogalekar/rna-at-most-two-short-helices> and under DOI
<https://doi.org/10.5281/zenodo.22100052>. It adds the comprehensive AI-use
disclosure in the dedicated manuscript section, removes the shorter AI-use
sentence from both abstracts, preserves the Lean-derived publication
sequences and expanded Appendix B, and corrects the release metadata's theorem
scope. The GitHub and Zenodo release assets are byte-synchronized; the arXiv
package is built from the same manuscript source.
At the time of this release, the manuscript and formal proof have not yet been
reviewed by an independent human subject-matter expert.
The authoritative license scopes are fixed in `../LICENSES.md`. Exact
frozen-input identifiers are recorded in `docs/INPUT_PROVENANCE.md`, and
distributed-file digests are recorded in `SHA256SUMS.txt`.
