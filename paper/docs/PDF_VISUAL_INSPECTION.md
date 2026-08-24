# Final PDF visual inspection

Inspection date: 2026-08-24 (local); release date: 2026-08-24 (UTC)

Result: **PASS**

## Frozen PDF

| Field | Value |
|---|---|
| File | `Designability_of_RNA_Targets_with_Up_to_Two_Length_2_Helices.pdf` |
| SHA-256 | `ef8ff08b36f1e9185b79170904ff5f6dfb70df3a202f7ab6d29c60a9b889c57c` |
| Pages | 32 |
| Size | 257,098 bytes |
| Page size | US letter, 612 by 792 points |
| PDF version | 1.5 |
| Encryption | none |

The PDF was built twice with Tectonic from the final source-derived Lean
listings and bundled font files, using `SOURCE_DATE_EPOCH=1787529600`
(2026-08-24 00:00:00 UTC).  Both builds produced byte-identical PDFs with the
SHA-256 digest above.

## Automated render checks

- `pdfinfo` reports the expected title, author, 32 pages, and no encryption.
- `pdffonts` reports 30 font rows; every row is embedded and subset.  Twenty-nine
  rows are Unicode mapped; the remaining row is the embedded mathematical-symbol
  font `CMSY8`, whose displayed glyphs were visually verified.
- `pdftotext -layout` succeeds and contains the complete paper through all 13
  bibliography entries.
- The retained LaTeX log contains no overfull box, undefined citation,
  undefined reference, missing-character warning, or TeX error.
- Seven underfull boxes occur in wrapped material in the release-identifier
  box and Appendix C artifact table.  Visual inspection confirms that these
  affect only loose spacing and do not clip, overlap, or obscure text.
- Tectonic reports three invalid-byte replacements in comments inside its
  bundled `algorithm2e.sty`; the generated algorithm and every manuscript
  glyph render correctly.

All 32 pages were rendered to PNG with `pdftoppm -png -r 105`.  Three contact
sheets were inspected for whole-document continuity, and critical text,
figures, listings, tables, and the bibliography were inspected at original
render resolution.  Pages 1--5 were additionally inspected after Sections
1.2--1.3 were expanded and the new three-panel color figure was added.  Pages
14, 22, 23, and 29--32 were reinspected at original resolution to confirm the
later figures, listings, artifact records, repository and DOI, availability
statement, and complete bibliography after pagination changed.

## Page-by-page visual result

| Pages | Material checked | Result |
|---|---|---|
| 1--5 | Title, revised abstract and expert-review disclosure; expanded Sections 1.2--1.3; new color Figure 1; contribution box, proof pipeline, and opening definitions | PASS |
| 6--9 | Tree, helix, motif, target-class, color, and prior-result definitions; strengthened three-stack boundary | PASS |
| 10--13 | Loop lemmas, feasible-state displays, complete length-2 table, and long-helix transfers | PASS |
| 14--17 | Detailed two-child allocation figure, assignment tables, Algorithm 1, and global coloring | PASS |
| 18--21 | Sequence construction, inventory and uniqueness proofs, theorem conclusion, and first example | PASS |
| 22--23 | Both two-stack configurations, long RNA strings, and worked-example figures | PASS |
| 24--26 | Exact public Lean listing, axiom audit, metrics digest, green identifier box, and audit records | PASS |
| 27--28 | Development history, scope, limitations, conclusion, and Appendix A tables | PASS |
| 29--30 | Unicode Lean listings, listing continuation, and start of artifact table | PASS |
| 31 | Artifact-table completion, acknowledgments, and data/code availability with repository and DOI | PASS |
| 32 | Complete bibliography, all 13 entries and DOI lines | PASS |

No clipping, overlap, illegible glyph, broken figure, broken table, bad page
break, or other publication-blocking visual defect was found.
