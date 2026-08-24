# Final PDF visual inspection

Inspection date: 2026-08-23 (local); release date: 2026-08-24 (UTC)

Result: **PASS**

## Frozen PDF

| Field | Value |
|---|---|
| File | `Designability_of_RNA_Targets_with_Up_to_Two_Length_2_Helices.pdf` |
| SHA-256 | `81f01e4f2d3d3f22012bde27555d563caa941a9789dc451f6c9067b2ad07868e` |
| Pages | 31 |
| Size | 235,469 bytes |
| Page size | US letter, 612 by 792 points |
| PDF version | 1.5 |
| Encryption | none |

The PDF was built twice with Tectonic from the final source-derived Lean
listings and bundled font files, using `SOURCE_DATE_EPOCH=1787529600`
(2026-08-24 00:00:00 UTC).  Both builds produced byte-identical PDFs with the
SHA-256 digest above.

## Automated render checks

- `pdfinfo` reports the expected title, author, 31 pages, and no encryption.
- `pdffonts` reports 27 font rows; every row is embedded, subset, and Unicode
  mapped.
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

All 31 pages were rendered to PNG with `pdftoppm -png -r 120`.  Four contact
sheets were inspected for whole-document continuity, and critical text,
figures, listings, tables, and the bibliography were inspected at original
render resolution.  Pages 25, 30, and 31 were additionally reinspected at
original resolution after the DOI, repository URL, version, licenses, and
release identifiers were finalized.

## Page-by-page visual result

| Pages | Material checked | Result |
|---|---|---|
| 1--4 | Title, abstract, contribution box, Figure 1, opening definitions | PASS |
| 5--8 | Motif and target-class tables, Unicode/math notation, Lemma 2.9, strengthened Proposition 3.5 | PASS |
| 9--12 | Loop lemmas, Figure 2, feasible-state displays, transition tables | PASS |
| 13--16 | Figure 3, root-assignment tables, Algorithm 1, sequence construction | PASS |
| 17--19 | Counting and uniqueness proofs, equations, page continuations | PASS |
| 20--22 | Both worked examples, long RNA strings, Figures 4 and 5 | PASS |
| 23--25 | Exact public Lean listing, axiom audit, metrics digest, green identifier box | PASS |
| 26--27 | Scope, limitations, conclusion, Appendix A tables | PASS |
| 28--29 | Unicode Lean listings, listing continuation, start of artifact table | PASS |
| 30 | Artifact-table completion, acknowledgments, and data/code availability with repository and DOI | PASS |
| 31 | Complete bibliography, all 13 entries and DOI lines | PASS |

No clipping, overlap, illegible glyph, broken figure, broken table, bad page
break, or other publication-blocking visual defect was found.
