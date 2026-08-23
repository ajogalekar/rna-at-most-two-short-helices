# Final PDF visual inspection

Inspection date: 2026-08-22

Result: **PASS**

## Frozen PDF

| Field | Value |
|---|---|
| File | `Designability_of_RNA_Targets_with_Up_to_Two_Length_2_Helices.pdf` |
| SHA-256 | `922b3dd4a1df2b1026d869e559f6e9567a6b07e808bb4969cf3eeb55998e5b07` |
| Pages | 31 |
| Page size | US letter, 612 by 792 points |
| PDF version | 1.5 |
| Encryption | none |

The PDF was built twice with Tectonic in a fresh temporary source directory
containing only the final TeX source, source-derived Lean listings, and bundled
font files.  The second clean pass is the frozen PDF.  The two passes have
different binary metadata timestamps but byte-identical extracted text.

## Automated render checks

- `pdfinfo` reports the expected title, author, 31 pages, and no encryption.
- `pdffonts` reports 27 font rows; every row is embedded, subset, and Unicode
  mapped.
- `pdftotext -layout` succeeds and contains the complete paper through all 13
  bibliography entries.
- The retained LaTeX log contains no overfull box, undefined citation,
  undefined reference, missing-character warning, or TeX error.
- Three underfull boxes occur in wrapped cells of the Appendix C artifact
  table.  Visual inspection confirms that these affect only loose spacing and
  do not clip, overlap, or obscure text.
- Tectonic reports three invalid-byte replacements in comments inside its
  bundled `algorithm2e.sty`; the generated algorithm and every manuscript
  glyph render correctly.

All 31 pages were rendered to PNG with `pdftoppm -png -r 120`.  Four contact
sheets were inspected for whole-document continuity, and critical text,
figures, listings, tables, and the bibliography were inspected at original
render resolution.  Two independent page-range inspections covered pages
1--16 and 17--31.  The final digest update changed rendered pixels only on
pages 24 and 30; both final pages were reinspected at original resolution.

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
| 30 | Repeated artifact-table header, availability statement, acknowledgments, start of references | PASS |
| 31 | Remaining bibliography, all 13 entries and DOI lines | PASS |

No clipping, overlap, illegible glyph, broken figure, broken table, bad page
break, or other publication-blocking visual defect was found.
