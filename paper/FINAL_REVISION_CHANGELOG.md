# Final revision changelog

Date: 2026-08-22

> **Historical-record notice (2026-08-24 UTC).** This document preserves the
> prepublication revision state. Its statements that the repository URL, DOI,
> and public-source licenses were pending are superseded by the version 1.0.0
> release metadata in `../README.md`, `../CITATION.cff`, and `../LICENSES.md`.
> The version DOI is `10.5281/zenodo.22075874`; the public GitHub repository
> and immutable Zenodo Software record are the final release endpoints.

This changelog records the final mathematical, editorial, citation, formal-artifact, and packaging revision. Exact values that depend on the final assembled bytes or a fresh timed build are recorded in the final release manifest and metrics report; no provisional package digest or build metric is asserted here.

## Post-audit exposition revision (2026-08-24)

| area | change | validation |
|---|---|---|
| Haleš coloring framework | Expanded Section 1.2 to spell out the interval tree, exposed-color capacities, greedy top-down coloring, inclusive levels, separation condition, color-to-sequence map, and why the original structure-approximation repair does not prove designability of the unchanged target. | Claims were checked against the primary Haleš et al. source and the manuscript's formal definitions and self-contained uniqueness proof. |
| Isolated-stack gap | Expanded Section 1.3 with the complete four-row length-2 transition table, the restricted entry-state guarantee, the three-gray multiloop collision, the scope caveat, and the strengthened non-gray-ending repair forced available by the global bound of two. | The transition words and exposures were checked against Lemmas 6.1--6.3 and the formal target-class decomposition; specialist audits reported no remaining mathematical overclaim. |
| Explanatory color figure | Added a three-panel TikZ figure showing a proper separated-coloring certificate and nucleotide map, the naive three-gray collision, and the `GBB` long-helix repair. Every decisive state is explicitly labeled so the figure remains interpretable without color. | Full-resolution inspection found no clipping, overlap, overfull box, illegible glyph, or color-dependent inference. |
| Regenerated artifact | Rebuilt the manuscript from source with the frozen Lean listings and deterministic timestamp. | Coupled source/Lean validation passes; two builds are byte-identical; all 32 pages render; all 30 font records are embedded and subset. The final digest is recorded in `docs/FINAL_PDF_CONTENT_STABILITY.txt`. |

## Mathematical revisions

| area | change | validation |
|---|---|---|
| Three-isolated-stack boundary | Strengthened Proposition 3.5 from failure of the manuscript's uniform-residue construction to failure of **every** proper modulo-2 separated coloring of `((.))((.))((.))`. Added the nonvacuity lemma relating modulo-2 separation to uniform residue form. Replaced the earlier sufficiency-based impossibility argument with a necessity proof from the complete length-2 transition table and the forced terminal-loop residue. | Exhaustive search of all (3^6=729) colorings: 180 proper, 36 proper and ordinarily separated, zero proper and modulo-2 separated. Lean kernel reduction independently proves the strong finite nonexistence statement. |
| Boundary caveat | Preserved the sharp limitation: the same target has the proper ordinarily separated helix words `BB`, `WW`, `GB` and is uniquely designed by `GGACCCCAGGAGACU`. The result is therefore a boundary for modulo-2 separation, not for ordinary separation or designability. | Exact optimum-count DP: target pairs 6, optimum 6, optimum count 1; gray levels `{0}` and unpaired levels `{-2,1,2}`. |
| Deterministic roots | Fixed the residue convention completely: unpaired-root case ξ = 0; no-unpaired root of degree at most two ξ = 0; no-unpaired root of degree three or four η = 0 and ξ = 1. The algorithmic discussion now names all remaining fixed symmetric choices required for determinism. | Root cases cross-checked against the root assignment table and both worked examples. |
| Internal (r=2) example | Reconstructed (T_2) under the deterministic small-root convention. The retained sequence is `GGGAGGAGCUUGCACCUGGGCCCCCC`, with helix words `BBB`, `GBB`, `GB`, `GB`, `BBB`. The review's `GGGGGAGGCCCCGGUCCAGGCCUCCC` is documented as valid and uniquely designing but not as an (F/Q)-recursive realization of the strengthened internal transfer. | Exact color/level reconstruction gives ξ = 0, η = 1 and levels `[[1,2,3],[3,4,5],[5,6],[5,6],[4,5,6]]`; properness passes; optimum-count DP returns 13 pairs and one optimum; downstream Lean proves the literal design theorem and named-residue/color facts. |
| Strengthened transfer exposition | Clarified that (Q) prescribes gray as the first color at an η entry and that (a) is the free trailing non-gray color, fixed as black. Removed the undefined (h=4) stabilization remark. | Checked row-by-row against the strengthened transfer table and the internal example. |

## Formal verification and source hardening

| area | change | validation |
|---|---|---|
| Exact public listing | Replaced retyped Lean-like text with the exact Unicode public proposition, theorem, and proof term extracted from the frozen source. | Full-source digest checks and declaration-block digest checks pass. |
| Appendix listings | Replaced simplified excerpts, including the genuinely invalid/semantically unsuitable `not` and `!=` forms, with exact Unicode declarations from the frozen alphabet, structure, helix, motifs, target-class, and theorem modules. The review's separate claim that ASCII `forall`, `exists`, and `->` do not compile was corrected: those forms are accepted by the pinned toolchain. | The generated audit module imports the real theorem module and `#check`s all 28 displayed declarations successfully under Lean 4.34.0-rc1. |
| Reproducible listing pipeline | Added a hash-pinned extractor, declaration-level source map, generated listing files, generated `#check` audit module, and a human-readable listing check record. | `scripts/extract_paper_lean_listings.py` validates six frozen source files before extraction; `paper_listings/LEAN_LISTING_CHECKS.md` records the successful run. |
| Publication semantic examples | Added downstream-only Lean theorems for (T_1), corrected (T_2), the three-stack boundary, a length-1 rejection control, and the `AUAU` tied-fold negative control. Added a separate axiom-audit module. | `lake build RNA.AtMostTwoShort.PublicationExamples`, `lake build RNA.AtMostTwoShort.PublicationExamplesAxiomAudit`, and `lake build RNA.AtMostTwoShort.Designability` all pass. Publication endpoints report exactly `[propext, Classical.choice, Quot.sound]`. |
| Frozen theorem closure | Kept the audited theorem source and dependency closure unchanged; the two semantic-example modules are downstream-only and are not imported by the theorem. | Before/after SHA-256 maps agree for all 60 pre-existing tracked Lean files; the import-direction audit passes. See `docs/THEOREM_CLOSURE_IDENTITY_REPORT.md` in the Lean repository. |
| Independent executable examples | Replaced the earlier checker with a deterministic, standard-library-only exact checker covering target compatibility, Nussinov optimum and optimum count, decoded colors and levels, exposed-multiset properness, the full three-stack coloring space, and a tied-fold control. | `python3 verify_examples.py` passes every test; exact output is frozen in `EXAMPLE_VERIFICATION.txt` and interpreted in `docs/FINAL_EXAMPLE_VERIFICATION.md`. |

## Evidence language and disclosure

| area | change | validation |
|---|---|---|
| Audit description | Replaced language that could imply a human third party with “blinded automated audit by an independent AI session.” Replaced “primary verdict” with “recorded verdict.” | Complete-source terminology inspection finds no claim of independent human review. |
| Evidence hierarchy | Ranked, in order, kernel acceptance; isolated reconstruction; source-integrity, dependency, and axiom audits; the automated specification comparison; and finite checks and negative controls. Stated that the AI cross-check does not replace kernel checking, reproducibility, public inspection, or human peer review. | The hierarchy appears consistently in the abstract, introduction, formal-verification section, development history, conclusion, and artifact appendix. |
| Scope of formal evidence | Added explicit limits: formal verification does not establish biological realism, novelty, importance, empirical utility, or claims outside the formal model. | Wording checked against the formal theorem and the documented audit scope. |

## Citation and related-work revisions

| area | change | validation |
|---|---|---|
| Inverse-folding methods | Rewrote the methods survey so each modality has a matching source: RNAinverse, RNA-SSD, INFO-RNA, RNAiFold, and NUPACK ensemble-defect optimization. Removed the unsupported learned-generator phrase. | Primary-source records and wording-match decisions are documented in `docs/CITATION_AUDIT.md`. |
| Added primary sources | Added Hofacker et al. for RNAinverse and García-Martín et al. for RNAiFold; retained the RNA-SSD, INFO-RNA, and NUPACK ensemble-defect sources. Added or verified the named Nussinov DP, Turner nearest-neighbor context, Lean 4, and exact-seeding/biseparability sources where used. | Bibliographic metadata and DOI values were checked against publisher, proceedings, author-manuscript, or official records. |
| Existing citations | Corrected the WABI proceedings description, distinguished the 2024 conference result from the stronger 2025 journal result, qualified the Bonnet et al. hardness claim, and changed historical-priority wording about the Haleš model to the supported “studied” wording. | Each claim has an explicit match or qualification verdict in the citation audit. |
| Novelty boundary | Standardized the search cutoff to 19 August 2026 and stated twice that failure to locate prior work is not proof of novelty. | Date and qualification are identical in §§3 and 16.3. |

## Editorial and presentation revisions

| area | change | validation |
|---|---|---|
| Terminology | Standardized manuscript prose on “length-2”; retained “isolated stack” as the scientific synonym. Explained why the apparently redundant no-length-1 target condition is retained. | Text search finds no `length-two` occurrence; the explanation is checked against the frozen target predicate. |
| Proper-coloring gloss | Separated the root capacity statement from the nonroot parent-child equivalence and included the capacity qualifications needed for correctness. | Checked directly against the exposed-multiset definition for all parent colors and the root. |
| Prose repairs | Fixed “are containing,” repaired the garbled Appendix A.2 sentence, clarified schematic versus actual child order, and removed the undefined stabilization aside. | Targeted searches find none of the superseded wording. |
| Organization and figures | Updated the organization paragraph to include the development/audit section and conclusion. Added in-body references and interpretation for Figures 1, 3, 4, and 5. | Section-label cross-check and figure label/reference search pass. |
| Worked examples | Updated (T_2), its residue choice, sequence, color words, levels, figure labels, and explanatory text consistently. Added an explicit comparison with the valid but nonrecursive review sequence. | Manuscript values match the exact checker and downstream Lean theorems. |

## Artifact and release packaging

| area | change | validation/status |
|---|---|---|
| Artifact names | Standardized names to **canonical source archive**, **release-qualification results package**, **blinded fidelity bundle**, **Claude fidelity-audit package**, and **manuscript source package**. | Names are synchronized across §14, Appendix C, availability text, and release documentation. |
| Fixed artifact identities | Preserved the already validated identifiers for the frozen proof specification and qualification/audit packages. | Values are reproduced only where a corresponding byte artifact and checksum record exist. |
| Metrics and final byte identities | Added a release-metrics and final-manifest step for Lean source size, declaration counts, fresh clean-build wall-clock, final package membership, and package digests. | Exact final values are recorded in the final metrics report and manifest; this changelog intentionally does not duplicate values that depend on the final assembled bytes. |
| Availability status | Kept `\RepositoryURL` and `\ArchiveDOI` as explicit pending placeholders and identified selection of an explicit public-source license as a third blocker. The generated PDF is labeled prepublication, not submission-ready. | No repository URL, DOI, or license was fabricated. Public availability can be asserted only after those fields are supplied and the released bytes are deposited. |
| Release contents | The release layout includes manuscript source and PDF, exact derived listings and their checks, deterministic example checker and output, response and changelog records, citation/provenance audits, downstream publication examples, and the frozen qualification packages. | Final membership and SHA-256 values are recorded by the external release manifest after assembly, avoiding circular self-digests. |

## Publication status

The mathematics, worked examples, source-derived listings, semantic regression theorems, review response, citation audit, and artifact provenance have been hardened for release. The release remains **prepublication only** until a permanent repository URL, archival DOI, and explicit public-source license are supplied. Those are metadata and availability blockers, not mathematical exceptions, and no placeholder has been promoted to a factual claim.
