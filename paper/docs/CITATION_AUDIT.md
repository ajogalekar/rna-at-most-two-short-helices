# Final post-edit citation audit

**Manuscript:** Designability_of_RNA_Targets_with_Up_to_Two_Length_2_Helices.tex

**Audit date:** 2026-08-22

> **Historical-record notice (2026-08-24 UTC).** This audit preserves the
> prepublication citation-review state. Its release-blocker paragraph is
> superseded by the version 1.0.0 metadata in `../../README.md`,
> `../../CITATION.cff`, and `../../LICENSES.md`. The version DOI is
> `10.5281/zenodo.22075874`; the public GitHub repository and immutable Zenodo
> Software record are the final release endpoints.

**Status:** **PASS — no open citation-scope corrections**

**Bibliography state:** 13 entries, all cited

## Final verdict

The manuscript's citation revision is complete. The current source contains 13
bibliography entries and cites all 13. There are no undefined citation keys, no
uncited bibliography entries, no duplicate bibliography keys, and no citation
warnings in the current LaTeX log.

The earlier LEARNA recommendation is resolved by deletion: the manuscript no
longer claims to cover “learned sequence generators,” does not mention LEARNA,
and therefore does not require the Runge et al. reference. This is not an
unsupported clause left in the paper. The only remaining occurrence of
“generators” concerns a mathematical free-group encoding and is unrelated to
learned RNA design.

All previously identified wording and attribution issues are resolved:

- WABI 2024 is correctly identified as the 24th workshop.
- The Bonnet hardness statement is narrowed to RNA Design Extension with
  prescribed nucleotide constraints.
- The inverse-folding methods paragraph maps each retained method to an
  appropriate primary source.
- Haleš et al. are described as studying the model, without an unsafe priority
  claim.
- The WABI and 2025 journal results are distinguished.
- The bounded-isolated-stack question is presented as motivation of the
  present paper, not as an open problem explicitly stated by Boury et al.
- Biseparability and exact seeding cite the RECOMB 2025 paper.
- Nussinov dynamic programming and Turner nearest-neighbor thermodynamics have
  primary citations.
- The Lean 4 paper is used only for Lean itself; artifact-specific verification
  claims rely on the release record rather than on the language paper.

The permanent artifact repository URL, archival artifact DOI, and explicit
public-source license remain release blockers, but they are artifact
availability matters outside the scope of this citation audit. They are not
bibliographic defects and are not counted as open citation checklist items.

## Mechanical consistency check

The following results were obtained directly from the current TeX source:

| Check | Result |
|---|---:|
| Bibliography entries | 13 |
| Unique cited keys | 13 |
| Citation commands | 16 |
| Citation-key occurrences | 24 |
| Undefined citation keys | 0 |
| Uncited bibliography entries | 0 |
| Duplicate bibliography keys | 0 |
| LaTeX citation warnings | 0 |
| Bibliography width argument | 99 |

Bibliography keys, in manuscript order:

1. andronescu2004
2. bonnet2020
3. boury2024
4. boury2025
5. boury2025seeding
6. busch2006
7. garciamartin2013
8. hales2017
9. hofacker1994
10. lean4
11. nussinov1980
12. turner2010
13. zadeh2011

The set of unique citation keys is exactly the same set. The current auxiliary
file contains a resolved bibcite record for each of the 13 entries. The current
LaTeX log has unrelated shell-escape and microtype warnings only; it has no
undefined-citation or undefined-reference warning.

## Final claim-level audit

| Current manuscript claim | Current source mapping | Final verdict |
|---|---|---|
| ViennaRNA's RNAinverse as a canonical early thermodynamic inverse-folding heuristic; RNA-SSD stochastic local search; INFO-RNA dynamic-programming initialization plus local search; RNAiFold constraint programming; NUPACK ensemble-defect optimization | hofacker1994; andronescu2004; busch2006; garciamartin2013; zadeh2011 | **MATCH.** Each retained method is named explicitly and mapped to its primary method paper. The NUPACK clause is specifically about ensemble-defect optimization, so zadeh2011 is the precise source; a separate NUPACK system citation is unnecessary. |
| Learned sequence generators / LEARNA | No such clause or name remains in the manuscript | **RESOLVED BY DELETION.** No learned-generator assertion remains to support, and runge2019 is correctly absent from the final 13-item bibliography. |
| Bonnet et al. proved NP-completeness for a Watson–Crick design-extension formulation with prescribed nucleotide constraints | bonnet2020 | **MATCH.** The wording is now qualified and does not assert hardness for the unconstrained design problem studied in this manuscript. |
| The combinatorial Watson–Crick base-pair model studied by Haleš et al.; proper/separated coloring framework; separated coloring implies designability; local obstructions and related designable classes | hales2017 | **MATCH.** “Studied” avoids the earlier unsupported historical-priority wording. |
| Modulo-m separation and motif-free separability hardness; all-long positive theorem and linear-time construction | boury2024, with boury2025 where the journal expansion is also discussed | **MATCH.** The conference is correctly identified as the 24th WABI, and its role is not conflated with the later strengthening. |
| Hardness without isolated base pairs and the known minimum-helix-length-two construction using many isolated stacks | boury2025 | **MATCH WITH THE STATED QUALIFICATION.** The manuscript says “their known construction,” rather than generalizing to every counterexample. |
| A bounded number of isolated stacks motivates the present theorem | Context from boury2024 and boury2025 | **MATCH AS AUTHOR MOTIVATION.** The paper no longer attributes an explicit bounded-stack open question to those authors. |
| Biseparability and separated/biseparable exact seeds for thermodynamic inverse folding | boury2025seeding, with boury2025 in the broader seed discussion | **MATCH.** The RECOMB 2025 source is cited at first use and in the downstream-seeding discussion. |
| Exact Nussinov dynamic programming | nussinov1980 at the first substantive occurrence | **MATCH.** Later use in the second example is covered by the established named method. |
| Turner nearest-neighbor thermodynamics/energies | turner2010 at first substantive use | **MATCH.** The manuscript correctly treats performance under Turner energies as an empirical question and makes no thermodynamic-performance claim for the theorem. |
| The theorem is formalized in Lean 4 | lean4 for the prover/language; artifact records for manuscript-specific evidence | **MATCH WITH EVIDENCE SEPARATION.** The Lean paper identifies the system but is not used as evidence that this repository builds or was audited. |
| A documented search through 19 August 2026 did not locate an exact prior theorem or counterexample | The manuscript explicitly says the search is necessarily incomplete and is not proof of novelty | **ACCEPTABLE QUALIFIED SEARCH STATEMENT.** This is not presented as a theorem established by the bibliography and creates no additional citation action. |

## Final bibliography inventory

| Key | Primary work and identifier | Supported use in the manuscript |
|---|---|---|
| andronescu2004 | Andronescu et al., “A New Algorithm for RNA Secondary Structure Design,” Journal of Molecular Biology 336(3):607–624 (2004), [doi:10.1016/j.jmb.2003.12.041](https://doi.org/10.1016/j.jmb.2003.12.041) | RNA-SSD and stochastic/local-search inverse folding |
| bonnet2020 | Bonnet, Rzążewski, and Sikora, “Designing RNA Secondary Structures Is Hard,” Journal of Computational Biology 27(3):302–316 (2020), [doi:10.1089/cmb.2019.0420](https://doi.org/10.1089/cmb.2019.0420) | Qualified RNA Design Extension hardness |
| boury2024 | Boury, Bulteau, and Ponty, WABI 2024, LIPIcs 312, article 19, [doi:10.4230/LIPIcs.WABI.2024.19](https://doi.org/10.4230/LIPIcs.WABI.2024.19) | Modulo-m separation, motif-free hardness, and all-long positive construction |
| boury2025 | Boury, Gardelle, Bulteau, and Ponty, Algorithms for Molecular Biology 20:20 (2025), [doi:10.1186/s13015-025-00278-6](https://doi.org/10.1186/s13015-025-00278-6) | Journal expansion, no-isolated-base-pair hardness, known length-two construction, and broader seed discussion |
| boury2025seeding | Boury et al., “Old Dog, New Tricks,” RECOMB 2025, LNCS 15647:134–152, [doi:10.1007/978-3-031-90252-9_9](https://doi.org/10.1007/978-3-031-90252-9_9) | Biseparability and exact-seeding performance |
| busch2006 | Busch and Backofen, “INFO-RNA—a Fast Approach to Inverse RNA Folding,” Bioinformatics 22(15):1823–1831 (2006), [doi:10.1093/bioinformatics/btl194](https://doi.org/10.1093/bioinformatics/btl194) | INFO-RNA initialization and local search |
| garciamartin2013 | García-Martín, Clote, and Dotú, “RNAiFOLD,” Journal of Bioinformatics and Computational Biology 11(2):1350001 (2013), [doi:10.1142/S0219720013500017](https://doi.org/10.1142/S0219720013500017) | Constraint-programming RNA design |
| hales2017 | Haleš et al., “Combinatorial RNA Design,” Algorithmica 79(3):835–856 (2017), [doi:10.1007/s00453-016-0196-x](https://doi.org/10.1007/s00453-016-0196-x) | Combinatorial model, coloring framework, sufficient design condition, and structural results |
| hofacker1994 | Hofacker et al., “Fast Folding and Comparison of RNA Secondary Structures,” Monatshefte für Chemie 125(2):167–188 (1994), [doi:10.1007/BF00818163](https://doi.org/10.1007/BF00818163) | ViennaRNA/RNAinverse canonical early heuristic |
| lean4 | de Moura and Ullrich, “The Lean 4 Theorem Prover and Programming Language,” CADE 28, LNCS 12699:625–635 (2021), [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37) | Lean 4 language and prover only |
| nussinov1980 | Nussinov and Jacobson, “Fast Algorithm for Predicting the Secondary Structure of Single-Stranded RNA,” PNAS 77(11):6309–6313 (1980), [doi:10.1073/pnas.77.11.6309](https://doi.org/10.1073/pnas.77.11.6309) | Named exact Nussinov dynamic program |
| turner2010 | Turner and Mathews, “NNDB,” Nucleic Acids Research 38(suppl. 1):D280–D282 (2010), [doi:10.1093/nar/gkp892](https://doi.org/10.1093/nar/gkp892) | Turner nearest-neighbor model context |
| zadeh2011 | Zadeh, Wolfe, and Pierce, “Nucleic Acid Sequence Design via Efficient Ensemble Defect Optimization,” Journal of Computational Chemistry 32(3):439–452 (2011), [doi:10.1002/jcc.21633](https://doi.org/10.1002/jcc.21633) | NUPACK ensemble-defect optimization |

## Resolved citation checklist

- [x] Correct the WABI ordinal to “24th” and use the official proceedings metadata.
- [x] Narrow the Bonnet sentence to design extension with prescribed constraints.
- [x] Replace the ambiguous practical-methods citation group with explicit
  tool-to-source mappings.
- [x] Add RNAinverse/Hofacker 1994 and RNAiFold; retain RNA-SSD, INFO-RNA, and
  ensemble-defect NUPACK citations.
- [x] Resolve the learned-generator clause by removing it. LEARNA and
  runge2019 are not needed because no learned-generator claim remains.
- [x] Cite the RECOMB 2025 biseparability/seeding paper.
- [x] Attribute the no-isolated-base-pair hardness strengthening specifically
  to the 2025 journal paper.
- [x] Recast bounded-isolated-stack “left open” wording as the present authors'
  motivation.
- [x] Add Nussinov and Turner primary citations for the retained eponyms.
- [x] Use the Lean 4 paper only for the language/prover and separate it from
  artifact-specific verification evidence.
- [x] Use bibliography width 99 and consistent 2025a/2025b labels.
- [x] Confirm that all 13 bibliography entries are cited and all citation keys
  resolve.

## Out-of-scope release blockers

The citation audit is closed. The following remain real publication-release
blockers, but they concern artifact availability rather than citations:

- permanent public repository URL;
- archival artifact DOI;
- explicit public-source license.

No other citation-scope blocker remains open.
