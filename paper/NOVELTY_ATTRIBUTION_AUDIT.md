# Novelty and attribution audit

Audit date: 2026-08-25

Result: **central attribution corrections accepted; unsupported quantitative
claims excluded**

This audit was triggered by an adversarial AI review immediately before arXiv
submission. The review was treated as a set of leads, not as evidence. Each
accepted correction below was checked against a primary publication.

| Lead | Primary-source result | Manuscript decision |
|---|---|---|
| Boury et al. already display the long-helix words used in Lemma 6.3. | Confirmed. WABI 2024 Figure 8 and the 2025 journal Figure 12 display, up to black-white symmetry, `a^h`, `aGa^(h-2)`, `aaGa^(h-3)`, `Ga^(h-1)`, and `GGa^(h-2)`. Lemma 6.3 selects all but the `aaGa^(h-3)` family; in particular, `GBB` is the `h=3` instance of a published column. | Lemma and subsection renamed as a non-gray-ending selection from Boury's table. The text now says explicitly that no new local word family is introduced. Novelty is limited to the global bounded-resource induction that forces the relevant option to be available. |
| The parity device predates Boury's modulo-m framework. | Confirmed. Haleš et al., Theorem 10 (Result R8), explicitly force gray-pair and unpaired-node levels onto opposite parity classes while repairing an enlarged target. | Section 1.2 credits Haleš with the even-odd device. Section 1.3 credits Boury et al. with the general modulo-m formulation, target-preserving dynamic program, and all-long theorem. |
| Proposition 3.5 has a three-branch antecedent. | Confirmed. Haleš et al., Figure 6, compare `(..)(..)(..)` with the inflated designable target `((..))((..))((..))`; Figure 7 continues the same repair discussion. The paper's `((.))((.))((.))` is a distinct one-unpaired-per-hairpin variant. | Proposition 3.5 now cites the earlier figures and states that the geometry is adapted. Haleš et al. did not state modulo-2 nonseparability; the manuscript notes that its parity impossibility proof also applies to their two-stutter. |
| Saturated targets are prior coverage. | Confirmed. Haleš et al., Result R4/Theorem 4, characterize four-letter designability of saturated targets by the maximum paired-degree bound. | The theorem discussion now distinguishes the new modulo-2 certificate from the already known designability conclusion for saturated members. Worked example T1 has an explicit footnote. |
| The theorem does not create a new modulo-2 decision algorithm. | Confirmed. Boury et al. decide modulo-m separability in `O(n 2^m)` time, hence in linear time for fixed `m=2`. | The algorithmic discussion now states that the theorem supplies a structural success guarantee and direct witness construction, not a new decision capability or asymptotic improvement. |
| Boury's phrase “the question remains for h_min=2” can be quoted as the open question answered here. | Rejected as misleading. The phrase asks whether the all-long threshold is tight and is immediately followed by Boury et al.'s own nonseparable `h_min=2` construction. It is not an unresolved bounded-two question. | The phrase is not used. The manuscript instead quotes the conclusion's correctly scoped observation that the modulo-2 method extends beyond the all-long class “in a way that remains to be fully characterized.” |

## Additional literature decisions

- Added Jonathan Jedwab, Tara Petrie, and Samuel Simon, “An infinite class of
  unsaturated rooted trees corresponding to designable RNA secondary
  structures,” *Theoretical Computer Science* 833 (2020), 147–163,
  doi:10.1016/j.tcs.2020.05.046.
- Added Hua-Ting Yao, Cédric Chauve, Mireille Régnier, and Yann Ponty,
  “Undesignable motifs in structural RNAs and combinatorial consequences,”
  *Journal of Mathematical Biology* 92:49 (2026),
  doi:10.1007/s00285-026-02358-6.
- A paper titled “RNA Inverse Folding Under Stacked Base Pairs Maximization”
  by Théo Boury, Laurent Bulteau, and Yann Ponty appears on the official WABI
  2026 accepted-paper list. No public paper, proceedings record, DOI, or page
  range was available during this audit. Because its objective is also
  distinct from base-pair-count maximization, no substantive claim or formal
  citation was added before the paper itself could be inspected.

## Computational claims excluded

Three AI-generated exploratory scripts were recovered from a private Claude
session transcript and their headline totals were reproduced. They are not in
the public repository or Zenodo artifact, one older script contains a stale
control, the random generator is deliberately biased, and the reported
three-helix and fifteen-helix percentages depend on that arbitrary sampling
distribution. The manuscript therefore includes none of those new counts.
They may be reported later only after the scripts, exact methods, outputs,
environment, and hashes are independently checked and archived.

## Primary sources

- Haleš et al., *Algorithmica* 79(3):835–856 (2017),
  doi:10.1007/s00453-016-0196-x.
- Boury, Bulteau, and Ponty, WABI 2024, LIPIcs 312, 19:1–19:23,
  doi:10.4230/LIPIcs.WABI.2024.19.
- Boury et al., *Algorithms for Molecular Biology* 20:20 (2025),
  doi:10.1186/s13015-025-00278-6.
