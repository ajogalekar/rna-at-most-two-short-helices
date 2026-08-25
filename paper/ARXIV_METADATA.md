# Prepared arXiv metadata (do not submit without author approval)

## Categories

- Primary: `q-bio.QM` (Quantitative Methods)
- Cross-list: `q-bio.BM` (Biomolecules)
- No CS cross-list is requested, avoiding a separate CS endorsement domain.

## Title and author

**Title:** Designability of RNA Targets with Up to Two Length-2 Helices

**Author:** Ashutosh S. Jogalekar

## Abstract for the arXiv metadata field

RNA inverse folding asks for an RNA sequence whose prescribed secondary structure is the unique maximum-base-pair compatible fold. In the four-letter Watson-Crick model (A-U and C-G pairs only, no pseudoknots, and zero minimum base-pair span), prior work guarantees designability for motif-free targets when every maximal helix has length at least 3. We prove that the guarantee still holds when the target has at most two maximal helices of length 2, no maximal helix of length 1, and avoids the obstruction motifs $m_5$ and $m_{3\bullet}$; all remaining maximal helices have length at least 3. Our constructive proof extends modulo-2 separated colorings. A length-2 helix can force a gray boundary condition at an adjacent loop. Since at most two such demands occur, each loop remains within its two-gray capacity; if both meet at one multiloop, a length-at-least-3 incoming helix is recolored to terminate non-gray. The resulting proper separated coloring yields an explicit sequence, and every distinct compatible noncrossing fold has fewer pairs. The construction runs in $O(n)$ time and space. The theorem and supporting lemmas are formalized in Lean 4 against pinned Mathlib and reproduced from a frozen public artifact; the kernel-reported axiom set is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The work was developed with substantial generative-AI assistance under human supervision. No claim is made for nearest-neighbor thermodynamic energy models.

This version stays below arXiv's 1,920-character abstract limit after normalizing whitespace.

## Comments field

Final verified counts:

```text
37 pages, 7 figures. Includes a Lean 4 formalization and
reproducibility artifact at https://doi.org/10.5281/zenodo.22089626;
source at https://github.com/ajogalekar/rna-at-most-two-short-helices.
```

The Zenodo software DOI belongs in Comments, not arXiv's article DOI field.

## Endorsement plan

Select `q-bio.QM` when an arXiv draft is started and let arXiv report the account's endorsement status. If personal endorsement is required, request one endorsement in the `q-bio` domain from an established arXiv author who knows the author and understands the work. Do not mass-email prospective endorsers. The `q-bio.BM` cross-list should remain within the same endorsement domain.

No arXiv submission, endorsement request, or other arXiv account action is authorized by this file.
