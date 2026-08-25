# Prepared arXiv metadata (do not submit without author approval)

## Categories

- Primary: `q-bio.QM` (Quantitative Methods)
- Cross-list: `q-bio.BM` (Biomolecules)
- No CS cross-list is requested, avoiding a separate CS endorsement domain.

## Title and author

**Title:** Designability of RNA Targets with Up to Two Length-2 Helices

**Author:** Ashutosh S. Jogalekar

## Abstract for the arXiv metadata field

RNA inverse folding asks for an RNA sequence whose prescribed secondary structure is the unique maximum-base-pair compatible fold. In the four-letter Watson-Crick model (A-U and C-G pairs only, no pseudoknots, and zero minimum base-pair span), Hales et al. introduced a separated-coloring certificate and an even-odd device, while Boury et al. generalized this to modulo-$m$ separability, gave an $O(n 2^m)$ decision algorithm, and guaranteed designability when every helix has length at least 3. We prove that the guarantee still holds when a motif-free target has at most two maximal helices of length 2, no maximal helix of length 1, and all remaining helices of length at least 3. The proof builds on Boury et al.'s local helix-coloring transfers and adds a global counting argument showing that the demands created by at most two short helices can always be coordinated. This is a structural success guarantee for the existing modulo-2 algorithm, not a new general decision capability. The resulting coloring yields an explicit sequence whose every distinct compatible noncrossing fold has fewer pairs. No claim is made for nearest-neighbor thermodynamic energy models. The theorem and supporting lemmas are formalized in Lean 4 against pinned Mathlib and reproduced from a frozen public artifact; the kernel-reported axiom set is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The work was developed with foundational generative-AI assistance under the author's direction and has not yet received independent human expert review.

This version stays below arXiv's 1,920-character abstract limit after normalizing whitespace.

## Comments field

Final verified counts:

```text
39 pages, 7 figures. Formally verified in Lean 4; developed with foundational AI assistance; not yet independently reviewed. Artifact: https://doi.org/10.5281/zenodo.22101755. Source: https://github.com/ajogalekar/rna-at-most-two-short-helices
```

The Zenodo software DOI belongs in Comments, not arXiv's article DOI field.

## Endorsement status

The arXiv account is endorsed for the `q-bio` domain. Use `q-bio.QM` as the primary category and `q-bio.BM` as the cross-list; both remain within that endorsed domain.

No arXiv submission, endorsement request, or other arXiv account action is authorized by this file.
