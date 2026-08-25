# Version 1.0.1 synchronized manuscript revision

Release date: 2026-08-24
Branch: `final-publication-release`
Tag: `v1.0.1`
DOI: <https://doi.org/10.5281/zenodo.22089626>
Concept DOI: <https://doi.org/10.5281/zenodo.22075873>
Canonical repository: <https://github.com/ajogalekar/rna-at-most-two-short-helices>
Creator: Ashutosh S. Jogalekar
Affiliation: Szilard Scientific, LLC

This patch release synchronizes the final pre-arXiv manuscript bytes across
the public GitHub repository, GitHub Release, and immutable Zenodo record.
Version `1.0.0` remains unchanged under DOI
<https://doi.org/10.5281/zenodo.22075874>.

Review status: at the time of this release, the manuscript has not yet
received a completed independent review by a human expert. The proof was
developed with substantial generative-AI assistance and was formally verified
in Lean. The author remains responsible for every claim.

## Changes from 1.0.0

- removed the short human-review-status sentence from the abstract while
  retaining the full review-status and author-responsibility statement in the
  AI-assisted-development and formal-verification section;
- generated the displayed `w1` and `w2` nucleotide literals from their actual
  Lean definitions, with validator checks tying each macro to its intended
  manuscript assignment;
- expanded Appendix B with source-derived interval-tree, paired-degree,
  unpaired-child, stack-offset, and stacked definitions needed to audit the
  `m5`, `m3dot`, and maximal-helix encodings;
- generated and checked a 42-declaration Lean listing audit from seven
  hash-pinned source files; and
- strengthened CI and release checks for generated literals, manuscript file
  hashes, source-derived listings, examples, and dot-bracket literals.

No theorem-closure Lean file changed. The 46-file theorem dependency closure,
canonical source archive, release-qualification results, and two fidelity
bundles remain byte-identical to version `1.0.0`.

## Release assets

The GitHub and Zenodo releases carry the same eight assets:

1. the DOI-bearing manuscript PDF;
2. the complete tagged repository ZIP;
3. `ZENODO_SHA256SUMS.txt` covering the other seven assets;
4. the unchanged canonical source archive;
5. its unchanged checksum sidecar;
6. the unchanged release-qualification results package;
7. the unchanged blinded fidelity bundle; and
8. the unchanged Claude fidelity-audit package.

The arXiv source upload is a separate distribution step and is not part of
these eight immutable release assets.
