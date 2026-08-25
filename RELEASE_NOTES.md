# Version 1.0.2 AI-use disclosure and metadata-scope revision

Release date: 2026-08-25
Branch: `final-publication-release`
Tag: `v1.0.2`
DOI: <https://doi.org/10.5281/zenodo.22100052>
Concept DOI: <https://doi.org/10.5281/zenodo.22075873>
Canonical repository: <https://github.com/ajogalekar/rna-at-most-two-short-helices>
Creator: Ashutosh S. Jogalekar
Affiliation: Szilard Scientific, LLC

This editorial patch synchronizes the final pre-arXiv manuscript bytes across
the public GitHub repository, GitHub Release, and immutable Zenodo record.
Version `1.0.1` remains unchanged under DOI
<https://doi.org/10.5281/zenodo.22089626>, and version `1.0.0` remains
unchanged under DOI <https://doi.org/10.5281/zenodo.22075874>.

Review status: at the time of this release, the manuscript and formal proof
have not yet received a completed independent review by a human subject-matter expert. The dedicated
manuscript section gives the complete AI-use disclosure and division of
responsibility. The formal proof was verified in Lean, and the author remains
responsible for every claim.

## Changes from 1.0.1

- expanded the existing dedicated AI-use section to disclose generative AI's
  foundational and pervasive role across all major research, formalization,
  auditing, figure, release-preparation, and manuscript-writing stages;
- removed the shorter AI-use sentence from both the manuscript and arXiv
  metadata abstracts;
- preserved the explicit human decision-making and full author-responsibility
  statement;
- corrected the Zenodo and citation descriptions so they state every formal
  target-class restriction rather than overgeneralizing the theorem, and
  tightened the corresponding shorthand in the manuscript's discussion; and
- regenerated the line-number-sensitive dot-bracket audit and all
  manuscript-dependent release bytes.

No theorem-closure Lean file changed. The 46-file theorem dependency closure,
canonical source archive, release-qualification results, and two fidelity
bundles remain byte-identical to versions `1.0.1` and `1.0.0`.

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
