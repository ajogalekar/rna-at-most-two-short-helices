# Version 1.0.3 novelty, attribution, and pre-arXiv calibration

Release date: 2026-08-25
Branch: `final-publication-release`
Tag: `v1.0.3`
DOI: <https://doi.org/10.5281/zenodo.22101755>
Concept DOI: <https://doi.org/10.5281/zenodo.22075873>
Canonical repository: <https://github.com/ajogalekar/rna-at-most-two-short-helices>
Creator: Ashutosh S. Jogalekar
Affiliation: Szilard Scientific, LLC

This editorial patch synchronizes the final pre-arXiv manuscript bytes across
the public GitHub repository, GitHub Release, and immutable Zenodo record.
Version `1.0.2` remains unchanged under DOI
<https://doi.org/10.5281/zenodo.22100052>, version `1.0.1` remains unchanged under DOI
<https://doi.org/10.5281/zenodo.22089626>, and version `1.0.0` remains
unchanged under DOI <https://doi.org/10.5281/zenodo.22075874>.

Review status: at the time of this release, the manuscript and formal proof
have not yet received a completed independent review by a human subject-matter expert. The dedicated
manuscript section gives the complete AI-use disclosure and division of
responsibility. The formal proof was verified in Lean, and the author remains
responsible for every claim.

## Changes from 1.0.2

- credits Haleš et al. explicitly for the original opposite-parity device and
  Boury et al. for the published local helix-word table and general modulo-m
  framework;
- identifies the new proof step narrowly as the bounded-two global
  resource-counting induction, without presenting prior local transfer words
  as new;
- states that the at-most-two bound is a sufficient construction limit, not a
  structural boundary or a new decision algorithm, and distinguishes the
  theorem from Boury et al.'s fixed-m dynamic program;
- credits the geometric antecedent of the three-isolated-stack example and
  notes that the saturated worked example is already covered by Haleš et al.'s
  saturated-target theorem;
- adds verified related-work citations to Jedwab--Petrie--Simon and
  Yao--Chauve--Régnier--Ponty, while omitting unsupported or unarchived
  computational prevalence claims;
- preserves the comprehensive dedicated AI-use and human-responsibility
  disclosure, adds a concise disclosure at the end of both manuscript and
  arXiv-metadata abstracts, and carries a short version in arXiv Comments; and
- regenerates the dot-bracket audit, bibliography audit, PDF, and every
  manuscript-dependent release byte.

No theorem-closure Lean file changed. The 46-file theorem dependency closure,
canonical source archive, release-qualification results, and two fidelity
bundles remain byte-identical to versions `1.0.2`, `1.0.1`, and `1.0.0`.

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
