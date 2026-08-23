# Final revision input provenance

Recorded: 2026-08-22 (America/Los_Angeles)

## Formal repository baseline

- Repository: /Users/ashujo/Documents/Science/rna_at_most_two_short_helices_lean
- Required publication branch: final-publication-release
- Audited baseline commit: 28070dd0032f417b1eed03a1fa23f81a260eaff7
- Final declaration:
  RNA.atMostTwoShortHelixDesignability :
  RNA.AtMostTwoShortHelixDesignabilityStatement
- Baseline build command:
  lake build RNA.AtMostTwoShort.Designability
- Baseline result: PASS, 3,053 jobs

The publication examples were added in new downstream modules only. The
byte-identity and import-closure checks are recorded in
THEOREM_CLOSURE_IDENTITY_REPORT.md.

## Frozen input packages

| Input | SHA-256 |
|---|---|
| Language-revised manuscript source package | 9770a9e2f37a2ee2bcedb303e0e2d1dbe126e67463abb6c1aa8426d2f4bef83b |
| Baseline manuscript TeX inside that package | 07b216622af3f02ac05e1157af148b5806975c67cd2eefd03e52407732eb8cb8 |
| Baseline manuscript PDF inside that package | 3dbc7082884bb105d71394049ba3f8531e36dad3a3d965885704581332895fc8 |
| Canonical source archive | b077b6118a6cbfadb6c6fce00af65ed34125ffa431f6ca8b7e2e9de3c268d40f |
| Blinded fidelity bundle | bfd2c8d90f5666ccb2dda6a3e9c2f81b84419ae84cc25beb3f880c80b5c66b8b |
| Release-qualification results package | 2da05881fb3808e7add46526f6f202f81e6f0b4f9b37acd622a8acd7b435615b |
| Claude fidelity-audit package | 0a77ea7e9f9dc0342a14330b93644dc943a0b2c0e89f302b092ca08de404092b |

All digests were recomputed from the local files rather than copied without
checking. The final Claude manuscript review is preserved verbatim in
FINAL_CLAUDE_REVIEW.md; byte comparison against its recovered source returned
no difference.

## Naming convention

The final manuscript and release records use these names consistently:

1. canonical source archive;
2. release-qualification results package;
3. blinded fidelity bundle;
4. Claude fidelity-audit package; and
5. manuscript source package.

No repository URL, archival DOI, public-source license, or submission status
was inferred. Those items remain explicit blockers.
