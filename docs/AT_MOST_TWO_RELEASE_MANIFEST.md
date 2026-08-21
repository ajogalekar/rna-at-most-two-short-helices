# At-most-two-short-helices release manifest

## Release identity

This downstream release proves `RNA.atMostTwoShortHelixDesignability` for the
exact public proposition `RNA.AtMostTwoShortHelixDesignabilityStatement`.
The proof directly uses the at-most-two resource induction and includes the
zero-, one-, two-short, and all-unpaired cases.

- Frozen upstream base:
  `c37eac40ef5a28bf5733fd576ce6d4c44091ee6a`
- Corrected specification commit:
  `020fa8cd54f64c3e7264fd9dcab7ac11e6b671bc`
- Implementation commit:
  `b64d9165191a89e692d518c4e8cdaa9beafb61f3`
- Documentation/release commit:
  `fcb3bc37db5dddd4bf51b85efaefa644160b19c7`
- Clean archive-source commit:
  `<ARCHIVE_SOURCE_COMMIT_TO_FILL_AFTER_COMMIT>`
- Final checksum-metadata commit:
  `<FINAL_CHECKSUM_COMMIT_REPORTED_EXTERNALLY>`
- Branch: `at-most-two-short-helices`

The implementation commit is intentionally separate from the documentation
and archive-provenance commits. This makes the exact checked Lean source easy
to identify independently of release bookkeeping.

## Pinned environment

- Lean: `4.34.0-rc1`, compiler commit
  `3447a668783dbce1a8fdb97101dd067687b2b418`
- Target: `arm64-apple-darwin24.6.0`
- Lake: `5.0.0-src+3447a66`
- Mathlib resolved revision:
  `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`
- Host used for release validation: macOS `26.5.2` (`25F84`), arm64

Pinned-file SHA-256 values:

```text
cdbc6c372a2b37ad94430a6cec69cedfa4d36f255bfd968773fd91bf7a1746bf  lean-toolchain
4375055260da09d0942728731fbc7cf8ea128eb341137363d5902344b72a661d  lakefile.toml
46d8242f5e4baa7fda3b9a0283f996cde8926d10c721513fc1e95f6a50653e25  lake-manifest.json
13eb6f79a64a2a80fe5526330799fe79f8a0b46a9e0ef7aad542c33b126b6e5a  RNA.lean
fb9bee1126791b9ca53b3903c061df27e3856dd20b9c7fc248b7acd4e5326841  docs/CANONICAL_AT_MOST_TWO_PROOF.md
a8a0f08ca2b9b412367b005e0fcfbb096ee1062ee07ec866ae9789ca21df14ef  docs/CANONICAL_AT_MOST_TWO_PROOF_SHA256.txt
```

The copied Track B documents are read-only. Their individual digests are
recorded and verified by `docs/track_b_reference/SHA256SUMS.txt`; they are
traceability references and are not proof oracles.

## Validation record

Required clean archive-source commands:

```bash
lake clean
lake build
lake build RNA.AtMostTwoShort.AxiomAudit
rg -n --glob '*.lean' '\bsorry\b|\badmit\b|^\s*axiom\b|\bunsafe\b|\bsorryAx\b|\bnative_decide\b' RNA RNA.lean
git diff --check
git status --short
```

Result: **PASS (2026-08-20).** From clean commit
`fcb3bc37db5dddd4bf51b85efaefa644160b19c7`, the full build completed all
3,070 jobs and the separate audit build completed all 3,056 jobs. The
token-aware prohibited-source scan returned no matches; `git diff --check`,
the clean-worktree check, and copied-reference checksum verification passed.
Only pre-existing warnings from unchanged inherited modules were printed;
the new modules emitted no warning or panic.

The final theorem's kernel-reported transitive dependency set is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There are no project axioms, admissions, `sorryAx`, mathematical uses of
`unsafe`, `native_decide`, external proof executables, or calls to the old
exact-one designability theorem in the new theorem's dependency path.

## Archive

- File: `at_most_two_short_helices_lean_source.zip`
- External location:
  `/Users/ashujo/Documents/Science/at_most_two_short_helices_lean_source.zip`
- SHA-256: `<ARCHIVE_SHA256_TO_FILL_AFTER_ARCHIVE_CREATION>`
- Adjacent sidecar:
  `at_most_two_short_helices_lean_source.zip.sha256`
- Archive source commit: `<ARCHIVE_SOURCE_COMMIT_TO_FILL_AFTER_COMMIT>`

The archive is created with `git archive` from the clean archive-source
commit. It contains `README.md`, `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`, `RNA.lean`, all handwritten `RNA/` sources, and all
`docs/` content, including the read-only Track B references and checksums. It
does not contain `.git`, `.lake`, compiled artifacts, dependencies, caches,
editor state, `.DS_Store`, Python outputs, or the archive itself.

An archive cannot contain its own digest without changing that digest. The
archived manifest therefore records the archive-source commit but retains a
pre-digest placeholder. The adjacent sidecar and the repository's later
checksum-only metadata commit record the exact archive SHA-256. No Lean source
or proof changes after the archive-source commit.
