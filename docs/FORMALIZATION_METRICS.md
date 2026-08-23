# Formalization metrics

Qualification date: 2026-08-22

This report supplies the exact source-size, declaration, environment, and
measured-build data used by the manuscript formalization section. All source
counts are reproducible with:

    python3 scripts/measure_formalization.py

Machine-readable output is available with:

    python3 scripts/measure_formalization.py --json

## Qualified source identity

| Field | Value |
|---|---|
| Repository | /Users/ashujo/Documents/Science/rna_at_most_two_short_helices_lean |
| Branch | final-publication-release |
| Audited baseline commit | 28070dd0032f417b1eed03a1fa23f81a260eaff7 |
| Theorem closure manifest | docs/final_dependency_closure.txt |
| Closure manifest SHA-256 | 4dda2cb3d78cec0bb6c5dd34237abe05ec0a35903a9e4beb24979ff4d3256d34 |
| Metrics script SHA-256 | 77d7b0ebeb655ea5830b3a324ef0519117879e69b30110febbae6af54622c1e1 |
| Closure scope | 46 unique handwritten Lean files |
| Full project scope | 62 unique handwritten Lean files |

The full project scope is the union of the repository's tracked Lean sources
and the two downstream publication modules. Set union makes the result stable
whether those two modules are still untracked or have been added to Git. The
script fails unless the release has exactly 46 closure files and 62 project
files, unless the expected counts are explicitly overridden.

Generated files, build products, and dependency sources are not counted.
In particular, nothing under .lake, build, generated, lake-packages, or
Mathlib is admitted to either handwritten-source scope.

## Reproducible source-line counts

| Scope | Files | Raw physical lines | Raw nonblank lines | Nonblank/noncomment lines |
|---|---:|---:|---:|---:|
| Final theorem dependency closure | 46 | 20,738 | 18,607 | 16,908 |
| Full handwritten project | 62 | 25,015 | 22,136 | 20,175 |

“Raw physical” is the UTF-8 Python splitlines count. “Raw nonblank” counts
physical lines containing any non-whitespace before comments are removed.
“Nonblank/noncomment” removes Lean line comments and nested block comments
with a lexical state machine, retains quoted strings and escapes, and then
counts physical lines with residual non-whitespace.

## Reproducible declaration counts

The requested declaration groups are source-command counts, not environment
constant counts:

- definitions = def + abbrev;
- structures and inductives = structure + inductive;
- lemmas and theorems = lemma + theorem;
- examples = example.

| Scope | Definitions | Structures + inductives | Lemmas + theorems | Examples |
|---|---:|---:|---:|---:|
| Final theorem dependency closure | 426 | 27 | 1,102 | 0 |
| Full handwritten project | 641 | 27 | 1,392 | 48 |

For completeness, the exact keyword breakdown and the otherwise ungrouped
instance commands are:

| Scope | def | abbrev | structure | inductive | lemma | theorem | example | instance |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Final theorem dependency closure | 390 | 36 | 20 | 7 | 0 | 1,102 | 0 | 61 |
| Full handwritten project | 599 | 42 | 20 | 7 | 0 | 1,392 | 48 | 61 |

There are no class, opaque, or axiom source commands in either scope.
Including the 61 instance commands, the all-counted source-command totals are
1,616 for the closure and 2,169 for the full project.

A command is recognized only when its first comment-stripped token, after
same-line attributes and declaration modifiers, is a counted declaration
keyword. Thus generated auxiliaries do not inflate the count, and one source
command counts once even if the elaborator creates multiple constants.

## Qualification environment

| Field | Exact value |
|---|---|
| Installed RAM | 34,359,738,368 bytes (32 GiB) |
| Architecture | arm64 |
| Logical CPUs | 10 |
| Operating system | macOS 26.5.2 (build 25F84), Darwin 25.5.0 |
| Lean | 4.34.0-rc1, arm64-apple-darwin24.6.0, compiler commit 3447a668783dbce1a8fdb97101dd067687b2b418, Release |
| Lake | 5.0.0-src+3447a66 |
| Mathlib revision | de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11 |
| Build parallelism | No -j option; Lake's default scheduler on the 10-logical-CPU host |

Pinned build-input hashes:

| Input | SHA-256 |
|---|---|
| lean-toolchain | cdbc6c372a2b37ad94430a6cec69cedfa4d36f255bfd968773fd91bf7a1746bf |
| lakefile.toml | 4375055260da09d0942728731fbc7cf8ea128eb341137363d5902344b72a661d |
| lake-manifest.json | 46d8242f5e4baa7fda3b9a0283f996cde8926d10c721513fc1e95f6a50653e25 |

## Existing measured clean target qualification

The target qualification used macOS /usr/bin/time -p. The exact command
sequence began with lake clean and then built the public theorem target from
the cleaned tree.

| Exact command | Character | Lake graph jobs | Real (s) | User (s) | Sys (s) | Exit | Result |
|---|---|---:|---:|---:|---:|---:|---|
| lake clean | Clean preparation | — | 9.05 | 0.20 | 3.12 | 0 | PASS |
| lake build RNA.AtMostTwoShort.Designability | Clean target build | 3,061 | 823.27 | 5,235.51 | 1,286.53 | 0 | PASS |

The raw target-build record is docs/PUBLICATION_RELEASE_BUILD.log
(SHA-256
29011d981cc00f4f3d2d5528bbe5dbcceaca6842c2127dce45b901017e03f4cc).
Lake's reported graph-job count is not the number of simultaneous workers.
The log includes non-fatal linter and deprecation warnings from existing
sources and no build error.

## Bare full-project build and final-audit qualification

The exact final command sequence was run serially from a clean tree.  The bare
`lake build` is the clean full-project measurement; each named command after it
uses the newly populated cache and confirms the theorem audit and downstream
publication modules explicitly.

| Exact command | Cache state / purpose | Lake graph jobs | Real (s) | User (s) | Sys (s) | Exit | Result | Raw log |
|---|---|---:|---:|---:|---:|---:|---|---|
| `lake clean` | Clean preparation | — | 3.18 | 0.21 | 1.98 | 0 | PASS | docs/FINAL_FORMAL_BUILD.log |
| `lake build` | Clean bare full-project build | 3,070 | 894.10 | 5,405.09 | 1,355.88 | 0 | PASS | docs/FINAL_FORMAL_BUILD.log |
| `lake build RNA.AtMostTwoShort.AxiomAudit` | Post-clean final-theorem axiom audit | 3,056 | 2.98 | 1.53 | 2.82 | 0 | PASS | docs/FINAL_FORMAL_BUILD.log |
| `lake build RNA.AtMostTwoShort.PublicationExamples` | Post-clean downstream examples | 3,056 | 6.59 | 8.17 | 2.17 | 0 | PASS | docs/FINAL_FORMAL_BUILD.log |
| `lake build RNA.AtMostTwoShort.PublicationExamplesAxiomAudit` | Post-clean 18-endpoint axiom audit | 3,057 | 2.71 | 1.48 | 2.20 | 0 | PASS | docs/FINAL_FORMAL_BUILD.log |

The run began at `2026-08-22T21:40:31-0700` and ended at
`2026-08-22T21:55:40-0700`.  Its raw log has 3,423 lines, 220,349 bytes, and
SHA-256
`9b19f6aa6ccf775649da572109289e7447775a94fa967885fe8efc96da203096`.
The build emitted only pre-existing linter and deprecation warnings; it
reported no error.

## Post-build statement, axiom, and source-policy evidence

| Exact command | Output | SHA-256 | Result |
|---|---|---|---|
| `lake env lean /tmp/FinalTheoremReleaseAudit.lean` | docs/FINAL_THEOREM_PRINT.txt | `bf76a8b776b39a27c2b771ae5330947e129c3bd8cc386aa201e72a63b8f6b7b7` | PASS |
| `lake env lean RNA/AtMostTwoShort/AxiomAudit.lean` and `lake env lean RNA/AtMostTwoShort/PublicationExamplesAxiomAudit.lean` | docs/FINAL_AXIOM_OUTPUTS.txt | `e65d124fd82348fc3dd4080e9e37209c35c12da3363098cb0d43d2466ec1a59d` | PASS |
| `python3 scripts/audit_handwritten_lean_tokens.py` | docs/FINAL_HANDWRITTEN_TOKEN_AUDIT.txt | `edfc7def1613a4aa42e897bbe789951e87a07160111a6d17d73eb7ca39f883bf` | PASS |
| `python3 scripts/audit_source_integrity.py` | docs/FINAL_SOURCE_INTEGRITY_AUDIT.txt | `05581a1453d1b2df9a4786c4e5e51ed859e2aed566244decc0191007e2a225a4` | PASS |

The theorem print gives the exact public proposition and theorem and reports
only `[propext, Classical.choice, Quot.sound]`.  The combined axiom output
reports the same set for the final theorem and all 18 publication endpoints.
The token-aware audit covers all 62 handwritten Lean files and finds zero
actual-code tokens named `sorry`, `admit`, `axiom`, `unsafe`, `sorryAx`, or
`native_decide`.  The source-integrity audit independently compares all 60
pre-existing Lean files with baseline commit
`28070dd0032f417b1eed03a1fa23f81a260eaff7`, rechecks all 46 closure digests,
and finds no reverse import from a pre-existing source into either downstream
publication module.

## Closure identity cross-check

The distributed closure manifest is byte-identical to the authoritative
isolated-run manifest. The 46 closure paths were also compared directly with
the authoritative isolated-run pre-build hash inventory
source_hashes_before.sha256.

All 46 paths occur exactly once in that inventory and all 46 current SHA-256
digests match. There are zero missing paths, zero duplicate baseline entries,
and zero digest mismatches. The detailed verification and full current digest
map are in docs/THEOREM_CLOSURE_IDENTITY_REPORT.md.
