# RNA targets with one short helix — Lean foundation

This repository contains Milestones 1 and 2 of a Lean 4 formalization of the exact
four-letter Watson–Crick model and theorem statement in
[`docs/CANONICAL_PROOF.md`](docs/CANONICAL_PROOF.md). The final designability
theorem is represented as a `Prop`; its proof is intentionally deferred.

Milestone 2 adds maximal-helix partition/canonical lookup, black-white-grey
color algebra, exact integer levels and strong two-separation, L/M/E endpoint
theory, actual-child root and loop allocations, universal long-helix transfer,
the complete length-two table, `Safe`, and a bridge from local transfer words
to global target levels.  It deliberately stops before the global recursive
coloring theorem and nucleotide construction.

## Pinned toolchain

- Lean: `4.34.0-rc1`, commit
  `3447a668783dbce1a8fdb97101dd067687b2b418`
- Mathlib requirement: `v4.34.0-rc1`
- Mathlib resolved revision:
  `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`
- Elan: `4.2.3 (b6cec7e10 2026-06-08)`
- Lake: `5.0.0-src+3447a66`
- Host: macOS `26.5.2` (`25F84`), Apple Silicon `arm64`

The Lean channel is pinned in `lean-toolchain`; the Mathlib release is pinned in
`lakefile.toml`; every resolved dependency commit is pinned in
`lake-manifest.json`. These files must be committed together.

## Exact creation and build commands

The project was created from `/Users/ashujo/Documents/Science` with Mathlib's
official toolchain selector rather than a separately chosen Lean release:

```bash
/Users/ashujo/.elan/bin/lake +leanprover-community/mathlib4:lean-toolchain \
  new rna_one_short_helix_lean math
```

Because the destination was inside an existing outer Git worktree, Lake did not
create a nested repository. The requested project-local repository was then
initialized explicitly:

```bash
git -C /Users/ashujo/Documents/Science/rna_one_short_helix_lean init -b main
```

Fetch the matching Mathlib cache and build from a clean checkout with:

```bash
cd /Users/ashujo/Documents/Science/rna_one_short_helix_lean
source /Users/ashujo/.elan/env
lake exe cache get
lake build
```

Useful provenance checks:

```bash
source /Users/ashujo/.elan/env
elan --version
elan show
lake env lean --version
lake --version
jq -r '.packages[] | select(.name == "mathlib") | .rev' lake-manifest.json
shasum -a 256 docs/CANONICAL_PROOF.md
sw_vers
uname -m
```

The preserved manuscript SHA-256 is
`28a443348eb96574d7943243cbe26f69005bb5565350589bf5bb7c230aa26735`.

Official setup references:

- [Lean installation](https://lean-lang.org/install/manual/)
- [Using Mathlib as a dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
- [Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
