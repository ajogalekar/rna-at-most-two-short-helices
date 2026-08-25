# Lean listing extraction and semantic checks

## Result

**PASS.** The extraction run validated all seven frozen source files against
pinned SHA-256 digests, extracted 42 declaration blocks into three
manuscript-ready listing files, and wrote a declaration-level source map.
Lean then resolved all 42 displayed declarations from the audited public
import with exit status 0.

The run used repository commit
`28070dd0032f417b1eed03a1fa23f81a260eaff7` on branch
`final-publication-release`, Lean `4.34.0-rc1` (commit
`3447a668783dbce1a8fdb97101dd067687b2b418`) and Python `3.14.6`.

## Reproduction commands

From the repository's `paper/` directory:

```sh
LEAN_REPO=..
python3 scripts/extract_paper_lean_listings.py \
  --repo "$LEAN_REPO" \
  --output paper_listings
```

Observed summary:

```text
Validated 7 frozen source files.
Extracted 42 declaration blocks into 3 listings.
Wrote source map: <manuscript>/paper_listings/SOURCE_MAP.tsv
Wrote Lean audit: <manuscript>/paper_listings/PaperLeanListingAudit.lean
```

Still from the manuscript directory, resolve it once and run Lean from the
theorem repository so Lake supplies the pinned environment:

```sh
MANUSCRIPT_DIR="$PWD"
(cd "$LEAN_REPO" && \
  lake build RNA.AtMostTwoShort.Designability && \
  lake env lean "$MANUSCRIPT_DIR/paper_listings/PaperLeanListingAudit.lean")
```

The explicit build makes the check work in a newly extracted source tree as
well as in an already built development.

Observed result: exit status 0.  Lean printed the inferred type of every
`#check` declaration, ending with:

```text
RNA.AtMostTwoShortHelixDesignabilityStatement : Prop
RNA.atMostTwoShortHelixDesignability : RNA.AtMostTwoShortHelixDesignabilityStatement
```

## Extraction contract

`extract_paper_lean_listings.py` performs these checks before writing output:

1. Every one of the seven frozen source files must be present and UTF-8.
2. Its full-file SHA-256 digest must match the pinned audited digest.
3. Every mapped inclusive line range must exist.

Each row of `SOURCE_MAP.tsv` records the listing, block order, fully qualified
declaration, repository-relative source path, explicit Lean module, inclusive
source line range, full-source SHA-256, and exact extracted-block SHA-256.
Within a listing, the extractor inserts only one blank separator line between
mapped source blocks; the mapped Unicode declaration blocks themselves are
copied from source.

## Generated-file digests

```text
bb9671434ccf286a06ae538e21c23444e9020c319431f62228b3a99d64e87b4b  01_core_model.lean
02d0cf171f11f168aaa4ef59ae5eba89d8fd6457f4fc130c8f1267669c790702  02_helix_target_class.lean
7f8eb5f5c69c30370b180bb3d8af624276521877887d7db25fe2470d2fd3dcda  03_public_theorem.lean
cec1bb1e2423f8ae60fd77be993779890ca4106c25e9e2fadac84ff5566df456  SOURCE_MAP.tsv
551bfa864ce6301e1d6613847f2521f31ec3632a90597b9f0897d319462aa500  PaperLeanListingAudit.lean
```

The listings are excerpts, not standalone Lean modules: their namespace and
import context remains in the frozen source files.  The separate audit module
therefore imports `RNA.AtMostTwoShort.Designability` and checks every displayed
fully qualified declaration in the repository's actual module context.

The recorded qualification run used the local paths preserved in
`docs/INPUT_PROVENANCE.md`; those historical paths are provenance only and are
not required by the portable commands above.
