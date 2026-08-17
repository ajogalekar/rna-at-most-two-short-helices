# Final release manifest

This manifest records the reproducibility metadata for the completed
Milestone 5 source release.  The implementation, documentation content, clean
archive-source commit, kernel audit, and external review artifact are fixed.

## Canonical specification

- Canonical manuscript: `docs/CANONICAL_PROOF.md`
- SHA-256:
  `28a443348eb96574d7943243cbe26f69005bb5565350589bf5bb7c230aa26735`
- The manuscript remained frozen during Milestone 5.

## Repository history

| Milestone | Recorded base | Implementation | Documentation / handoff |
|---|---|---|---|
| 1 | none (the implementation is the repository root commit) | `d857457487b7ee74b0d49dd60388d549b618e861` | same commit |
| 2 | `d857457487b7ee74b0d49dd60388d549b618e861` | `9c6f752c2fcf174fe91af35eab21cddc62cc69da` | `bf6a7cefbe34c1d7dc44b21dd8bb031b9c66e68b` |
| 3 | `bf6a7cefbe34c1d7dc44b21dd8bb031b9c66e68b` | `1db9e27d4bce6cf1f3a62ff0004083f041e83615` | `04766212239932dc7fba49f5e24d396f0e375789` |
| 4 | `04766212239932dc7fba49f5e24d396f0e375789` | `58d15f9e9e445d5fc00d371dd9f7fe1c3d8f898a` | `4e575299721282869d0a7a987e7433eb642c0719` |
| 5 | `4e575299721282869d0a7a987e7433eb642c0719` | `7848ae1988e4c923645fe76b7b522974ea5dbf36` | `c711723d386a886f551be3e6f793e5196c4e1a77` |

Milestone 5's mandatory pre-implementation proof-design commit is
`4194bba4e9a04173552ac7dc6483c99329db1e9c`
(`Document Milestone 5 proof architecture`).

- Working branch: `milestone-5-no-tie-final`
- Clean archive-source commit:
  `d22684984c5093511ea7a8e4e8fc465bc529b387`
  (`Record Milestone 5 release provenance`)
- Post-archive checksum record: this metadata-only commit.  A Git commit cannot
  contain its own SHA-1; its exact hash is therefore reported by
  `git rev-parse HEAD` in the final handoff rather than asserted inside itself.

## Toolchain and platform

- Elan: `4.2.3 (b6cec7e10 2026-06-08)`
- Lean toolchain selector: `leanprover/lean4:v4.34.0-rc1`
- Lean: `4.34.0-rc1`
- Lean commit: `3447a668783dbce1a8fdb97101dd067687b2b418`
- Lean target: `arm64-apple-darwin24.6.0`
- Lake: `5.0.0-src+3447a66`
- Mathlib requirement: `v4.34.0-rc1`
- Mathlib resolved revision:
  `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`
- Operating system: macOS `26.5.2`, build `25F84`
- Kernel / architecture reported by `uname`: Darwin `25.5.0`, `arm64`

Pinned-file hashes:

| File | SHA-256 |
|---|---|
| `lean-toolchain` | `cdbc6c372a2b37ad94430a6cec69cedfa4d36f255bfd968773fd91bf7a1746bf` |
| `lakefile.toml` | `4375055260da09d0942728731fbc7cf8ea128eb341137363d5902344b72a661d` |
| `lake-manifest.json` | `46d8242f5e4baa7fda3b9a0283f996cde8926d10c721513fc1e95f6a50653e25` |

## Exact public theorem

Final theorem name:

```lean
RNA.oneShortHelixDesignability
```

Source declaration:

```lean
theorem oneShortHelixDesignability :
    OneShortHelixDesignabilityStatement
```

Fully expanded proposition:

```lean
∀ {n : Nat} (T : SecondaryStructure n),
  InTargetClassK T →
  ∃ w : Sequence n,
    StructureCompatible w T ∧
    ∀ S : SecondaryStructure n,
      StructureCompatible w S →
      S ≠ T →
      pairCount S < pairCount T
```

All competitors in the final quantifier are arbitrary values of the existing
matching-based `SecondaryStructure n` type and use the same complete witness
sequence `w`.

## Kernel dependencies

- Exact transitive axiom set of `RNA.oneShortHelixDesignability`:
  `[propext, Classical.choice, Quot.sound]`
- Audit module: `RNA/FinalAxiomAudit.lean`
- Human-readable audit: `docs/FINAL_AXIOM_AUDIT.md`

This value was copied verbatim from the successful output of:

```text
lake build RNA.FinalAxiomAudit
```

## Validation commands

The final clean validation, run successfully at archive-source commit
`d22684984c5093511ea7a8e4e8fc465bc529b387`, was:

```bash
cd /Users/ashujo/Documents/Science/rna_one_short_helix_lean
lake clean
lake build
lake build RNA.FinalAxiomAudit
rg -n --glob '*.lean' 'sorry|admit|axiom|unsafe' RNA RNA.lean
git diff --check
git status --short
```

Each source-search occurrence must be classified in the final report; audit
commands such as `#print axioms` are text matches but are not axiom
declarations.

## Review archive

- Archive filename: `milestone_5_final_review_source.zip`
- Final location:
  `/Users/ashujo/Documents/Science/milestone_5_final_review_source.zip`
- Source archive SHA-256:
  `26c28269aa13028d8d64dd9073763dd7ce044b481c82bdbeca78bf9de957b8fb`
- External checksum sidecar:
  `/Users/ashujo/Documents/Science/milestone_5_final_review_source.zip.sha256`

The archive contains this manifest because it contains the complete `docs/`
directory.  Consequently, embedding the archive's own final SHA-256 value in
the in-archive copy creates a self-reference: changing that field changes the
archive bytes and therefore changes the digest.  The reproducible release
convention used here was therefore:

1. commit the clean archive-source repository with this manifest naming the
   archive and its exact provenance;
2. create the ZIP solely from that clean final commit, with the required
   inclusions and exclusions;
3. move the ZIP outside the repository;
4. compute its SHA-256 after the move; and
5. write the exact digest and archive basename to the external `.sha256`
   sidecar, without rebuilding the ZIP; and
6. update the repository copy of this manifest with that already-fixed digest,
   without claiming that the resulting metadata-only commit is itself the
   archived source snapshot.

Exact provenance wording for the completed release:

> `milestone_5_final_review_source.zip` is the source snapshot of commit
> `d22684984c5093511ea7a8e4e8fc465bc529b387`, built with the inclusion and exclusion
> rules in Section 18 of the Milestone 5 specification.  Its exact SHA-256 is
> `26c28269aa13028d8d64dd9073763dd7ce044b481c82bdbeca78bf9de957b8fb`,
> also recorded in the adjacent
> `milestone_5_final_review_source.zip.sha256` sidecar.  The sidecar is external
> because the manifest itself is contained in the hashed archive.

Thus the repository copy of this manifest records the actual archive digest;
the archive necessarily contains the immediately preceding, pre-digest copy
of this one file.  The Lean source, all other documentation, and every pinned
project file in the archive are exactly those of the clean archive-source
commit above.
