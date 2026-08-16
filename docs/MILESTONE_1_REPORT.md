# Milestone 1 report

## 1. Files created

Project and build files:

- `.gitignore`
- `.github/workflows/create-release.yml`
- `.github/workflows/lean_action_ci.yml`
- `.github/workflows/update.yml`
- `lakefile.toml`
- `lake-manifest.json`
- `lean-toolchain`
- `README.md`
- `RNA.lean`

Lean library:

- `RNA/Alphabet.lean`
- `RNA/Structure.lean`
- `RNA/IntervalTree.lean`
- `RNA/Motifs.lean`
- `RNA/Helix.lean`
- `RNA/TargetClass.lean`
- `RNA/Statement.lean`
- `RNA/Examples.lean`
- `RNA/AxiomAudit.lean`

Traceability and audit documents:

- `docs/CANONICAL_PROOF.md`
- `docs/CANONICAL_PROOF_SHA256.txt`
- `docs/DESIGN_DECISIONS.md`
- `docs/FORMALIZATION_BLUEPRINT.md`
- `docs/MODEL_FIDELITY_AUDIT.md`
- `docs/AXIOM_AUDIT.md`
- `docs/MILESTONE_1_REPORT.md`

The generated placeholder `RnaOneShortHelixLean.lean` and
`RnaOneShortHelixLean/Basic.lean` were removed after the library was renamed to
the requested `RNA` module tree.

## 2. Toolchain versions and hashes

- Elan: `4.2.3 (b6cec7e10 2026-06-08)`
- Lean: `4.34.0-rc1`, commit
  `3447a668783dbce1a8fdb97101dd067687b2b418`
- Lake: `5.0.0-src+3447a66`
- Mathlib release requirement: `v4.34.0-rc1`
- Mathlib resolved revision:
  `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`
- Host: macOS `26.5.2` build `25F84`, `arm64`

SHA-256 values at report generation:

| File | SHA-256 |
|---|---|
| `lean-toolchain` | `cdbc6c372a2b37ad94430a6cec69cedfa4d36f255bfd968773fd91bf7a1746bf` |
| `lakefile.toml` | `4375055260da09d0942728731fbc7cf8ea128eb341137363d5902344b72a661d` |
| `lake-manifest.json` | `46d8242f5e4baa7fda3b9a0283f996cde8926d10c721513fc1e95f6a50653e25` |
| `docs/CANONICAL_PROOF.md` | `28a443348eb96574d7943243cbe26f69005bb5565350589bf5bb7c230aa26735` |

## 3. Architecture decision

The public theorem interface is the manuscript's direct representation: a
finite set of normalized arcs carrying partial-matching and noncrossing proofs.
This represents every noncrossing partial matching on `Fin n`; it does not come
from a narrower inductive grammar.

The interval tree is derived from that public matching. Paired nodes are target
arcs, unpaired nodes are target-unpaired positions, and `none` is a virtual root.
The executable parent selects the enclosing target pair with greatest left
endpoint. Laminarity proves that this is the unique smallest enclosing interval.
Ordered children, paired degree, and motifs are then derived from that parent.

Maximal helices use a canonical finite descriptor: an outer arc and a bounded
positive natural length. Exact stack-offset equations require every run member;
maximality forbids both an outward predecessor and the next inward member.
Lean proves that the member count equals the declared length and that two
maximal helices are equal or pair-disjoint.

See `docs/DESIGN_DECISIONS.md` for the comparison with dot-bracket words and
tree-first representations.

## 4. Exact `UniqueDesigns` definition

```lean
def UniqueDesigns (w : Sequence n) (T : SecondaryStructure n) : Prop :=
  StructureCompatible w T ∧
    ∀ S : SecondaryStructure n,
      StructureCompatible w S →
      S ≠ T →
      pairCount S < pairCount T
```

Lean proves this equivalent to target compatibility, maximum pair count among
all structures compatible with the same `w`, and uniqueness at equality.

## 5. Exact `InTargetClassK` definition

```lean
def InTargetClassK (T : SecondaryStructure n) : Prop :=
  ∃ h₂ : MaximalHelix T,
    h₂.length = 2 ∧
      (∀ h : MaximalHelix T, h.length = 2 → h = h₂) ∧
      (∀ h : MaximalHelix T, h.length ≠ 1) ∧
      (∀ h : MaximalHelix T, h ≠ h₂ → 3 ≤ h.length) ∧
      ¬ HasM5 T ∧
      ¬ HasM3Dot T
```

The witness and uniqueness clause make “exactly one” explicit.

## 6. Exact final theorem proposition

```lean
def OneShortHelixDesignabilityStatement : Prop :=
  ∀ {n : Nat} (T : SecondaryStructure n),
    InTargetClassK T →
      ∃ w : Sequence n, UniqueDesigns w T
```

This declaration is a definition of a proposition. It is neither an axiom nor a
proved theorem in Milestone 1.

## 7. Examples proved

- A valid two-position structure contains an adjacent pair.
- The arcs `(0,2)` and `(1,3)` cross and cannot be the arc set of a valid
  four-position secondary structure.
- The nested target `(())` is in `InTargetClassK`.
- `GGCC` uniquely designs `(())`, checked with `by decide` over every one of the
  nine matching-based `SecondaryStructure 4` values.
- `AUAU` does not uniquely design `(())`: both `(())` and the explicitly
  constructed `()()` competitor are compatible, while the competitor is
  distinct and has the same pair count.
- Lower integer energy is equivalent to greater pair count.
- Unique minimum energy is equivalent to compatible maximum pair count plus
  uniqueness at equality.

## 8. Build and test commands

```bash
cd /Users/ashujo/Documents/Science/rna_one_short_helix_lean
source /Users/ashujo/.elan/env
lake exe cache get
lake build
lake build +RNA.AxiomAudit
```

The final validation also runs a forbidden-token search and a byte/hash check of
the preserved manuscript.

## 9. Ambiguities and blockers

There is no blocker to the exact Milestone 1 definitions or examples.

Two traceability notes are recorded rather than silently repaired:

- the canonical manuscript jumps from Lemma 1 to Lemma 3; no Lemma 2 is
  present, so none is invented;
- Lemma 5's prose relies on the motif-free section context without repeating
  that hypothesis in its opening sentence. A future Lean statement must make
  the context explicit.

`docs/BLOCKERS.md` was not created because no exact-definition blocker remains.

## 10. Deferred to Milestone 2 and later

No colouring or final-designability proof is attempted here. Deferred work
includes pair colours; exposed multisets; levels and separation; long-helix
transfer; the two-pair bridge; global colouring recursion; sequence assignment;
adjacent cancellation/free groups; saturation and atomic designs; prefix
balance; deletion/compression; the no-tie theorem; and the proof of the final
proposition.
