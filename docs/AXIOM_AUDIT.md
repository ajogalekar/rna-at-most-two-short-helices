# Axiom audit

Command run from the project root:

```bash
source /Users/ashujo/.elan/env
lake build +RNA.AxiomAudit
```

The reproducible `#print axioms` commands are in `RNA/AxiomAudit.lean`.

## Results

| Declaration | Reported axioms |
|---|---|
| `RNA.Nucleotide.comp_comp` | none |
| `RNA.Nucleotide.comp_ne_self` | none |
| `RNA.compatible_symm` | `propext` |
| `RNA.energy_lt_iff_pairCount_gt` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.uniqueDesigns_iff_maximum_and_unique_count` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.uniqueMinimumEnergy_iff_maximum_and_unique_count` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.pairedNode_laminar` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.parent_pair_smallest` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.parent_isParent` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.isParent_unique` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.parent_eq_iff_isParent` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.parent_wellDefined_unique` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.motifBounds` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.MaximalHelix.ext_outer` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.exists_maximalHelix_iff_run` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.MaximalHelix.helixMembers_card` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.MaximalHelix.eq_or_disjoint_members` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.Examples.adjacent_pair_is_present` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.Examples.crossingArcSet_cannot_be_a_secondaryStructure` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.Examples.nestedTarget_in_classK` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.Examples.ggcc_unique_design` | `propext`, `Classical.choice`, `Quot.sound` |
| `RNA.Examples.auau_not_unique_design` | `propext`, `Classical.choice`, `Quot.sound` |

`propext`, `Classical.choice`, and `Quot.sound` are the ordinary foundational
principles shipped with Lean and used throughout Mathlib. No declaration above
depends on a project-defined axiom, an admitted theorem, native-code proof
oracle, or an external computation.

The finite examples use `by decide`. Their propositions are reduced and their
proof terms checked by Lean's kernel; `native_decide` is not used.

## Audit conclusion

No dependency beyond normal Lean/Mathlib foundations was found. The project
contains no custom `axiom` declaration.

## Forbidden-token source scan

```bash
rg -n -w 'sorry|admit|axiom|unsafe' RNA.lean RNA --glob '*.lean'
```

This command produced no output. Audit documents contain these words only as
quoted search terms or explanatory prose; they are not Lean declarations or
proof terms.
