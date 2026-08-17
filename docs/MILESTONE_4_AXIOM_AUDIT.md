# Milestone 4 axiom audit

## Method

`RNA/Milestone4AxiomAudit.lean` imports the completed global sequence
certificate and runs `#print axioms` on the load-bearing Milestone 4 sequence,
local-distinctness, inventory, prefix-balance, noncrossing-obstruction, and
global-certificate declarations.

The audit was compiled from the project root with:

```text
lake build RNA.Milestone4AxiomAudit
```

The build completed successfully.

## Audited declarations

Sequence construction and local correctness:

- `leftLetterOfColoring`;
- `sequenceOfProperColoring`;
- `structureCompatible_sequenceOfProperColoring`;
- `locallyDistinct_sequenceOfProperColoring`.

Exact inventory and maximum pair count:

- `nucleotideCount_U_sequenceOfProperColoring`;
- `nucleotideCount_G_sequenceOfProperColoring`;
- `nucleotideCount_C_sequenceOfProperColoring`;
- `nucleotideCount_A_sequenceOfProperColoring`;
- `pairCount_le_nucleotideCount_U_add_C`;
- `pairCount_le_sequenceOfProperColoring`;
- `equality_uses_all_limiting_nucleotides`.

Prefix balance and manuscript Lemma 20:

- `completeSubtreeBalance`;
- `prefixBalanceAt_pairedLeft_eq_pairedLevel`;
- `prefixBalanceAt_unpaired_eq_unpairedLevel`;
- `prefixBalanceAt_greyRight_eq`.

Noncrossing closure and manuscript Lemma 21:

- `positionPartner_strictlyInside_of_enclosing_arc`;
- `interior_G_count_eq_C_count_of_all_paired`;
- `levelImbalance_obstruction`;
- `targetUnpaired_pairing_obstruction`.

Global witness and maximum theorem:

- `globalSequenceCertificate`;
- `targetClass_has_maximumPairSequence`.

## Kernel-reported dependencies

Lean reported exactly the same transitive axiom set for every declaration:

```text
[propext, Classical.choice, Quot.sound]
```

No audited declaration depends on a project-defined axiom or admitted result.

## Interpretation

- `propext` is propositional extensionality.
- `Classical.choice` selects witnesses already justified by proved existence or
  uniqueness results, including unique position roles, finite bijection
  inverses, matching partners, and the retained global coloring certificate.
- `Quot.sound` is the standard quotient soundness principle used transitively
  by Lean/Mathlib finite collections and related library constructions.

The noncomputable definitions do not bypass the kernel: their specifications,
termination arguments, injectivity/surjectivity proofs, compatibility proofs,
and obstruction theorems are ordinary proof terms checked by Lean. The finite
cardinality arguments use proved equivalences and injections; no external
enumerator, native-code oracle, or unsafe mathematical witness is used.

## Result

Milestone 4 satisfies the requested axiom policy. The complete constructed
sequence, target compatibility, local distinctness, exact nucleotide counts,
maximum-pair theorem, equality saturation, prefix/level correspondence, and
level-imbalance obstructions depend only on the three accepted standard
principles above.
