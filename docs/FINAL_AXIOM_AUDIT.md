# Final axiom and dependency audit

## Method

`RNA/FinalAxiomAudit.lean` imports the final theorem module and asks Lean's
kernel to report the transitive axioms of every load-bearing Milestone 5
declaration.  It also runs the required direct inspection commands for the
public theorem:

```lean
#check oneShortHelixDesignability
#print oneShortHelixDesignability
#print axioms oneShortHelixDesignability
```

The audit is validated from the project root with:

```text
lake build RNA.FinalAxiomAudit
```

The command completed successfully.  All declaration names in the audit
resolved, including the required `#check`, full `#print`, and
`#print axioms` commands for `oneShortHelixDesignability`.

## Audited declarations

Adjacent cancellation and suffix cancellation:

- `saturable_iff_reducesToEmpty`;
- `suffix_saturable_of_concat_saturable_of_prefix_saturable`.

Atomic words and atomic designs:

- `atomic_iff_every_saturated_hasOuterPair`;
- `AtomicDesignBlock.concat_atomicDesigns`;
- `AtomicDesignBlock.wrap_atomicDesigns`.

Saturated local-distinctness uniqueness:

- `saturated_unique_of_localDistinctness`.

Tied competitors and paired-skeleton restriction:

- `unpairedPositionSet_eq_of_tied`;
- `mem_pairedRestriction_iff_liftPairedArc_mem`;
- `pairCount_pairedRestriction`;
- `saturatedStructure_targetPairedRestriction`;
- `saturatedStructure_competitorPairedRestriction`;
- `structureCompatible_pairedRestriction`;
- `parent_pairedRestriction`;
- `locallyDistinct_targetPairedRestriction`;
- `eq_target_of_competitorPairedRestriction_eq`.

No-tie and final designability:

- `noTie_sequenceOfProperSeparatedColoring`;
- `eq_target_of_tied_pairCount`;
- `uniqueDesigns_sequenceOfProperSeparatedColoring`;
- `oneShortHelix_uniqueDesigns`;
- `oneShortHelixDesignability`.

## Kernel-reported dependencies

Lean reported exactly the same transitive axiom set for every declaration
listed above:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, the final three inspection commands produced the theorem type,
printed declaration, and dependency line:

```text
RNA.oneShortHelixDesignability : OneShortHelixDesignabilityStatement
theorem RNA.oneShortHelixDesignability :
  OneShortHelixDesignabilityStatement :=
<not imported>
'RNA.oneShortHelixDesignability' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

`<not imported>` is Lean's display for an opaque theorem body loaded through a
compiled module.  The declaration type and its transitive dependency set are
nevertheless loaded and checked; the source proof body was compiled before
the audit module.

The dependencies have their standard Lean/Mathlib meanings:

- `propext` is propositional extensionality;
- `Classical.choice` selects witnesses whose existence has already been
  proved, including finite minima, order equivalences, and matching objects;
- `Quot.sound` is quotient soundness, used transitively by Mathlib's free
  group and finite-collection infrastructure.

There is no project-defined axiom, admitted theorem, external proof oracle, or
unsafe mathematical witness in the dependency closure.

## Policy check

The substring search

```text
rg -n --glob '*.lean' 'sorry|admit|axiom|unsafe' RNA
```

was classified as follows:

- `sorry`: zero occurrences;
- `unsafe`: zero occurrences;
- `admit`: seven substring occurrences, all the ordinary English word
  “admits” or the proved identifier
  `targetClass_admits_proper_strongTwoSeparated`; none is the Lean command
  `admit`;
- `axiom`: 104 substring occurrences: 101 are `#print axioms` audit commands
  and three are explanatory audit comments containing “axiom” or “axioms”.
  None declares an `axiom`.

Thus every source-search match is documentary or an inspection command, and
none is a placeholder or additional logical premise.
