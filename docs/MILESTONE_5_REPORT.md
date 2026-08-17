# Milestone 5 report: no ties and final designability

## 1. Base commit

- Base commit: `4e575299721282869d0a7a987e7433eb642c0719`
- Proof-design commit: `4194bba4e9a04173552ac7dc6483c99329db1e9c`
- Working branch: `milestone-5-no-tie-final`

The frozen manuscript `docs/CANONICAL_PROOF.md` was not modified.

## 2. Final implementation commit

The Lean implementation commit is
`7848ae1988e4c923645fe76b7b522974ea5dbf36`
(`Formalize no-tie and final RNA designability theorem`).

## 3. Final documentation/release commit

The documentation/release content commit is
`c711723d386a886f551be3e6f793e5196c4e1a77`
(`Document Milestone 5 proof and release audits`).  A later metadata-only
provenance seal records the exact clean archive-source commit and the archive
digest; a Git commit and an archive-contained manifest cannot literally embed
their own hashes.

## 4. Files and declarations added

The implementation adds the following handwritten modules:

- `RNA/Word.lean`: finite words and exact `Sequence` bridges;
- `RNA/StructureTransport.lean`: order-embedding transport of arcs and
  structures, including skip-two deletion transport;
- `RNA/Saturable.lean`: saturation, adjacent deletion, FreeGroup encoding,
  cancellation, parity, and prefix saturation;
- `RNA/StructureOperations.lean`: concatenation, wrapping, interval
  restrictions, saturation preservation, and exact split lemmas;
- `RNA/AtomicDesign.lean`: atomic words/designs and Lemmas 16--18;
- `RNA/SaturatedUniqueness.lean`: saturated local-distinctness uniqueness;
- `RNA/TiedCompetitor.lean`: unpaired-position counts and tied-set equality;
- `RNA/PairedRestriction.lean`: paired-skeleton compression and lifting;
- `RNA/NoTie.lean`: general equality-at-the-optimum and strict unique design;
- `RNA/OneShortHelixDesignability.lean`: the final class-K theorem;
- `RNA/Milestone5Examples.lean`: positive examples and negative controls;
- `RNA/FinalAxiomAudit.lean`: transitive kernel-dependency audit.

It also adds `docs/MILESTONE_5_BASE_COMMIT.txt`,
`docs/MILESTONE_5_PROOF_DESIGN.md`, `docs/MILESTONE_5_REPORT.md`,
`docs/FINAL_STATEMENT_AUDIT.md`, `docs/FINAL_AXIOM_AUDIT.md`, and
`docs/FINAL_RELEASE_MANIFEST.md`, and updates `README.md`,
`docs/FORMALIZATION_BLUEPRINT.md`, and `docs/MODEL_FIDELITY_AUDIT.md`.

The key new declarations are `Word`, `SaturatedStructure`, `Saturable`,
`DeletesComplementaryPair`, `ReducesToEmpty`,
`saturable_iff_reducesToEmpty`,
`suffix_saturable_of_concat_saturable_of_prefix_saturable`, `Atomic`,
`AtomicDesign`, `atomic_iff_every_saturated_hasOuterPair`,
`AtomicDesignBlock.concat_atomicDesigns`,
`AtomicDesignBlock.wrap_atomicDesigns`,
`saturated_unique_of_localDistinctness`, `unpairedPositionSet_eq_of_tied`,
`pairedRestrictedSequence`, `targetPairedRestriction`,
`competitorPairedRestriction`, `locallyDistinct_targetPairedRestriction`,
`eq_target_of_competitorPairedRestriction_eq`,
`noTie_sequenceOfProperSeparatedColoring`,
`uniqueDesigns_sequenceOfProperSeparatedColoring`,
`oneShortHelix_uniqueDesigns`, and `oneShortHelixDesignability`.  The complete
load-bearing list is audited in `docs/FINAL_AXIOM_AUDIT.md`.

## 5. Word representation

The internal finite-word type is

```lean
abbrev Word := List Nucleotide
```

`Word.toSequence : Sequence z.length` is list lookup at the same finite
index.  Empty, append, `take`, `drop`, prefix/suffix, and wrapping operations
are native list operations, with exact value and length theorems.  Every
matching on a word remains an ordinary `SecondaryStructure z.length`, so this
auxiliary representation does not restrict competitors.

## 6. Cancellation architecture

`DeletesComplementaryPair` deletes one adjacent complementary pair and
`ReducesToEmpty` is its reflexive-transitive closure.  Forward matching
induction chooses a minimum-span arc, proves it adjacent, deletes it through a
strict order embedding, and recurses.  Reverse induction reinserts the two
positions and their adjacent arc.

The normal-form layer uses Mathlib's `FreeGroup (Fin 2)`.  A/C are the two
positive generators and U/G their respective inverses.  The implementation
proves both the reduction/product bridge and the append product law.  The exact
characterization is:

```lean
saturable_iff_reducesToEmpty
```

## 7. Suffix-cancellation theorem

The load-bearing theorem is:

```lean
suffix_saturable_of_concat_saturable_of_prefix_saturable
```

Its proof is algebraic and universal; it does not enumerate words or
structures.  It derives `encodedProduct y = 1` from the corresponding facts
for `x ++ y` and `x`.

## 8. Atomic definitions and Lemmas 16--18

`Atomic z` explicitly requires nonemptiness, saturability, and absence of a
saturable prefix of every length `k` with `1 ≤ k < z.length`.
`AtomicDesign z R` additionally requires that `R` is saturated, compatible,
and equal to every compatible saturated `SecondaryStructure z.length`.

Lemma 16 is `atomic_iff_every_saturated_hasOuterPair`.  Its reverse direction
uses suffix cancellation and the exact consecutive matching constructor.
Lemma 17 is `AtomicDesignBlock.concat_atomicDesigns`.  Lemma 18 is
`AtomicDesignBlock.wrap_atomicDesigns`, including the zero-child case.  Each
quantifies over arbitrary compatible saturated `SecondaryStructure` values,
not target-shaped matchings.

## 9. Saturated local-distinctness uniqueness

`saturated_unique_of_localDistinctness` states Theorem 19 for an arbitrary
saturated target `R`, arbitrary complete compatible sequence `z`, and an
arbitrary compatible saturated competitor.  It uses the actual interval tree.
Saturation eliminates singleton children and proves that the ordered paired
children exactly and consecutively cover each paired interior and the root
backbone.  Child restrictions become atomic designs by induction; wrapping is
used at paired nodes and concatenation at the virtual root.

## 10. Restriction/compression architecture

The retained positions are the target-paired positions.  Their finite ordered
subtype is ranked by `Finset.orderIsoOfFin`, producing an explicit
order-preserving equivalence with `Fin (pairedSkeletonLength T)`.  The module
defines one restricted sequence and compressed target/competitor structures.

Exact arc membership equivalences prove preservation and reflection of
matching validity, noncrossingness, compatibility, pair count, saturation,
strict paired ancestry, paired parent-child relations, root-child relations,
and child order.  These facts transfer `LocallyDistinct`.  Exact inverse arc
transport gives faithful lifting of compressed equality once the deleted
positions are unpaired in both original structures.

## 11. Common-unpaired-set theorem

`targetUnpaired_subset_competitor_unpaired` first uses the Milestone-4 equality
case and target-unpaired obstruction to prove inclusion.  Independently, the
position-role equivalence proves

```text
targetUnpairedCount S + 2 * pairCount S = n.
```

Only then does equal pair count and finite cardinality upgrade inclusion to
the exact theorem `unpairedPositionSet_eq_of_tied`.

## 12. General no-tie theorem

`noTie_sequenceOfProperSeparatedColoring` (with the readable alias
`eq_target_of_tied_pairCount`) is Theorem 22.  It assumes only a proper
separated coloring, its fixed deterministic sequence, compatibility of an
arbitrary competitor, and equality of pair counts.  It proves `S = T` through
the exact common-unpaired set, paired-skeleton compression, Theorem 19, and
faithful lifting.  No class-K hypothesis occurs in this theorem.

## 13. Unique design from a proper separated coloring

`uniqueDesigns_sequenceOfProperSeparatedColoring` combines target
compatibility and the universal Milestone-4 pair-count bound with the no-tie
theorem.  A distinct competitor cannot attain equality, so its pair count is
strictly smaller.  This is the self-contained replacement for any external
RNA-design implication.

## 14. Exact final class-K theorem

`oneShortHelix_uniqueDesigns` uses exactly
`(globalSequenceCertificate hK).sequence`; it does not choose another
sequence.  The final theorem is:

```lean
theorem oneShortHelixDesignability :
    OneShortHelixDesignabilityStatement
```

Unfolding the unchanged Milestone-1 proposition gives the exact universal
statement quoted in `docs/FINAL_STATEMENT_AUDIT.md`.

## 15. Examples and negative controls

`RNA/Milestone5Examples.lean` checks:

1. the class-K theorem on `(())` and the retained sequence `GGCC`;
2. rejection of the equal-pair `AUAU` / `()()` tie;
3. the general no-tie theorem on a target with an unpaired position;
4. a positive saturated local-distinctness instance;
5. a second perfect matching when local distinctness fails;
6. concrete deletion/compression with one common unpaired position;
7. persistence of the deliberate Milestone-4 tie, together with failure of
   its separated-coloring hypothesis.

These are kernel-checked finite examples, not premises of the universal proof.

## 16. Axiom results

The exact `#print axioms` output is transcribed in
`docs/FINAL_AXIOM_AUDIT.md`.  No project-defined axiom, admission, unsafe proof,
external proof oracle, or external RNA theorem occurs.  The exact transitive
set for the final theorem is:

```text
[propext, Classical.choice, Quot.sound]
```

## 17. Clean-build commands

The release validation is:

```bash
lake clean
lake build
lake build RNA.FinalAxiomAudit
rg -n --glob '*.lean' 'sorry|admit|axiom|unsafe' RNA RNA.lean
git diff --check
git status --short
```

The non-clean full build and the dedicated audit build both passed before the
implementation commit.  The same commands are run once more from `lake clean`
for the release record.

## 18. Remaining limitations

The development proves the frozen theorem only for the frozen class K and
energy model.  It does not model wobble pairs, thermodynamic loop/stacking
energies, pseudoknots, or other target classes.

## 19. Manuscript alterations

No manuscript theorem in Lemmas 15--19 or Theorems 22--23 required weakening
or alteration.  The formal energy remains exactly minus pair count, pairing is
Watson--Crick only, and competitors remain arbitrary compatible noncrossing
partial matchings on the same complete sequence.

## 20. Work remaining outside Lean

There is no mathematical proof work remaining outside Lean for the stated
theorem.  Empirical RNA modeling, alternative energy models, biological
validation, and extensions beyond the frozen specification remain outside this
formalization.
