# Milestone 4 report

This report records the implementation of the complete sequence assignment,
pairing-inventory optimality, and prefix/level-balance results required by
Milestone 4. It is a documentation-only follow-up to the final implementation
commit. No Lean source was changed after that implementation commit.

## 1. base and final commits

- Branch: `milestone-4-sequence-and-balance`.
- Recorded base commit: `04766212239932dc7fba49f5e24d396f0e375789`.
- Final implementation commit: `58d15f9e9e445d5fc00d371dd9f7fe1c3d8f898a`.
- Final implementation message: `Formalize Milestone 4 sequence and balance`.

The final hash above identifies the completed Lean implementation. This report
was added afterward as a docs-only follow-up, so it does not identify itself as
part of that implementation commit.

## 2. files and declarations added

The implementation added ten Lean modules and exposed them through `RNA.lean`:

- `RNA/PositionRole.lean` adds `EndpointSide`, `PositionRole`,
  `positionOfRole`, `positionRoleEquiv`, `positionRoleAt`, the role
  injectivity/surjectivity and lookup equations, `existsUnique_positionRole`,
  `unique_pair_of_positionPaired`, and the optional endpoint lookups
  `leftEndpointNode?` and `rightEndpointNode?` with their exact role equations.
- `RNA/SequenceAssignment.lean` adds the color-filtered child sets and their
  properness bounds; `orderedGreyChildren`, `greySiblingRank`,
  `greyRankLetter`; `leftLetterOfColoring`,
  `leftLetterOfProperColoring`, and their black, white, grey-anchor, grey-copy,
  range, and distinctness theorems; and `sequenceOfProperColoring` with exact
  equations for unpaired, left, right, black, white, grey, and complementary
  endpoints.
- `RNA/SequenceCertificate.lean` adds `ChildLeftLettersDistinct`,
  `LocallyDistinct`, `childLeftLettersDistinct_sequenceOfProperColoring`,
  `childLeft_ne_parentRight_sequenceOfProperColoring`,
  `structureCompatible_sequenceOfProperColoring`,
  `locallyDistinct_sequenceOfProperColoring`, `SequenceAssignmentCertificate`,
  `sequenceAssignmentCertificate`, `GlobalSequenceAssignmentCertificate`, and
  `globalSequenceAssignmentCertificate`.
- `RNA/MatchingPartner.lean` adds the symmetric relation `PositionPartner`, its
  symmetry, nonself, pairedness, uniqueness, compatibility, and ordered-arc
  theorems, plus the proof-parametric selector `partnerOf` and its specification,
  nonself, pairedness, and involution theorems.
- `RNA/PairingInventory.lean` adds `NucleotidePosition`, `nucleotideCount`,
  `GreyPair`, `NonGreyPair`, the three inventory counts, the grey/non-grey pair
  partition, explicit U/A/G/C source maps and equivalences, the four exact
  nucleotide-count theorems, `U_position_has_unique_grey_source`, compatible-pair
  classification, the limiting-position injection, the universal upper bound,
  equality-saturation machinery, and `targetClass_has_maximumPairSequence`.
- `RNA/PrefixBalance.lean` adds `nucleotideWeight`, boundary and interval
  representations, `balanceOn`, `nucleotideCountIn`, exact G-minus-C count
  equations, `prefixBalanceBoundary`, `prefixBalanceAt`, open-target-pair sets,
  the exact open-pair invariant, `completeSubtreeBalance`,
  `completedSiblingBalance`, and the paired-left, unpaired, and grey-right level
  correspondence theorems.
- `RNA/LevelImbalance.lean` adds `StrictlyInside`,
  `InteriorNucleotidePosition`, noncrossing interior closure, interior G/C
  partner maps and cardinality equality, the open-interval count bridge,
  `levelImbalance_obstruction`, and `targetUnpaired_pairing_obstruction`.
- `RNA/GlobalSequence.lean` adds `AssignedNucleotideCounts`,
  `assignedNucleotideCounts_sequenceOfProperColoring`,
  `GlobalColoringCertificate.separated`, `GlobalSequenceCertificate`, and
  `globalSequenceCertificate`.
- `RNA/Milestone4Examples.lean` adds executable finite examples for sequence
  orientation, inventory saturation, exact levels, and imbalance obstruction.
- `RNA/Milestone4AxiomAudit.lean` runs `#print axioms` over the Milestone 4
  construction and theorem surface.

The traceability documents added are
`docs/MILESTONE_4_BASE_COMMIT.txt`, `docs/MILESTONE_4_SEQUENCE_DESIGN.md`,
`docs/MILESTONE_4_PREFIX_BALANCE_DESIGN.md`, and
`docs/MILESTONE_4_AXIOM_AUDIT.md`. `docs/FORMALIZATION_BLUEPRINT.md` and
`docs/MODEL_FIDELITY_AUDIT.md` were updated. The frozen
`docs/CANONICAL_PROOF.md`, the public scientific definitions, the toolchain,
and the pinned dependencies were not changed.

## 3. position-role representation

For a target `T`, the role type is

```lean
PositionRole T := UnpairedPosition T ⊕ (PairedNode T × EndpointSide)
```

where `EndpointSide` is `left` or `right`. The map `positionOfRole` sends each
role to its actual backbone position. Partial matching proves that this map is
injective; the paired/unpaired partition proves it is surjective. Consequently
`positionRoleEquiv` is a genuine equivalence with `Fin n`, and
`positionRoleAt` gives the unique role of every position.

`no_left_right_endpoint`, `unique_pair_of_positionPaired`, and the exact
`positionRoleAt_*` equations make the three cases disjoint and exhaustive.
Endpoint lookup returns `Option (PairedNode T)` and never manufactures a
default arc.

## 4. grey-orientation architecture

The implementation uses architecture A from the design note: a well-founded
recursive left-letter assignment along the parent relation.

- Black pairs receive `G` and white pairs receive `C`.
- A grey pair at the root, or below a non-grey parent, receives `A` or `U`
  according to its rank in `orderedGreyChildren`.
- A grey pair below a grey parent copies that parent's left letter.

Actual `ProperColoring` inequalities prove that a root or non-grey interface
has at most two grey children and a grey parent has at most one grey child.
Thus `greySiblingRank_lt_two` validates the two-letter rank map, and
`greyRankLetter_injective_below_two` gives distinct letters to distinct grey
siblings. Recursion terminates because a parent pair strictly contains its
child and hence has a smaller left endpoint. The construction is deterministic
and performs no search over A/U orientations.

## 5. exact complete-sequence constructor

`sequenceOfProperColoring (chi : Coloring T) (hProper : ProperColoring chi) :
Sequence n` is total because it eliminates through the exact position-role
equivalence:

- a target-unpaired position receives `A`;
- a pair's left endpoint receives its `leftLetterOfProperColoring` value;
- its right endpoint receives the Watson–Crick complement of that value.

The pointwise theorems `sequenceOfProperColoring_unpaired`,
`sequenceOfProperColoring_left`, `sequenceOfProperColoring_right`, the four
black/white endpoint equations, `sequenceOfProperColoring_grey_left`, and
`sequenceOfProperColoring_right_eq_comp_left` expose every case. This is one
complete `Sequence n`, not a partial map and not a map completed with arbitrary
defaults.

## 6. target-compatibility theorem

`structureCompatible_sequenceOfProperColoring` proves

```lean
StructureCompatible (sequenceOfProperColoring chi hProper) T
```

for every target `T`, coloring `chi`, and proof `hProper`. Each target right
endpoint is the complement of its left endpoint, so every target arc is
Watson–Crick compatible with the constructed sequence.

## 7. local-distinctness theorem

`LocallyDistinct T w` states both parts of manuscript Lemma 13: child-left
letters are pairwise distinct at the root and at every paired interface, and
each nonroot child-left letter differs from its parent's right letter.

`childLeftLettersDistinct_sequenceOfProperColoring` and
`childLeft_ne_parentRight_sequenceOfProperColoring` prove the two components
directly from properness and the exact grey orientation.
`locallyDistinct_sequenceOfProperColoring` packages the universal result for
the constructed sequence. Its proof covers black, white, and grey parent cases;
it does not replace the statement with a finite test.

## 8. exact nucleotide-count theorems

For `w := sequenceOfProperColoring chi hProper`, the implementation proves the
four exact equalities

```text
#U(w) = greyPairCount chi
#G(w) = nonGreyPairCount chi
#C(w) = nonGreyPairCount chi
#A(w) = greyPairCount chi + targetUnpairedCount T.
```

They are exported as `nucleotideCount_U_sequenceOfProperColoring`,
`nucleotideCount_G_sequenceOfProperColoring`,
`nucleotideCount_C_sequenceOfProperColoring`, and
`nucleotideCount_A_sequenceOfProperColoring`, and are packaged by
`AssignedNucleotideCounts`. Explicit finite equivalences establish the
provenance of every counted position. In particular,
`U_position_has_unique_grey_source` gives the unique grey target pair incident
to any U position.

## 9. pairing-inventory upper bound

`compatiblePair_four_cases` classifies every compatible competitor arc by its
nucleotide endpoints. `limitingPositionOfCompatibleArc` selects its U endpoint
for an A–U/U–A arc and its C endpoint for a G–C/C–G arc. Partial matching makes
that selection injective, yielding

```lean
pairCount S ≤ nucleotideCount w U + nucleotideCount w C
```

in `pairCount_le_nucleotideCount_U_add_C` for every `SecondaryStructure n`
compatible with `w`. Substituting the exact counts gives
`pairCount_le_sequenceOfProperColoring`, namely `pairCount S ≤ pairCount T`.
This inventory argument is universal over competitors and does not assume a
preferred alternative structure.

## 10. equality-case result

When the limiting inventory bound is tight, `equality_uses_all_U_and_C` proves
that every U and every C position is paired. Since the assigned sequence has
`#G = #C`, the injective C-to-G partner map is bijective;
`all_G_paired_of_all_C_paired_of_count_eq` therefore proves that every G is
paired as well.

`equality_uses_all_limiting_nucleotides` combines these facts: every compatible
competitor satisfying `pairCount S = pairCount T` pairs every U, C, and G
position. This is an equality-saturation result only. It deliberately permits
ties and does not assert that the competitor equals the target.

## 11. prefix-balance representation and indexing convention

`nucleotideWeight` assigns `G ↦ +1`, `C ↦ -1`, and `A,U ↦ 0`.
`balanceOn` is the signed sum on an arbitrary finite set, and
`balanceOn_eq_count_G_sub_C` proves exactly that it is the integer G count minus
the integer C count. `openIntervalBalance_eq_count_G_sub_C` is the corresponding
arbitrary-sequence equation on an open interval.

`prefixBalanceBoundary w k` sums positions with `i.val < k.val`, where
`k : Fin (n + 1)`. Thus boundary `k` represents the first `k` positions.
`prefixBalanceAt w i` is the inclusive manuscript prefix at zero-indexed
position `i`; definitionally it is the boundary after `i`, whose value is
`i.val + 1`. Hence manuscript one-based prefix index `k` corresponds to Lean
position `i` with `i.val = k - 1`.

The interval subtraction lemmas include
`prefixBalanceAt_sub_eq_openIntervalBalance_of_endpoint_weights_zero`, the
direct A/U-endpoint bridge used by the imbalance proof.

The central proof is stronger than a collection of local cancellation lemmas.
It reindexes the full prefix sum by the exact position-role equivalence and
proves `prefixBalanceBoundary_eq_openPairSum`: at every boundary, the prefix
balance is exactly the sum of `Color.delta` over target pairs open at that
boundary. Completed pairs cancel exactly. This open-pair invariant is the
common source of complete-subtree balance, completed-sibling balance, and the
exact level correspondences below.

## 12. complete-subtree balance theorem

`completeSubtreeBalance` proves, for every paired target node `v`,

```lean
closedIntervalBalance (sequenceOfProperColoring chi hProper)
  v.val.left v.val.right = 0.
```

The proof compares the exact sets of strict ancestors open just before the
left endpoint and just after the right endpoint. `completedSiblingBalance`
exports the immediate sibling-use form: a complete earlier paired subtree
contributes zero before a later sibling. Both follow from the open-pair
invariant, so nesting depth and subtree size are arbitrary.

## 13. level/prefix-balance correspondence

The existing scientific definitions `pairedLevel` and `unpairedLevel` are not
changed. The following exact equalities implement manuscript Lemma 20:

- `prefixBalanceAt_pairedLeft_eq_pairedLevel`: the inclusive balance at every
  target pair's left endpoint equals its `pairedLevel`.
- `prefixBalanceAt_unpaired_eq_unpairedLevel`: the inclusive balance at every
  target-unpaired position equals its `unpairedLevel`.
- `prefixBalanceAt_greyRight_eq`: for a grey pair, the balances at its right
  and left endpoints are equal, and that common value is its `pairedLevel`.

`enclosingPairSum_eq_unpairedLevel` supplies the exact parent/ancestor bridge
for unpaired positions. These are integer equalities with the explicit indexing
convention from Section 11, not approximate depth statements.

## 14. noncrossing interior-closure theorem

`positionPartner_strictlyInside_of_enclosing_arc` is universal: if `outer` is
an actual arc of any competitor `S`, `i` lies strictly inside `outer`, and `j`
is the actual `PositionPartner S i j`, then `j` also lies strictly inside
`outer`. The proof uses the existing noncrossing and partial-matching fields of
`SecondaryStructure`; it does not assume a particular target or enumerate
folds.

Together with compatibility, the interior G↔C partner maps are injective in
both directions. `interior_G_count_eq_C_count_of_all_paired` therefore proves
equal numbers of interior G and C positions whenever all such positions are
paired. `nucleotideCountIn_openInterval_eq_card_interior` connects this exact
cardinality statement to open-interval balance.

## 15. level-imbalance obstruction

`levelImbalance_obstruction` implements manuscript Lemma 21. For every proper
target coloring, every compatible competitor `S`, and every actual A–U or U–A
arc of `S`, unequal inclusive prefix balances at the two endpoints imply an
explicit position `k` such that

```lean
(w k = G ∨ w k = C) ∧ ¬ S.positionPaired k.
```

If all interior G/C positions were paired, universal interior closure and the
G/C bijection would make the open-interval balance zero. The endpoint-weight
subtraction theorem would then make the two endpoint prefix balances equal,
contradicting the hypothesis. The conclusion is therefore a witness-bearing
unmatched limiting nucleotide, not only a count inequality.

## 16. target-unpaired pairing obstruction

`targetUnpaired_pairing_obstruction` proves that if a compatible competitor
pairs a position unpaired by the target, then the competitor leaves some G or
C position unpaired. The proof uses the same assigned sequence throughout:

1. the target-unpaired position is A;
2. compatibility makes its competitor partner U;
3. `U_position_has_unique_grey_source` identifies the U's unique grey target
   pair;
4. the exact unpaired, paired-left, and grey-right level equations convert
   prefix balances to the existing levels;
5. `Separated` makes those endpoint balances unequal;
6. the actual ordered competitor arc is passed to
   `levelImbalance_obstruction`.

The statement is universal over `S : SecondaryStructure n` and over every
actual partner witness. It prepares the later equality argument but does not
claim that a tie is impossible.

## 17. global sequence certificate

`GlobalSequenceCertificate T hK` retains the exact Milestone 3
`GlobalColoringCertificate`, its derived left-letter function, and one complete
`sequence : Sequence n`. It also retains target compatibility, local
distinctness, grey range/copy laws, exact counts, the universal pair-count
bound, equality saturation, all three balance/level correspondences, and the
target-unpaired obstruction.

`globalSequenceCertificate` defines the sequence once:

```lean
let C := globalColoringCertificate hK
let w := sequenceOfProperColoring C.coloring C.proper
```

Every certificate field then concerns that same `w`. In particular, the target
and every quantified competitor are evaluated against one shared sequence;
there is no competitor-dependent reassignment. `GlobalColoringCertificate.separated`
derives the ordinary exact-integer separation used by the final obstruction
from the retained `StrongTwoSeparatedWith` evidence.

## 18. exact maximum-pair theorem

`targetClass_has_maximumPairSequence` proves the exact universal statement

```lean
∃ w : Sequence n,
  StructureCompatible w T ∧
    ∀ S : SecondaryStructure n,
      StructureCompatible w S → pairCount S ≤ pairCount T.
```

The witness is the complete sequence constructed from the verified global
coloring. Every `SecondaryStructure n` competitor is quantified, and both the
target and competitors use that same witness. This proves maximum pair count,
not unique maximum: equal-pair competitors remain allowed in Milestone 4.
`sequenceOfProperColoring_isMaximumCompatible` is the corresponding theorem
for an arbitrary proper coloring.

## 19. examples and negative controls

`RNA/Milestone4Examples.lean` checks the architecture and the boundaries of the
proved result:

- `nestedAllBlackSequence_eq_ggcc` constructs `GGCC` for the nested all-black
  target and verifies target compatibility.
- `nestedAllGreySequence_eq_aauu` constructs the correct copied-grey
  orientation `AAUU`. In contrast, the deliberately wrong opposite orientation
  `AUAU` is compatible with both the nested target and the disjoint `()()`
  structure; `incorrectOppositeGreyOrientation_disjoint_tie` records that tie.
  This is a negative control for the grey-copy rule and for any accidental
  no-tie claim.
- `disjointAllGreySequence_eq_auua` constructs `AUUA`; its two grey root
  children receive distinct A/U orientations.
- `smallestCanonicalSequence_eq_ggcc` checks that the smallest global
  certificate also yields `GGCC`, while
  `smallestCanonicalSequence_inventory_bound` instantiates the universal
  inventory bound.
- `inventorySequence_eq_augca` constructs `AUGCA`. The distinct competitor
  pairing U–A at positions 1 and 4 and G–C at positions 2 and 3 ties the target;
  `inventoryTie_pairCount_eq` and
  `inventoryTie_uses_all_limiting_nucleotides` verify both the tie and exact
  equality saturation.
- The internal M-to-L example checks the exact values `2/3/2`: paired-left
  balance/level 2, target-unpaired balance/level 3, and grey-right
  balance/level 2, in `internalBalance_pairedLeft_value`,
  `internalBalance_unpaired_value`, and
  `internalBalance_greyRight_value`.
- `imbalanceSequence_eq_augac` constructs `AUGAC`. Its compatible competitor
  has the U–A arc from positions 1 to 3; position 2 is G and is explicitly
  unmatched. `imbalanceCompetitor_explicit_unmatched_G` exhibits that witness,
  and `imbalanceCompetitor_obstruction` obtains the universal obstruction.

The tie examples are intentional: they show that the maximum-pair and
equality-saturation theorems have not silently been strengthened into the
Milestone 5 no-tie theorem.

## 20. axiom results

`RNA/Milestone4AxiomAudit.lean` audits the grey left-letter constructor, full
sequence constructor, compatibility, local distinctness, all four exact
counts, inventory bound, equality saturation, subtree and level results,
interior closure, both obstruction theorems, global certificate, and maximum
theorem. Every audited declaration reports exactly

```text
[propext, Classical.choice, Quot.sound]
```

These are the documented standard Lean/Mathlib dependencies. There is no
project-defined axiom and no admitted result. The noncomputable definitions use
classical choice only over proved existence/uniqueness facts.

Validation at the final implementation commit completed `lake clean` followed
by a clean full `lake build` of 3048 jobs, and the required
`lake build RNA.Milestone4AxiomAudit`. The handwritten Lean source scan was
clean: no `sorry`, `admit`, custom `axiom`, or proof-establishing `unsafe` use
was present.

## 21. unresolved blockers

There are no unresolved Milestone 4 blockers. All nine stop-condition results
compile with the faithful existing definitions, so no weakened substitute,
finite-only surrogate, or `MILESTONE_4_BLOCKERS.md` was needed.

## 22. work deferred to Milestone 5

The following work remains explicitly deferred:

- adjacent complementary deletion and its preservation lemmas;
- the free-group interpretation and suffix cancellation;
- saturable prefixes, atomic words, atomic designs, and atomic endpoint
  characterization;
- concatenation and wrapping results for atomic designs;
- saturated-skeleton and saturated local-distinctness uniqueness;
- equality of the target and competitor unpaired-position sets;
- deletion and order-preserving compression of common unpaired positions;
- the no-tie theorem;
- `UniqueDesigns`;
- the final `OneShortHelixDesignabilityStatement`.

Accordingly, Theorems 22 and 23 of the canonical proof are not claimed as
implemented. Milestone 4 proves existence of a maximum-pair sequence and the
obstructions needed for the later equality argument, while allowing ties.
