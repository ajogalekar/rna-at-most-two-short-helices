# Formalization blueprint and manuscript traceability

Status vocabulary:

- **implemented** — present and kernel-checked in the current source build;
- **statement drafted** — the exact proposition is present, but no theorem proof
  is claimed;
- **future work** — intentionally outside the current Lean development.

Declaration names below are the intended stable public names. Minor helper
lemmas may be renamed without changing the mapped specification.

## Manuscript definitions

| Manuscript concept | Lean module and declaration | Current status |
|---|---|---|
| Four bases `A,C,G,U` | `RNA.Alphabet.Nucleotide` | implemented |
| Complement involution | `RNA.Alphabet.Nucleotide.comp` | implemented |
| Watson–Crick compatibility | `RNA.Alphabet.Compatible` | implemented |
| Length-`n` sequence | `RNA.Alphabet.Sequence` | implemented |
| Normalized ordered arc | `RNA.Structure.Arc` | implemented |
| Endpoint incidence/shared endpoint | `RNA.Structure.Arc.Incident`, `Arc.ShareEndpoint` | implemented |
| Crossing/interleaving arcs | `RNA.Structure.Arc.Crosses` | implemented |
| Partial matching/noncrossing predicates | `RNA.Structure.IsPartialMatching`, `IsNoncrossing` | implemented |
| Secondary structure | `RNA.Structure.SecondaryStructure` | implemented |
| Target/structure compatibility | `RNA.Structure.StructureCompatible` | implemented |
| Pair count and energy | `RNA.Structure.pairCount`, `energy` | implemented |
| Unique designability | `RNA.Structure.UniqueDesigns`, `Designable` | implemented |
| Virtual root, paired nodes, unpaired nodes | `RNA.IntervalTree.IntervalNode`, `PairedNode`, `UnpairedPosition` | implemented |
| Smallest-enclosing parent and children | `RNA.IntervalTree.parent`, `pairedChildren`, `unpairedChildren`, `orderedChildren` | implemented; representation dependency discharged by parent proofs |
| Paired degree | `RNA.IntervalTree.pairedDegree` | implemented |
| Motifs `m5` and `m3dot` | `RNA.Motifs.HasM5`, `HasM3Dot`, `MotifFree` | implemented |
| Pair colours `B,W,G` | `RNA/Color.lean`: `RNA.Color` | implemented |
| Colour inverse and integer increment | `RNA/Color.lean`: `RNA.Color.inv`, `RNA.Color.delta` | implemented |
| Exposed multiset and properness | `RNA/Coloring.lean`: `RNA.exposedMultiset`, `RNA.ProperColoring` | implemented |
| Inclusive level and entry level | `RNA/Coloring.lean`: `RNA.pairedLevel`, `RNA.entryLevel` | implemented; exact integer ancestor sums and parent recursion proved |
| Separated colouring | `RNA/Coloring.lean`: `RNA.Separated` | implemented |
| Strong 2-separation and residues | `RNA/Coloring.lean`: `RNA.StrongTwoSeparated`; `RNA/Endpoint.lean`: `RNA.StrongTwoSeparatedWith` | implemented with `ZMod 2` residues |
| Exact stacked successor | `RNA.Helix.Arc.Stacked` | implemented |
| Maximal helix/run and length | `RNA.Helix.IsMaximalHelixRun`, `IsMaximalHelix`, `MaximalHelix`, `MaximalHelix.length` | implemented; finite-descriptor completeness proved |
| Target class `K` | `RNA.TargetClass.InTargetClassK` | implemented |
| Loop node and `L/M/E` shapes | `RNA/Endpoint.lean`: `RNA.IsLoopNode`, `RNA.EndpointType`, `RNA.IsLEndpoint`, `RNA.IsMEndpoint`, `RNA.IsEEndpoint` | implemented |
| `xi`/`eta` entry interfaces | `RNA/Endpoint.lean`: `RNA.StrongTwoSeparatedWith`, `RNA.endpoint_forcedResidues` | implemented |
| Admissible first colour | `RNA/Color.lean`: `RNA.Color.AdmissibleAt` | implemented |
| `Safe(H,epsilon,c1)` | `RNA/HelixTransfer.lean`: `RNA.Safe` (parameterized by helix length) | implemented |
| Helix paired/unpaired subtrees and strict recursion measure | `RNA.HelixSubtree`: `pairedHelixSubtree`, `unpairedHelixSubtree`, `helixSubtreePairCount` | implemented |
| Exact-domain subtree coloring and extension | `RNA.SubtreeColoring`: `SubtreeColoring`, `ExtendsSubtree`, `assembleSubtreeColoring` | implemented |
| Recursive subtree coloring certificate | `RNA.SubtreeConstruction`: `SubtreePostcondition`, `SubtreeCertificate`, `constructSubtree` | implemented |
| Proof-bearing total global coloring | `RNA.GlobalColoring`: `GlobalColoringCertificate`, `globalColoringCertificate` | implemented |
| Unique position-role partition | `RNA.PositionRole`: `PositionRole`, `positionRoleEquiv`, `positionRoleAt` | implemented; target-unpaired/left/right roles cover the backbone without a default arc |
| Top-down sequence assignment (Section 11) | `RNA.SequenceAssignment`: `leftLetterOfColoring`, `leftLetterOfProperColoring`, `sequenceOfProperColoring` | implemented; deterministic ordered grey-sibling ranks and grey-parent copying |
| Sequence compatibility and local certificate | `RNA.SequenceCertificate`: `structureCompatible_sequenceOfProperColoring`, `SequenceAssignmentCertificate`, `globalSequenceAssignmentCertificate` | implemented |
| Exact nucleotide inventory and maximum pair count | `RNA.PairingInventory`: `nucleotideCount`, `greyPairCount`, `nonGreyPairCount`, `pairCount_le_sequenceOfProperColoring`, `equality_uses_all_limiting_nucleotides` | implemented |
| Prefix balance `Lambda` | `RNA.PrefixBalance`: `prefixBalanceBoundary`, `prefixBalanceAt` | implemented with zero-indexed boundary/inclusive conversion |
| Noncrossing level-imbalance obstruction | `RNA.LevelImbalance`: `positionPartner_strictlyInside_of_enclosing_arc`, `levelImbalance_obstruction`, `targetUnpaired_pairing_obstruction` | implemented |
| Proof-bearing global sequence | `RNA.GlobalSequence`: `GlobalSequenceCertificate`, `globalSequenceCertificate` | implemented; every field uses the same retained sequence witness |
| Finite internal word and fixed-length bridge | `RNA.Word`: `Word`, `Word.toSequence`, `Sequence.toWord` | implemented; list values and both round trips are proved exactly |
| Saturated structure and saturable word | `RNA.Saturable`: `SaturatedStructure`, `Saturable` | implemented |
| Adjacent complementary reduction | `RNA.Saturable`: `DeletesComplementaryPair`, `ReducesToEmpty`, `saturable_iff_reducesToEmpty` | implemented |
| Free-group product and suffix cancellation | `RNA.Saturable`: `encodedProduct`, `saturable_iff_encodedProduct_eq_one`, `suffix_saturable_of_concat_saturable_of_prefix_saturable` | implemented with `FreeGroup (Fin 2)` |
| Atomic word and atomic design | `RNA.AtomicDesign`: `Atomic`, `AtomicDesign` | implemented |
| Order-preserving structural operations | `RNA.StructureTransport`, `RNA.StructureOperations` | implemented; map/pullback, consecutive append, wrapping, and interval restrictions |
| Target-paired skeleton compression | `RNA.PairedRestriction`: `pairedRestrictedSequence`, `targetPairedRestriction`, `competitorPairedRestriction` | implemented with an explicit increasing finite-order equivalence |
| Exact final theorem proposition | `RNA.Statement.OneShortHelixDesignabilityStatement` | implemented since Milestone 1; proved by `oneShortHelixDesignability` in `RNA.OneShortHelixDesignability` |

## Lemmas and theorems 1–23

The canonical manuscript jumps from Lemma 1 to Lemma 3. **There is no Lemma 2
in the authoritative file.** This blueprint neither invents one nor renumbers
later results.

| No. | Intended Lean declaration | Module | Status/dependency |
|---:|---|---|---|
| 1 | `motifBounds` | `RNA.Motifs` | implemented; derived-parent dependency discharged |
| 2 | — | — | absent from canonical manuscript |
| 3 | `strongTwoSeparated_implies_separated` | `RNA.Coloring` | implemented |
| 4 | `stacked_iff_unique_pairedChild_no_unpaired` | `RNA.HelixPartition` | implemented, including both tree directions |
| 5 | `existsUnique_endpointType_of_loopNode`, `parentOfHead_root_or_classified` | `RNA.Endpoint` | implemented |
| 6 | `endpoint_forcedResidues` | `RNA.Endpoint` | implemented from global levels and properness |
| 7 | `RootRow.proper`, root allocation coverage witness | `RNA.LocalAllocations` | implemented |
| 8 | `ordinaryMExposure_proper`, `designatedMExposure_proper`, L/E row theorems | `RNA.LocalAllocations` | implemented on actual ordered-child assignments |
| 9 | complete root/loop allocation coverage witnesses | `RNA.LocalAllocations` | implemented; unique short child and long-child obligations included |
| 10 | `longHelixTransfer`, `exists_longHelixTransfer` | `RNA.HelixTransfer`; global bridge in `RNA.HelixTransferBridge` | implemented |
| 11 | `validTwoPair_iff_mem_table`, `validTwoPairFinset_eq_table` | `RNA.HelixTransfer` | implemented as an exact exhaustive table |
| 12 | `targetClass_admits_proper_strongTwoSeparated` (via `exists_proper_strongTwoSeparatedWith`) | `RNA.GlobalColoring` | implemented; total exact-domain root-forest assembly and well-founded helix-subtree recursion |
| 13 | `locallyDistinct_sequenceOfProperColoring` | `RNA.SequenceCertificate` | implemented; root child-left injectivity and nonroot parent-right exclusion |
| 14 | `nucleotideCount_U_sequenceOfProperColoring`, `nucleotideCount_G_sequenceOfProperColoring`, `nucleotideCount_C_sequenceOfProperColoring`, `nucleotideCount_A_sequenceOfProperColoring`, `pairCount_le_sequenceOfProperColoring`, `equality_uses_all_limiting_nucleotides` | `RNA.PairingInventory` | implemented; explicit finite bijections, arbitrary-compatible-structure injection, and U/C/G equality saturation |
| 15 | `saturable_iff_reducesToEmpty`, `saturable_iff_encodedProduct_eq_one`, `suffix_saturable_of_concat_saturable_of_prefix_saturable` | `RNA.Saturable` | implemented; adjacent deletion/reinsertion plus Mathlib free-group product |
| 16 | `atomic_iff_every_saturated_hasOuterPair` | `RNA.AtomicDesign` | implemented for every compatible saturated matching of the word |
| 17 | `concat_atomicDesigns` | `RNA.AtomicDesign` | implemented with exact word-indexed concatenation and block isolation |
| 18 | `wrap_atomicDesigns` | `RNA.AtomicDesign` | implemented, including the empty child-list case and proper-prefix theorem |
| 19 | `saturated_unique_of_localDistinctness` | `RNA.SaturatedUniqueness` | implemented by strong induction over actual paired intervals, with atomic child blocks and root concatenation |
| 20 | `prefixBalanceAt_pairedLeft_eq_pairedLevel`, `prefixBalanceAt_unpaired_eq_unpairedLevel`, `prefixBalanceAt_greyRight_eq` | `RNA.PrefixBalance` | implemented; complete-subtree and completed-sibling balance proved against the existing exact levels |
| 21 | `levelImbalance_obstruction` (using `positionPartner_strictlyInside_of_enclosing_arc` and `interior_G_count_eq_C_count_of_all_paired`) | `RNA.LevelImbalance` | implemented; produces an explicit unpaired G/C position |
| 22 | `noTie_sequenceOfProperSeparatedColoring`, `eq_target_of_tied_pairCount` | `RNA.NoTie` | implemented for every proper separated coloring and every compatible tying competitor |
| 23 | `oneShortHelix_uniqueDesigns`, `oneShortHelixDesignability` | `RNA.OneShortHelixDesignability` | implemented; proves the original Milestone-1 proposition with the exact Milestone-4 witness |

## Exact table content and later constraints

The following details record frozen constraints on the implemented and future
declarations; they are not optional implementation suggestions:

- Lemma 1 must distinguish root/nonroot and presence/absence of unpaired
  children, yielding paired-child bounds `2/4` at the root and `1/3` at a
  nonroot pair.
- Lemma 5's sentence relies on the motif-free section context even though that
  hypothesis is not repeated in its opening clause. Its Lean statement must
  take `MotifFree T` or `InTargetClassK T` explicitly.
- Lemma 8's ordinary `M` ports are `B -> (B,G)/(B,G,G)`,
  `W -> (W,G)/(W,G,G)`, and `G -> (B,W)/(B,W,G)`. With a distinguished short
  child, that child is a specific grey occurrence and the remaining ports are
  `B -> B/(B,G)`, `W -> W/(W,G)`, and `G -> B/(B,W)`.
- Lemma 11's complete bridge table is `xi->xi: BB,WW`;
  `xi->eta: BG,WG`; `eta->xi: GB,GW`; `eta->eta: BB,WW,GG`.
- `Safe` is a deliberately stronger construction invariant, not a
  characterization of every valid two-pair colouring.
- Grey sibling orientation is now implemented deterministically by ordered
  grey-sibling rank in `RNA.SequenceAssignment`; a grey child of a grey parent
  recursively copies its parent's left letter.
- Atomic-design uniqueness ranges over compatible perfect matchings locally;
  public `UniqueDesigns` continues to range over all compatible partial
  matchings.

## Milestone 3 global-construction traceability

Theorem 12 now has the exact frozen-manuscript conclusion over the original
matching-based `SecondaryStructure` and existing `Coloring T` type. The
implementation first proves exact paired/unpaired helix-subtree decompositions
and strict decrease of subtree cardinality. It then recursively constructs
proof-bearing exact-domain `SubtreeColoring` values, flattens pairwise-disjoint
root-child subtrees into one total coloring, and proves actual root and
nonroot exposures proper. Gray pairs and target-unpaired positions are related
to the existing exact integer levels only through `levelParity`; neither the
target model nor the definition of global level is weakened.

The named global witness is retained by `globalColoringCertificate`. Milestone
4 reuses that exact coloring and root allocation in `globalSequenceCertificate`
rather than invoking a new existence search.

## Milestone 4 sequence, inventory, and balance traceability

Section 11 is implemented by the default-free role partition in
`RNA.PositionRole`, the deterministic top-down constructor
`leftLetterOfColoring`, and the total sequence `sequenceOfProperColoring`.
`structureCompatible_sequenceOfProperColoring` proves compatibility at the
actual endpoints of every target arc, while
`locallyDistinct_sequenceOfProperColoring` is the kernel-checked Lemma 13.

Lemma 14 is implemented in `RNA.PairingInventory`. Explicit finite bijections
identify U positions with grey target pairs, G and C positions with non-grey
target pairs, and A positions with the disjoint sum of grey pairs and
target-unpaired positions. `pairCount_le_sequenceOfProperColoring` proves the
universal inventory bound, and `equality_uses_all_limiting_nucleotides` proves
that every U, C, and G is paired in a tying compatible competitor. The
witness-bearing class-K maximum theorem is
`targetClass_has_maximumPairSequence`.

Lemma 20 is implemented in `RNA.PrefixBalance` using the manuscript's exact
`pairedLevel` and `unpairedLevel`, with
`completeSubtreeBalance` supplying the zero-balance subtree invariant. Lemma
21 is implemented by `levelImbalance_obstruction` in `RNA.LevelImbalance`,
after proving noncrossing interior closure and balanced interior G/C inventory
under total interior pairing. `targetUnpaired_pairing_obstruction` is the
Milestone 4 corollary needed by the later no-tie proof.

`globalSequenceCertificate` retains one global coloring and one sequence and
packages compatibility, local distinctness, exact counts, the maximum bound,
the equality case, all prefix/level identities, and the target-unpaired
pairing obstruction. Milestone 5 consumes those exact fields rather than
reconstructing substitutes.

## Milestone 5 cancellation, restriction, and no-tie traceability

`RNA.Word` uses `List Nucleotide` internally because cancellation needs words
of changing length, `take`, `drop`, concatenation, and wrapping. The proved
`Word.toSequence`/`Sequence.toWord` bridge preserves every indexed value. This
does not change the public model: the final target, witness, and competitors
remain `Sequence n` and `SecondaryStructure n`.

`RNA.Saturable` defines adjacent complementary deletion and its reflexive-
transitive closure. `saturable_iff_reducesToEmpty` proves both deletion and
reinsertion directions over arbitrary compatible noncrossing perfect
matchings. The homomorphic product `encodedProduct : Word → FreeGroup (Fin 2)`
sends A/U and C/G to two generator/inverse pairs.
`saturable_iff_encodedProduct_eq_one` and `encodedProduct_append` make
`suffix_saturable_of_concat_saturable_of_prefix_saturable` an algebraic
cancellation result rather than a finite enumeration.

`RNA.StructureTransport` maps and pulls structures through arbitrary finite
order embeddings. `RNA.StructureOperations` specializes this layer to exact
consecutive append, wrapping, prefixes, and open/closed intervals, including
saturation and compatibility transport. `RNA.AtomicDesign` then proves the
outer-pair characterization, concatenation of atomic designs with distinct
first letters, and wrapping with an avoided closing letter.

For a tied competitor, `RNA.TiedCompetitor.unpairedPositionSet_eq_of_tied`
first proves target-unpaired inclusion using the Milestone-4 obstruction, then
uses the exact paired/unpaired cardinality equation to obtain equality.
`RNA.PairedRestriction` deletes that common set through the increasing
`pairedPositionExpansion`/`pairedPositionCompression` equivalence. It proves
saturation, compatibility, pair-count preservation, tree-child transport,
local-distinctness transfer, and faithful lifting through
`eq_target_of_competitorPairedRestriction_eq`.

The source dependency chain in `RNA.NoTie` is exactly: equality inventory,
target-unpaired obstruction, common-unpaired equality, paired-skeleton
compression, saturated local-distinctness uniqueness, and faithful lifting.
`uniqueDesigns_sequenceOfProperSeparatedColoring` combines its equality case
with the Milestone-4 universal upper bound. `RNA.OneShortHelixDesignability`
then specializes to the coloring and sequence already stored by
`globalSequenceCertificate`; it does not choose a replacement sequence.

`pairedNode_atomicDesign_of_localDistinctness` in
`RNA.SaturatedUniqueness` performs strong induction on the closed length of an
actual target pair. Its children
are packaged as atomic blocks, `wrap_atomicDesigns` proves the displayed
closed block atomic, and exact word-equality transport identifies that block
with the closed target restriction. At the virtual root,
`saturated_unique_of_localDistinctness` reconstructs the complete sequence as
the concatenation of its root-child words and applies atomic concatenation to
both the target and an arbitrary saturated competitor. Theorem 19 and its
Theorems 22–23 consumers compile together in the current source build.

## Representation obligations discharged

Milestone 5 constructs explicit order-preserving maps for concatenation,
wrapping, deletion, interval restriction, and target-paired compression. The
Milestone 3 recursion remains on the interval tree derived from the original
`SecondaryStructure`. Neither the internal word layer nor the saturated
restriction narrows the final competitor quantifier: faithful lifting returns
the proof to the original arbitrary noncrossing partial-matching model.
