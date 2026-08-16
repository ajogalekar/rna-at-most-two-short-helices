# Formalization blueprint and manuscript traceability

Status vocabulary:

- **implemented** — present and kernel-checked through Milestone 2;
- **statement drafted** — the exact proposition is present, but no theorem proof
  is claimed;
- **future milestone** — intentionally outside the completed local theory;
- **representation dependency** — requires a derived-tree, reindexing, or other
  representation theorem before implementation.

Declaration names below are the intended stable public names. Minor helper
lemmas may be renamed without changing the mapped specification.

## Manuscript definitions

| Manuscript concept | Lean module and declaration | Status through Milestone 2 |
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
| Top-down sequence assignment | `RNA.Design.Assignment.AssignedSequence` | future milestone |
| Saturable word | `RNA.Uniqueness.Atomic.Saturable` | future milestone |
| Atomic word and atomic design | `RNA.Uniqueness.Atomic.Atomic`, `AtomicDesign` | future milestone |
| Saturated target | `RNA.Uniqueness.Atomic.Saturated` | future milestone |
| Prefix balance `Lambda` | `RNA.Uniqueness.Balance.prefixBalance` | future milestone |
| Exact final theorem proposition | `RNA.Statement.OneShortHelixDesignabilityStatement` | statement drafted |

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
| 12 | `exists_proper_strongTwoSeparated_of_memK` | `RNA.Coloring.Construction` | future milestone; recursive-tree dependency |
| 13 | `localDistinctness_of_assignedSequence` | `RNA.Design.Assignment` | future milestone |
| 14 | `assignedSequence_inventory`, `pairCount_le_target`, `eq_pairCount_uses_all_limitingBases` | `RNA.Design.Assignment` | future milestone |
| 15 | `saturable_iff_adjacentCancellation`, `saturable_suffix_of_concat` | `RNA.Uniqueness.Atomic` | future milestone; word reduction/free-group development |
| 16 | `atomic_iff_everyPerfectMatching_has_outerPair` | `RNA.Uniqueness.Atomic` | future milestone |
| 17 | `concat_atomicDesigns` | `RNA.Uniqueness.Atomic` | future milestone; concatenation/reindexing dependency |
| 18 | `wrap_atomicDesigns` | `RNA.Uniqueness.Atomic` | future milestone; wrapping/reindexing dependency |
| 19 | `saturated_unique_of_localDistinctness` | `RNA.Uniqueness.Atomic` | future milestone; interval-tree induction dependency |
| 20 | `prefixBalance_at_pairLeft`, `prefixBalance_at_unpaired`, `prefixBalance_at_grayRight` | `RNA.Uniqueness.Balance` | future milestone; indexing/path dependency |
| 21 | `levelImbalance_obstruction` | `RNA.Uniqueness.Balance` | future milestone |
| 22 | `eq_target_of_tied_pairCount` | `RNA.Uniqueness.NoTie` | future milestone; deletion/compression dependency |
| 23 | `OneShortHelixDesignabilityStatement`; later theorem `oneShortHelixDesignability` | `RNA.Statement` | exact proposition drafted now; proof future |

## Exact table content retained for later milestones

The following details are constraints on the future declarations, not optional
implementation suggestions:

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
- Grey sibling orientation in the sequence assignment must be deterministic or
  relationally specified and proved to satisfy the manuscript's top-down rule.
- Atomic-design uniqueness ranges over compatible perfect matchings locally;
  public `UniqueDesigns` continues to range over all compatible partial
  matchings.

## Representation obligations carried forward

Later concatenation, wrapping, deletion, and compression results must construct
explicit order-preserving maps between finite backbones. Later tree recursion
must operate on the interval tree derived from `SecondaryStructure`, with
termination and subtree disjointness proved. No future module may change the
public theorem to quantify over only a parsed word, a saturated skeleton, or an
inductively generated tree.
