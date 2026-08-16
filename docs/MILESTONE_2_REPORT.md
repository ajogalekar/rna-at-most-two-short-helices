# Milestone 2 report

## 1. Base and final commits

- Milestone 1 base commit:
  `d857457487b7ee74b0d49dd60388d549b618e861`
  (`d857457 Formalize Milestone 1 RNA model and theorem statement`).
- Milestone 2 final implementation commit:
  `9c6f752c2fcf174fe91af35eab21cddc62cc69da`
  (`9c6f752 Formalize Milestone 2 local coloring theory`).
- Working branch: `milestone-2-local-coloring`.

This report is added by the immediate documentation-only follow-up commit so
that it can record the already-fixed implementation hash.  No Lean source is
changed after the implementation commit.

The base hash is also recorded verbatim in `docs/MILESTONE_2_BASE_COMMIT.txt`.
The pre-existing Milestone 1 source archive was moved without modification to
`/Users/ashujo/Documents/Science/milestone_1_review_source.zip`; its SHA-256 is
`e9fad0d8cd06c7e9fb5a0802bdda1ea5399012dce75a2a605fd48c6e4967ca05`.

## 2. Modules and principal declarations added

### `RNA/HelixPartition.lean`

- `exists_maximalHelix_containing`
- `existsUnique_maximalHelix_containing`
- `maximalHelixContaining`, `mem_maximalHelixContaining`
- `biUnion_maximalHelices_members`, `disjoint_helixMembers_of_ne`
- `stacked_iff_unique_pairedChild_no_unpaired`
- `MaximalHelix.headNode`, `terminalNode`, `orderedMembers`
- `MaximalHelix.parent_offsetNode_succ`
- `MaximalHelix.existsUnique_outgoing_of_terminal_child`
- `shortHelix`, `shortHelix_length`
- `length_at_least_three_of_ne_shortHelix`
- `no_maximalHelix_length_one`

### `RNA/Color.lean`

- `Color`, `Color.inv`, `Color.delta`, `Color.NonGrey`
- `Parity = ZMod 2`, `Parity.opposite`
- `Color.deltaParity`, `Color.AdmissibleAt`
- `ProperExposure`, `ProperAdjacent`

### `RNA/Coloring.lean`

- `Coloring T = PairedNode T -> Color`
- `childColorMultiset`, `exposedMultiset`, `ProperColoring`
- `pairedAncestors`, `entryLevel`, `pairedLevel`
- `interfaceLevel`, `unpairedLevel`, `nodeLevel`
- `entryLevel_eq_interfaceLevel` and child/root recursion lemmas
- `Separated`, `StrongTwoSeparated`
- `strongTwoSeparated_implies_separated`

### `RNA/Endpoint.lean`

- `IsLoopNode`, `LoopNode`
- `IsLEndpoint`, `IsMEndpoint`, `IsEEndpoint`, `EndpointType`
- `helixChain_iff`
- `existsUnique_endpointType_of_loopNode`
- `parentOfHead_root_or_classified`
- `existsUnique_outgoing_of_root_child`
- `existsUnique_outgoing_of_loop_child`
- `targetClass_root_pairedChildCount_pos`
- `StrongTwoSeparatedWith`
- `endpoint_forcedResidues`
- `forcedResidues_of_proper_strongTwoSeparated`

### `RNA/LocalAllocations.lean`

- `PortAssignment`, `ChildPortAssignment`, `assignedChildPorts`
- `RootRow`, `EtaRootRow`, root table properness/admissibility
- `ordinaryMPorts`, `ordinaryMExposure`
- `designatedMPortsAt`, `designatedMExposure`
- `designatedM_tight_exposure`, `designatedM_tight_counts`
- `orderedPairedChild`, `pairedChildIndex`, `installPortRow`
- `ordinaryMActualExposure_eq`, `designatedMActualExposure_eq`
- `outgoingHelixAtRootSlot`, `outgoingHelixAtLoopSlot`
- `RootAllocation`, `LoopAllocation`
- `completeRootAllocationCoverage`
- `completeLoopAllocationCoverage`
- `completeNonrootAllocationCoverage`
- `RootAllocation.safeOutgoing`, `LoopAllocation.safeOutgoing`
- `outgoing_short_child_cases`, `atMostOne_short_outgoing_child`

### `RNA/HelixTransfer.lean`

- `exitResidue`, `inclusiveResidueAt`, `GreysAt`
- `InternallyProper`, `ClosesNonGrey`, `LocalTransfer`
- `Safe`
- constant, one-grey, all-grey, and grey-then-black word constructors
- `longHelixTransfer`, `exists_longHelixTransfer`
- `ValidTwoPair`, `twoPairTable`
- `validTwoPair_iff_mem_table`, `validTwoPairFinset_eq_table`
- `eta_to_xi_first_grey`, `xi_to_eta_second_grey`
- `safe_twoPair_target_eta_second_grey`

### `RNA/HelixTransferBridge.lean`

- `helixColorWord`, `HelixWordInstalled`
- `helixRunningResidue`
- `helixRunningResidue_eq_levelParity_pairedLevel`
- `exitResidue_helixColorWord_eq_terminalLevelParity`
- `greysAt_helixColorWord_iff_global`
- installed-transfer pointwise, terminal, grey, and non-grey corollaries
- `internallyProper_helixColorWord`
- `safe_installed_twoPair_mEndpoint_closes_grey`
- `safe_installed_lengthTwoTransfer_mEndpoint_closes_grey`

### Tests and audits

- `RNA/Milestone2Examples.lean`
- `RNA/Milestone2AxiomAudit.lean`
- `docs/MILESTONE_2_DESIGN_DECISIONS.md`
- `docs/MILESTONE_2_AXIOM_AUDIT.md`
- this report and the updated blueprint/model-fidelity audit.

## 3. Maximal-helices partition result

Yes.  `existsUnique_maximalHelix_containing` proves that every target arc lies
in exactly one maximal helix.  The existence proof maximizes only genuine
consecutive stack segments containing the selected target arc, so it cannot
jump over a missing pair.  `biUnion_maximalHelices_members` proves that the
union of all member sets is exactly `T.arcs`; common-member uniqueness and
`disjoint_helixMembers_of_ne` give pairwise disjointness.

The canonical `maximalHelixContaining` is noncomputable choice from this unique
witness.  Ordered offset nodes, heads, terminals, consecutive parents, and
unique outgoing helices are all connected to the original interval tree.

## 4. Colors and parity

Colors are the finite inductive type `Color.black | Color.white | Color.grey`.
`Color.delta` has integer codomain with values `1`, `-1`, and `0`.
`Parity` is `ZMod 2`; `Parity.opposite r = r + 1`.  Thus black and white both
have `deltaParity = 1`, while grey has `deltaParity = 0`.

Exact integer levels are never replaced by parity.  Reduction through
`levelParity` occurs only in strong two-separation and local transfer.

## 5. Properness, levels, and separation

`Coloring T` assigns a color only to `PairedNode T`, making non-target and
unpaired coloring ill-typed.  A root exposure contains child colors.  A paired
exposure contains `inv (chi p)` plus its actual paired-child colors.

`ProperExposure X` means:

```lean
X.count Color.black <= 1 ∧
X.count Color.white <= 1 ∧
X.count Color.grey <= 2
```

`entryLevel` is the integer delta sum over all strict paired ancestors;
`pairedLevel` adds the node's own delta.  Parent-set decomposition proves that
this ancestor sum is exactly zero at a root child and exactly the paired
parent's inclusive level otherwise.  An unpaired level is its computed
parent-interface level.

`Separated` forbids equality between any grey-pair integer level and any
unpaired integer level.  `StrongTwoSeparated` supplies a residue `xi`, places
all unpaired levels at `xi`, and all grey-pair levels at `xi.opposite`.
`strongTwoSeparated_implies_separated` proves the exact implication.

## 6. Endpoint taxonomy and forced residues

`existsUnique_endpointType_of_loopNode` proves that every motif-free loop node
has exactly one L/M/E type.  The absent no-unpaired/exactly-one-paired-child
case is contradicted by the full tree-chain equivalence.  A nonroot parent of a
maximal-helix head is a loop and is either L with exactly one paired child or M;
the root is returned as the separate alternative.

`forcedResidues_of_proper_strongTwoSeparated` uses the global coloring,
integer-level, properness, and strong-separation definitions.  It proves that
an L endpoint is at `xi`, with non-grey own and child colors, and that an M
endpoint is at `xi.opposite`.  E remains residue-free.

## 7. Root and loop allocations

The root rows are executable port vectors for arities one through four with
the manuscript's exact B / BW / BWG / BWGG colors and residue choices.
`completeRootAllocationCoverage` installs a selected row on actual ordered root
children, proves the relevant root condition, properness and admissibility, and
moves grey to the actual short child in an eta row.  Xi-row short ports are
proved non-grey.

The E and L rows have their exact singleton or `{inv(a),a}` exposures.  The six
ordinary M rows and six designated M rows are exact multiset equalities, both
abstractly and after installation on actual ordered children.  The tight
grey-closing/two-child designated row is exactly `{G,G,B}` with counts
`(1,0,2)`.

## 8. Complete allocation coverage

`completeNonrootAllocationCoverage` chooses the unique endpoint type and
returns a proof-bearing `LoopAllocation` on actual children.  Each actual child
is connected to its unique outgoing maximal helix.  Every outgoing port is
`Safe`; every outgoing helix is either the global short helix or has length at
least three.  `outgoing_short_child_cases` gives the no-short versus unique-
short dichotomy, and `atMostOne_short_outgoing_child` rules out two short
children globally.

Generic reindexing theorems show that ordinary rows can be permuted arbitrarily
and designated rows can permute remaining ports while fixing grey at the
chosen short slot without changing the exposure multiset.

## 9. Long-helix transfer

`longHelixTransfer` is universal for `h >= 3`, arbitrary entry and target
residues, and every admissible fixed first color.  For a non-grey first color
it constructs either the constant word or a word with one grey at position two
or three, proves that the two exits are opposite, and proves the grey placement
and non-grey opposite-residue closing condition.  For a grey first color it
uses `G^h` or `G^(h-1)B` (black is the deterministic non-grey choice).

`HelixWordInstalled` identifies a local result with the actual restriction of
a global coloring to a real maximal helix.  The bridge proves equality with
global `pairedLevel` parity at every offset and at the terminal, transfers the
grey invariant, and derives internal local properness from global properness.

## 10. Complete two-pair bridge

`validTwoPairFinset_eq_table` proves equality between the finite set of all
valid pairs and the exact four-row table:

| transition | pairs |
|---|---|
| `xi -> xi` | `BB`, `WW` |
| `xi -> eta` | `BG`, `WG` |
| `eta -> xi` | `GB`, `GW` |
| `eta -> eta` | `BB`, `WW`, `GG` |

The proof exhausts all nine color pairs in Lean.  Consequences force grey first
for `eta -> xi`, grey second for `xi -> eta`, and `GG` for a Safe
`eta -> eta` transition.  The installed global theorem proves that a Safe
length-two helix terminating at an M endpoint closes grey.

## 11. Exact `Safe` definition

```lean
def Safe (h : Nat) (entry eta : Parity) (first : Color) : Prop :=
  first.AdmissibleAt entry eta ∧
    (h = 2 ∧ entry = eta → first = Color.grey)
```

The second clause is a deliberately stronger construction choice.  The exact
table proves it necessary for an `eta -> xi` transition, unnecessary for every
`eta -> eta` transition because `BB` and `WW` are valid, and sufficient there
because it selects `GG`.  Root and loop allocation safety theorems prove the
unique short helix can consume the one required designated grey port.

## 12. Kernel-checked examples

`RNA/Milestone2Examples.lean` checks:

- inverse/delta/parity facts for all colors;
- proper and improper exposed multisets;
- improper BW/WB and proper BB/BG/GB/GG adjacencies;
- strong separation implies ordinary separation;
- an actual no-grey coloring where ordinary separation is vacuous but strong
  separation fails because unpaired levels have mixed parity;
- E, L-zero, L-one, M-two, and M-three actual endpoint shapes;
- all four executable root port rows;
- all six ordinary and all six designated M rows;
- the exact tight `{G,G,B}` row;
- all four accepted two-pair transitions and a rejected pair for each;
- exact finite-set table rows;
- universal transfer instantiated at lengths three and four;
- canonical maximal-helix lookup for an actual target arc;
- extraction of the unique short helix from `(())`;
- actual root and E-loop allocation witnesses on `(())`.

These examples exercise definitions; the universal theorems do not depend on
the examples.

## 13. Commands used

Baseline and validation commands included:

```bash
git status --short
git log -1 --oneline
lake clean
lake build
lake build RNA.HelixPartition
lake build RNA.Endpoint RNA.LocalAllocations
lake build RNA.Color RNA.HelixTransfer RNA.HelixTransferBridge
lake build RNA.Milestone2AxiomAudit
git diff --check
rg -n -w 'sorry|admit|axiom|unsafe' RNA.lean RNA --glob '*.lean'
shasum -a 256 docs/CANONICAL_PROOF.md
zip -r -X milestone_2_review_source.zip README.md lean-toolchain lakefile.toml lake-manifest.json RNA.lean RNA docs \
  -x '*.olean' '*.ilean' '.lake/*' '.git/*' '*/__pycache__/*' \
     '*/.DS_Store' '*/.idea/*' '*/.vscode/*' '*~'
unzip -l milestone_2_review_source.zip
```

The final validation performs a clean rebuild before committing.

### Forbidden-token occurrence explanation

The Lean-source scan has no matches.  The documentation scan has nine matches,
all non-code audit language:

- `MILESTONE_2_REPORT.md`: one occurrence is the quoted search command above.
- `MILESTONE_2_AXIOM_AUDIT.md`: the heading names the audit; two prose
  occurrences state that there is no project-defined dependency and that
  noncomputable choice adds none; one occurrence is the quoted search command.
- `AXIOM_AUDIT.md`: two prose occurrences state the Milestone 1 audit result;
  one occurrence is its quoted search command.
- `MILESTONE_1_REPORT.md`: one prose occurrence explains that the final
  proposition is a definition rather than an assumed result.

Thus none is a placeholder, declaration, proof escape, or untrusted definition.

## 14. Unresolved blockers

None.  No theorem was weakened and no Milestone 1 public scientific definition
was changed.  Therefore `docs/MILESTONE_2_BLOCKERS.md` was not created.

## 15. Deferred to Milestone 3 and later

Milestone 2 deliberately does not implement:

- the global recursive coloring theorem;
- the color-to-nucleotide sequence construction;
- adjacent cancellation or free groups;
- saturated uniqueness;
- prefix balance;
- the no-tie theorem;
- the final one-short-helix designability theorem.

The recommended next implementation is an existence theorem by well-founded
structural induction on paired-node count in a helix subtree, as described in
`MILESTONE_2_DESIGN_DECISIONS.md`.
