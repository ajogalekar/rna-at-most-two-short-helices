# Milestone 3 report: global proper strong-2-separated coloring

## 1. Base and final commits

- Milestone 2 base commit:
  `bf6a7cefbe34c1d7dc44b21dd8bb031b9c66e68b`
  (`bf6a7ce Document Milestone 2 validation and handoff`).
- Milestone 3 final implementation commit:
  `1db9e27d4bce6cf1f3a62ff0004083f041e83615`
  (`1db9e27 Formalize Milestone 3 global coloring`).
- Working branch: `milestone-3-global-coloring`.

This report is added by the immediate documentation-only follow-up commit so
that it can record the already-fixed implementation hash. No Lean source is
changed after the implementation commit.

The base hash is also recorded verbatim in
`docs/MILESTONE_3_BASE_COMMIT.txt`. The pre-existing Milestone 2 source archive
was moved without modification to
`/Users/ashujo/Documents/Science/milestone_2_review_source.zip`; its SHA-256 is
`30883d6fff310f1a6f707f7cbb9703aa9f301bfabc6a843a08370a07db964576`.

## 2. Files and declarations added

The main handwritten additions are:

- `RNA/Milestone3Local.lean`: `twoPairTransferOfSafe`,
  `transferForClassKHelix`, the closing-color API, installed-word exposure
  bridges, and actual-allocation exposure bridges;
- `RNA/HelixSubtree.lean`: paired and unpaired helix subtrees, their
  decompositions and disjointness results, the root partition, and the
  recursion measure;
- `RNA/SubtreeColoring.lean`: exact-domain partial assignments, extension,
  disjoint family flattening, local-word installation, subtree assembly, and
  root totalization;
- `RNA/SubtreeConstruction.lean`: `SubtreePostcondition`,
  `SubtreeCertificate`, `constructSubtree`, and
  `exists_subtreeColoring`;
- `RNA/GlobalColoring.lean`: root-forest construction,
  `GlobalColoringCertificate`, the two witness-bearing existence theorems,
  and the exact Theorem 12 declaration;
- `RNA/Milestone3Examples.lean`: five explicit class-K targets and checked
  construction facts;
- `RNA/Milestone3AxiomAudit.lean`: kernel dependency queries for all
  load-bearing declarations.

The milestone documentation consists of
`MILESTONE_3_BASE_COMMIT.txt`, `MILESTONE_3_ASSEMBLY_DESIGN.md`, this report,
and `MILESTONE_3_AXIOM_AUDIT.md`, together with narrow updates to the
formalization blueprint and model-fidelity audit.

## 3. Chosen subtree and assembly representation

The implementation combines the two representations compared in the design
document. A `SubtreeColoring H` is a proof-bearing assignment whose domain is
exactly `pairedHelixSubtree T H`. A `SubtreeCertificate` stores the selected
endpoint, local transfer, loop allocation, and an extension-stable correctness
theorem; that soundness proof is built recursively from the certificates of
the actual children. `assembleSubtreeColoring` flattens the local word and
pairwise-disjoint child assignments into the exact parent domain.

`ExtendsSubtree chi sigma` makes every postcondition quantify over any total
coloring agreeing with `sigma`. Consequently, no subtree proof can depend on
arbitrary colors outside its domain. Disjoint-union and unique-owner lemmas,
not an update-order convention, ensure that sibling assignments cannot
overwrite one another.

## 4. Exact well-founded measure

The recursion measure is

```lean
helixSubtreePairCount T H = (pairedHelixSubtree T H).card
```

`pairedHelixSubtree_outgoing_ssubset` proves that every actual outgoing child
helix has a strict paired-subtree inclusion. The theorem
`helixSubtreePairCount_outgoing_lt` converts this into the strict natural-number
decrease used in the `termination_by` proof for `constructSubtree`.

## 5. Subtree partition and disjointness results

`HelixSubtree.lean` proves, among other facts:

- `helixMemberNodes_subset_pairedHelixSubtree`;
- `pairedHelixSubtree_outgoing_subset` and
  `pairedHelixSubtree_outgoing_ssubset`;
- `pairedHelixSubtree_outgoing_disjoint` and
  `unpairedHelixSubtree_outgoing_disjoint`;
- `helixMemberNodes_disjoint_outgoing`;
- `pairedHelixSubtree_decomposition` and
  `unpairedHelixSubtree_decomposition`;
- `pairedHelixSubtree_root_disjoint` and
  `unpairedHelixSubtree_root_disjoint`;
- `rootPairedHelixSubtreeUnion_eq_univ`;
- `mem_root_unpairedChildren_iff_not_mem_rootSubtree` and
  `root_unpairedChildren_eq_compl_rootSubtrees`.

Together these show exact ownership at every recursive node, complete coverage
of all target pairs by the root forest, and the required complement statement
for root-unpaired positions.

## 6. Length-two transfer constructor

`twoPairTransferOfSafe` constructs the short-helix `LocalTransfer` directly
from `Safe 2 entry eta first`. Its deterministic policy is:

- xi to xi: `[first, first]`;
- xi to eta: `[first, grey]`;
- eta to xi: `[grey, black]`;
- eta to eta: `[grey, grey]`.

The constructor proves the word length, fixed first color, internal
properness, gray placement, requested exit, and a non-gray closing color for
an xi exit. The deterministic use of black in the eta-to-xi row is proved
valid rather than assumed.

## 7. Unified class-K helix transfer

`transferForClassKHelix` dispatches on the actual maximal-helix length. For
the unique length-two helix it uses `twoPairTransferOfSafe`; every other helix
is proved to have length at least three and uses the existing
`longHelixTransfer_of_safe`. The impossible length-one case is discharged by
the class-K hypothesis.

`LocalTransfer.closingColor`, its last-element theorem, and
`installedLocalTransfer_terminalColor_eq_closingColor` expose the resulting
terminal color to loop allocation and recursive assembly.

## 8. Construction-direction properness bridges

The reverse-direction bridges needed by construction are:

- `properExposure_internalHelix_of_installed`,
  `installedLocalTransfer_internalExposure`, and
  `properExposure_nonterminalHelixMember_of_installed`, which derive actual
  nonterminal exposure properness from an installed internally proper word;
- `LoopAllocation.properActualExposure`, which identifies actual child-head
  colors with the selected loop ports and proves terminal exposure proper;
- `RootAllocation.properActualExposure`, which proves virtual-root exposure
  proper from the actual root ports;
- installed-transfer level lemmas, used to prove the requested terminal
  residue, all gray placements, and the L-terminal non-gray condition.

None of these theorems assumes a future global `ProperColoring` premise.

## 9. Subtree recursive theorem

`constructSubtree` performs well-founded recursion on the exact measure above.
At each step it classifies the terminal endpoint, requests exit xi for E/L and
eta for M, constructs the local transfer, chooses the proved loop allocation,
recurses at every actual outgoing slot using `safeOutgoing`, and assembles the
local and child assignments.

Its `SubtreePostcondition` proves the indexed head color, real-word
installation, proper exposure for every subtree pair, gray residue eta,
unpaired residue xi, exact child ports, endpoint-specific terminal residue,
and the non-gray L close. `exists_subtreeColoring` packages the resulting
exact-domain assignment with a nonempty certificate. The contract is stable
under every total extension having the required entry residue.

## 10. Root assembly

`constructedRootSubtreeColorings` recursively constructs every actual
root-child component. `coloringOfRootSubtrees` flattens their pairwise-disjoint
domains, and `rootPairedHelixSubtreeUnion_eq_univ` turns the result into a
total `Coloring T`.

`assembledRootColoring_proper` handles the virtual root using the actual
`RootAllocation` and handles every paired node through its unique subtree
certificate. `assembledRootColoring_strongTwoSeparatedWith` combines subtree
gray/unpaired facts with the separate root-unpaired argument: root-unpaired
positions have integer level zero, and root allocation coverage forces an xi
row, whose selected xi is zero. `rootForestAssembly` packages the proper and
strong-with-residue statements.

`globalColoringCertificate` retains the chosen allocation, its row-coverage
facts, the total coloring, properness, and `StrongTwoSeparatedWith` evidence
for later constructive milestones.

## 11. Exact final coloring theorem

The witness-bearing theorem is:

```lean
theorem exists_proper_strongTwoSeparatedWith
    (hK : InTargetClassK T) :
    ∃ xi, ∃ chi : Coloring T,
      ProperColoring chi ∧ StrongTwoSeparatedWith chi xi
```

`exists_proper_strongTwoSeparated` forgets only the named residue, using the
same witness. The exact manuscript result is:

```lean
theorem targetClass_admits_proper_strongTwoSeparated
    (hK : InTargetClassK T) :
    ∃ chi : Coloring T,
      ProperColoring chi ∧ StrongTwoSeparated chi
```

This is Theorem 12 of `docs/CANONICAL_PROOF.md`. It is not connected to
`UniqueDesigns` in this milestone.

## 12. Examples proved

`Milestone3Examples.lean` contains the five requested finite targets:

1. `(())`, with its class-K proof and an explicitly checked valid length-two
   bridge;
2. `.(())`, with a root-unpaired position, an xi root row, exact level zero,
   and residue equality to xi;
3. `(())((()))((()))`, with class-K membership, an eta root row, and gray at
   the unique short root child;
4. `(((((.))((())))))`, with an internal M terminal, its length-two L child,
   the gray port assigned to that short child, the short head checked gray in
   the constructed global coloring, and the concrete gray-to-black short
   transfer;
5. a 29-position target with two levels of M branching, E and L endpoints,
   and the unique short helix below the inner M node.

All shape, allocation, transfer, and class-K assertions are kernel checked.
The global properness and strong-two-separation checks for these targets are
instances of `globalColoringCertificate` and the universal final theorem, not
premises of that theorem.

## 13. Axiom results

`lake build RNA.Milestone3AxiomAudit` succeeds. Every audited declaration,
including `constructSubtree`, `rootForestAssembly`,
`globalColoringCertificate`, and the final theorem, reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are accepted standard Lean/Mathlib principles. No project-defined
axiom, admission, external computation, or unsafe mathematical construction
appears. See `docs/MILESTONE_3_AXIOM_AUDIT.md` for the full declaration list.

The requested whole-source scan was:

```text
rg -n -w 'sorry|admit|axiom|unsafe' RNA.lean RNA --glob '*.lean'
```

It returns no matches. Extending the scan to `docs/` finds only explanatory
audit/report prose and copies of this search command in the Milestone 1–3
documentation. Thus there is no `sorry`, `admit`, custom `axiom`, or
mathematical use of `unsafe` in handwritten Lean source.

## 14. Unresolved blockers

There are no mathematical or representation blockers. The recursive assembly
constructs a total coloring and proves the exact global properties required by
the frozen manuscript.

## 15. Work deferred to Milestone 4

This milestone deliberately stops at Theorem 12. It does not assign A/C/G/U
letters from the coloring, prove local nucleotide distinctness, establish the
pairing-inventory bound, formalize cancellation or free groups, prove
saturated-skeleton uniqueness, develop prefix balance, prove the no-tie
theorem, or prove `OneShortHelixDesignabilityStatement`. Those tasks remain
for Milestone 4 and later milestones.
