# Milestone 2 axiom audit

The reproducible audit module is `RNA/Milestone2AxiomAudit.lean`.  It was run
from the project root with:

```bash
lake build RNA.Milestone2AxiomAudit
```

## Results

Every audited declaration reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Those are Lean/Mathlib's ordinary foundational principles.  No
project-defined axiom or admitted result occurs in the dependency closure.

The declarations audited are:

- maximal-helix coverage and partition:
  `exists_maximalHelix_containing`,
  `existsUnique_maximalHelix_containing`,
  `biUnion_maximalHelices_members`,
  `disjoint_helixMembers_of_ne`;
- helix/tree structure:
  `stacked_iff_unique_pairedChild_no_unpaired`,
  `MaximalHelix.existsUnique_outgoing_of_terminal_child`,
  `shortHelix_length`;
- coloring and endpoints:
  `strongTwoSeparated_implies_separated`,
  `existsUnique_endpointType_of_loopNode`,
  `nonroot_parentOfHead_classification`,
  `endpoint_forcedResidues`,
  `forcedResidues_of_proper_strongTwoSeparated`;
- actual allocation coverage:
  `completeRootAllocationCoverage`,
  `exists_completeRootAllocationCoverage`,
  `exists_completeLoopAllocationCoverage`,
  `completeNonrootAllocationCoverage`,
  `atMostOne_short_outgoing_child`;
- local transfer and the complete short bridge:
  `exists_longHelixTransfer`,
  `validTwoPair_iff_mem_table`,
  `validTwoPairFinset_eq_table`,
  `safe_twoPair_target_eta_second_grey`;
- global/local transfer:
  `helixRunningResidue_eq_levelParity_pairedLevel`,
  `installedLocalTransfer_pointwise`,
  `installedLocalTransfer_terminalLevel`,
  `installedLocalTransfer_globalGreysAt`,
  `internallyProper_helixColorWord`,
  `safe_installed_twoPair_mEndpoint_closes_grey`.

## Proof mechanisms

Finite color, residue, exposure, and two-pair cases use Lean tactics such as
`decide`, `fin_cases`, and constructor case analysis.  The resulting proof
terms are checked by the Lean kernel.  No native-code proof oracle or external
computation is used.

Noncomputable choices select objects already proved unique: a maximal helix
containing an arc, an outgoing helix at an actual child, the class-K short
helix, or a finite child index.  Their correctness is carried by proof fields
and uniqueness theorems; noncomputability does not add an axiom.

## Source scan

The final audit also runs:

```bash
rg -n -w 'sorry|admit|axiom|unsafe' RNA.lean RNA --glob '*.lean'
```

The expected result is no output.  Documentation occurrences are quoted audit
terms or prose and are enumerated in the Milestone 2 report.
