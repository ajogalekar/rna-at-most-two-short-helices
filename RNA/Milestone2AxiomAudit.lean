module

public import RNA.HelixTransferBridge
public import RNA.LocalAllocations

set_option autoImplicit false

/-!
# Reproducible Milestone 2 dependency audit

This module is intentionally not imported by `RNA.lean`; build it explicitly
to print the kernel dependencies of the load-bearing local-colouring results.
-/

#print axioms RNA.exists_maximalHelix_containing
#print axioms RNA.existsUnique_maximalHelix_containing
#print axioms RNA.biUnion_maximalHelices_members
#print axioms RNA.disjoint_helixMembers_of_ne
#print axioms RNA.stacked_iff_unique_pairedChild_no_unpaired
#print axioms RNA.MaximalHelix.existsUnique_outgoing_of_terminal_child
#print axioms RNA.shortHelix_length
#print axioms RNA.strongTwoSeparated_implies_separated
#print axioms RNA.existsUnique_endpointType_of_loopNode
#print axioms RNA.nonroot_parentOfHead_classification
#print axioms RNA.endpoint_forcedResidues
#print axioms RNA.forcedResidues_of_proper_strongTwoSeparated
#print axioms RNA.completeRootAllocationCoverage
#print axioms RNA.exists_completeRootAllocationCoverage
#print axioms RNA.exists_completeLoopAllocationCoverage
#print axioms RNA.completeNonrootAllocationCoverage
#print axioms RNA.atMostOne_short_outgoing_child
#print axioms RNA.exists_longHelixTransfer
#print axioms RNA.validTwoPair_iff_mem_table
#print axioms RNA.validTwoPairFinset_eq_table
#print axioms RNA.safe_twoPair_target_eta_second_grey
#print axioms RNA.helixRunningResidue_eq_levelParity_pairedLevel
#print axioms RNA.installedLocalTransfer_pointwise
#print axioms RNA.installedLocalTransfer_terminalLevel
#print axioms RNA.installedLocalTransfer_globalGreysAt
#print axioms RNA.internallyProper_helixColorWord
#print axioms RNA.safe_installed_twoPair_mEndpoint_closes_grey
