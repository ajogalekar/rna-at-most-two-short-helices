module

public import RNA.Examples

@[expose] public section

set_option autoImplicit false

/-!
# Reproducible foundational-dependency audit commands

Run `lake build +RNA.AxiomAudit` and copy the reported dependencies into
`docs/AXIOM_AUDIT.md`.
-/

#print axioms RNA.Nucleotide.comp_comp
#print axioms RNA.Nucleotide.comp_ne_self
#print axioms RNA.compatible_symm
#print axioms RNA.energy_lt_iff_pairCount_gt
#print axioms RNA.uniqueDesigns_iff_maximum_and_unique_count
#print axioms RNA.uniqueMinimumEnergy_iff_maximum_and_unique_count
#print axioms RNA.pairedNode_laminar
#print axioms RNA.parent_pair_smallest
#print axioms RNA.parent_isParent
#print axioms RNA.isParent_unique
#print axioms RNA.parent_eq_iff_isParent
#print axioms RNA.parent_wellDefined_unique
#print axioms RNA.motifBounds
#print axioms RNA.MaximalHelix.ext_outer
#print axioms RNA.exists_maximalHelix_iff_run
#print axioms RNA.MaximalHelix.helixMembers_card
#print axioms RNA.MaximalHelix.eq_or_disjoint_members
#print axioms RNA.Examples.adjacent_pair_is_present
#print axioms RNA.Examples.crossingArcSet_cannot_be_a_secondaryStructure
#print axioms RNA.Examples.nestedTarget_in_classK
#print axioms RNA.Examples.ggcc_unique_design
#print axioms RNA.Examples.auau_not_unique_design
