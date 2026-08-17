module

public import RNA.OneShortHelixDesignability

@[expose] public section

set_option autoImplicit false

/-!
# Final kernel dependency audit

This module asks Lean to display the types and transitive axiom dependencies
of the load-bearing Milestone 5 declarations.  In particular, the final
public theorem is checked, printed in full, and audited directly.
-/

namespace RNA

/-! ## Adjacent cancellation and suffix cancellation -/

#check saturable_iff_reducesToEmpty
#print axioms saturable_iff_reducesToEmpty

#check suffix_saturable_of_concat_saturable_of_prefix_saturable
#print axioms suffix_saturable_of_concat_saturable_of_prefix_saturable

/-! ## Atomic words and atomic designs -/

#check atomic_iff_every_saturated_hasOuterPair
#print axioms atomic_iff_every_saturated_hasOuterPair

#check AtomicDesignBlock.concat_atomicDesigns
#print axioms AtomicDesignBlock.concat_atomicDesigns

#check AtomicDesignBlock.wrap_atomicDesigns
#print axioms AtomicDesignBlock.wrap_atomicDesigns

/-! ## Saturated uniqueness -/

#check saturated_unique_of_localDistinctness
#print axioms saturated_unique_of_localDistinctness

/-! ## Tied competitors and paired-skeleton restriction -/

#check unpairedPositionSet_eq_of_tied
#print axioms unpairedPositionSet_eq_of_tied

-- Exact arc membership and pair-count preservation.
#check mem_pairedRestriction_iff_liftPairedArc_mem
#print axioms mem_pairedRestriction_iff_liftPairedArc_mem

#check pairCount_pairedRestriction
#print axioms pairCount_pairedRestriction

-- The two concrete saturated restrictions used by the no-tie theorem.
#check saturatedStructure_targetPairedRestriction
#print axioms saturatedStructure_targetPairedRestriction

#check saturatedStructure_competitorPairedRestriction
#print axioms saturatedStructure_competitorPairedRestriction

-- Compatibility and interval-tree parent preservation under compression.
#check structureCompatible_pairedRestriction
#print axioms structureCompatible_pairedRestriction

#check parent_pairedRestriction
#print axioms parent_pairedRestriction

#check locallyDistinct_targetPairedRestriction
#print axioms locallyDistinct_targetPairedRestriction

#check eq_target_of_competitorPairedRestriction_eq
#print axioms eq_target_of_competitorPairedRestriction_eq

/-! ## General no-tie and unique-designability theorems -/

#check noTie_sequenceOfProperSeparatedColoring
#print axioms noTie_sequenceOfProperSeparatedColoring

#check eq_target_of_tied_pairCount
#print axioms eq_target_of_tied_pairCount

#check uniqueDesigns_sequenceOfProperSeparatedColoring
#print axioms uniqueDesigns_sequenceOfProperSeparatedColoring

/-! ## Final class-K result -/

#check oneShortHelix_uniqueDesigns
#print axioms oneShortHelix_uniqueDesigns

#check oneShortHelixDesignability
#print oneShortHelixDesignability
#print axioms oneShortHelixDesignability

end RNA
