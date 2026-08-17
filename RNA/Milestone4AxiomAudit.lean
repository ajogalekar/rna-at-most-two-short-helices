module

public import RNA.GlobalSequence

@[expose] public section

set_option autoImplicit false

/-!
# Milestone 4 kernel dependency audit

This module asks Lean's kernel to report the transitive axioms used by the
load-bearing Milestone 4 sequence, inventory, balance, and obstruction
declarations.  The corresponding human-readable record is
`docs/MILESTONE_4_AXIOM_AUDIT.md`.
-/

namespace RNA

#print axioms leftLetterOfColoring
#print axioms sequenceOfProperColoring
#print axioms structureCompatible_sequenceOfProperColoring
#print axioms locallyDistinct_sequenceOfProperColoring

#print axioms nucleotideCount_U_sequenceOfProperColoring
#print axioms nucleotideCount_G_sequenceOfProperColoring
#print axioms nucleotideCount_C_sequenceOfProperColoring
#print axioms nucleotideCount_A_sequenceOfProperColoring
#print axioms pairCount_le_nucleotideCount_U_add_C
#print axioms pairCount_le_sequenceOfProperColoring
#print axioms equality_uses_all_limiting_nucleotides

#print axioms completeSubtreeBalance
#print axioms prefixBalanceAt_pairedLeft_eq_pairedLevel
#print axioms prefixBalanceAt_unpaired_eq_unpairedLevel
#print axioms prefixBalanceAt_greyRight_eq

#print axioms positionPartner_strictlyInside_of_enclosing_arc
#print axioms interior_G_count_eq_C_count_of_all_paired
#print axioms levelImbalance_obstruction
#print axioms targetUnpaired_pairing_obstruction

#print axioms globalSequenceCertificate
#print axioms targetClass_has_maximumPairSequence

end RNA
