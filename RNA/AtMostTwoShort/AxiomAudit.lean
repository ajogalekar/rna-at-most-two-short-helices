module

public import RNA.AtMostTwoShort.Designability
public import RNA.AtMostTwoShort.Examples

@[expose] public section

set_option autoImplicit false

/-!
# Kernel dependency audit for the at-most-two theorem

This module is built explicitly.  It asks Lean to display the types and
transitive kernel dependencies of every load-bearing layer, culminating in the
exact public proposition and theorem.
-/

namespace RNA

/-! ## Exact public definitions -/

#check shortHelixCount
#print shortHelixCount

#check InTargetClassKLeTwo
#print InTargetClassKLeTwo

#check InTargetClassK2
#print InTargetClassK2

#check UniqueDesigns
#print UniqueDesigns

/-! ## Short-resource accounting -/

#check shortHelixSubtreeCount_decomposition
#print axioms shortHelixSubtreeCount_decomposition

#check loopShortSupport_card_le_two
#print axioms loopShortSupport_card_le_two

#check rootShortSupport_card_le_two
#print axioms rootShortSupport_card_le_two

#check loopShortSupport_card_eq_two_length_at_least_three
#print axioms loopShortSupport_card_eq_two_length_at_least_three

/-! ## Strengthened transfer and actual allocation -/

#check longTransfer_eta_closesNonGrey_of_Q
#print axioms longTransfer_eta_closesNonGrey_of_Q

#check completeResourceLoopAllocation
#print axioms completeResourceLoopAllocation

#check onePositiveMActualExposure_eq
#print axioms onePositiveMActualExposure_eq

#check completeResourceLoopAllocation_twoSupportActualFacts
#print axioms completeResourceLoopAllocation_twoSupportActualFacts

#check completeResourceRootAllocation
#print axioms completeResourceRootAllocation

#check completeResourceRootAllocation_twoSupport_certificate
#print axioms completeResourceRootAllocation_twoSupport_certificate

/-! ## Recursive and global constructions -/

#check constructResourceSubtree
#print axioms constructResourceSubtree

#check constructResourceSubtree_resourceInvariant
#print axioms constructResourceSubtree_resourceInvariant

#check globalColoringCertificateLeTwo
#print axioms globalColoringCertificateLeTwo

#check exists_proper_strongTwoSeparatedWith_leTwo
#print axioms exists_proper_strongTwoSeparatedWith_leTwo

#check targetClassLeTwo_admits_proper_strongTwoSeparated
#print axioms targetClassLeTwo_admits_proper_strongTwoSeparated

/-! ## Unique designability -/

#check atMostTwoShortHelices_uniqueDesigns
#print axioms atMostTwoShortHelices_uniqueDesigns

#check AtMostTwoShortHelixDesignabilityStatement
#print AtMostTwoShortHelixDesignabilityStatement

#check atMostTwoShortHelixDesignability
#print atMostTwoShortHelixDesignability
#print axioms atMostTwoShortHelixDesignability

end RNA
