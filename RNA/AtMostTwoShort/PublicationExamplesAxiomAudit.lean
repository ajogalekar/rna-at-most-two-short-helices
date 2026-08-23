module

public import RNA.AtMostTwoShort.PublicationExamples

@[expose] public section

set_option autoImplicit false

/-!
# Kernel dependency audit for the publication examples

This module is built explicitly.  It prints the types and transitive kernel
dependencies of the semantic endpoints without adding an import edge to the
final theorem module.
-/

namespace RNA.PublicationExamples

/-! ## Positive targets and literal words -/

#check t1Target_inTargetClassKLeTwo
#print axioms t1Target_inTargetClassKLeTwo

#check t1Target_pairCount
#print axioms t1Target_pairCount

#check t1Coloring_proper
#print axioms t1Coloring_proper

#check t1Coloring_strongTwoSeparated
#print axioms t1Coloring_strongTwoSeparated

#check t1AssignedSequence_eq_w1
#print axioms t1AssignedSequence_eq_w1

#check w1_uniqueDesigns_t1Target
#print w1_uniqueDesigns_t1Target
#print axioms w1_uniqueDesigns_t1Target

#check t2Target_inTargetClassKLeTwo
#print axioms t2Target_inTargetClassKLeTwo

#check t2Target_pairCount
#print axioms t2Target_pairCount

#check t2Coloring_proper
#print axioms t2Coloring_proper

#check t2Coloring_strongTwoSeparated
#print axioms t2Coloring_strongTwoSeparated

#check t2Coloring_strongTwoSeparatedWith_zero
#print axioms t2Coloring_strongTwoSeparatedWith_zero

#check t2AssignedSequence_eq_w2
#print axioms t2AssignedSequence_eq_w2

#check w2_uniqueDesigns_t2Target
#print w2_uniqueDesigns_t2Target
#print axioms w2_uniqueDesigns_t2Target

/-! ## Negative controls -/

#check threeShortTarget_shortHelixCount
#print axioms threeShortTarget_shortHelixCount

#check threeShortTarget_not_inTargetClassKLeTwo
#print axioms threeShortTarget_not_inTargetClassKLeTwo

#check threeShortTarget_no_proper_modTwoSeparated
#print axioms threeShortTarget_no_proper_modTwoSeparated

#check lengthOneHelixTarget_not_inTargetClassKLeTwo
#print axioms lengthOneHelixTarget_not_inTargetClassKLeTwo

#check auau_not_uniqueDesigns_nested
#print axioms auau_not_uniqueDesigns_nested

end RNA.PublicationExamples
