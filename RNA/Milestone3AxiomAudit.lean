module

public import RNA.GlobalColoring

@[expose] public section

set_option autoImplicit false

/-!
# Milestone 3 kernel dependency audit

This module asks Lean's kernel to report the transitive axioms used by the
load-bearing Milestone 3 construction.  The corresponding human-readable
record is `docs/MILESTONE_3_AXIOM_AUDIT.md`.
-/

namespace RNA

#print axioms pairedHelixSubtree_decomposition
#print axioms rootPairedHelixSubtreeUnion_eq_univ
#print axioms helixSubtreePairCount_outgoing_lt

#print axioms twoPairTransferOfSafe
#print axioms transferForClassKHelix

#print axioms assembleSubtreeColoring
#print axioms constructSubtree
#print axioms exists_subtreeColoring

#print axioms rootForestAssembly
#print axioms globalColoringCertificate
#print axioms targetClass_admits_proper_strongTwoSeparated

end RNA
