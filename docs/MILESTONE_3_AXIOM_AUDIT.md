# Milestone 3 axiom audit

## Method

`RNA/Milestone3AxiomAudit.lean` imports the completed global construction and
runs `#print axioms` on the load-bearing declarations for subtree geometry,
local transfer, exact-domain assembly, well-founded recursion, root assembly,
and the final theorem.

The checked declarations are:

- `pairedHelixSubtree_decomposition`;
- `rootPairedHelixSubtreeUnion_eq_univ`;
- `helixSubtreePairCount_outgoing_lt`;
- `twoPairTransferOfSafe`;
- `transferForClassKHelix`;
- `assembleSubtreeColoring`;
- `constructSubtree`;
- `exists_subtreeColoring`;
- `rootForestAssembly`;
- `globalColoringCertificate`;
- `targetClass_admits_proper_strongTwoSeparated`.

The audit was compiled with:

```text
lake build RNA.Milestone3AxiomAudit
```

The build completed successfully. Lean reported the same transitive axiom set
for every declaration:

```text
[propext, Classical.choice, Quot.sound]
```

## Interpretation

These are ordinary Lean/Mathlib foundations used by finite sets, quotients,
subtypes, and the selection of witnesses already supplied by proved
existence theorems:

- `propext` is propositional extensionality;
- `Classical.choice` selects endpoint classifications, allocation witnesses,
  unique owners in finite disjoint unions, and the recursively constructed
  objects whose existence has been proved;
- `Quot.sound` is the standard quotient soundness principle used transitively
  by library data structures.

No project-defined axiom, admitted theorem, external-computation oracle, or
`unsafe` mathematical witness occurs in the audited dependency chains.
Well-founded recursion in `constructSubtree` is kernel checked using
`helixSubtreePairCount_outgoing_lt`; it is not an additional axiom.

## Result

The Milestone 3 construction satisfies the requested axiom policy. Its final
proper strong-2-separated coloring theorem depends only on the three accepted
standard principles above.
