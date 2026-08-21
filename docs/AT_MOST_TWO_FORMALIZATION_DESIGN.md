# At-most-two formalization design

This downstream development is additive. Existing model declarations and the
completed exact-one theorem remain unchanged.

## Module boundary

- `TargetClass`: global length-two helix set/count and exact class predicates.
- `ShortCount`: subtree resource count, exact decomposition, and support bounds.
- `Interface`: F/Q predicates and resource requirements.
- `Transfers`: allowed-length dispatch and strengthened eta/non-gray close.
- `ResourceCertificate`: parallel exact-domain extension-stable certificate.
- `ResourceAllocations`: actual E/L/M child-slot allocations for r=0,1,2.
- `ResourceRoot`: degree-zero and actual root allocations.
- `SubtreeConstruction`: well-founded resource induction.
- `GlobalColoring`: root forest, total coloring, and strong separation.
- `Designability`: generic no-tie bridge and final theorem.
- `Examples`: positive and negative kernel-checked controls.
- `AxiomAudit`: transitive axiom output for load-bearing declarations.

## Reuse policy

Generic declarations in `HelixSubtree`, `SubtreeColoring`, `HelixTransfer`, and
the installed local/global bridges are reused. Types indexed by
`InTargetClassK` (`SubtreeCertificate`, `LoopAllocation`, `RootAllocation`, and
`GlobalColoringCertificate`) are not weakened; parallel resource-aware types
are introduced. The final theorem depends directly on the new resource
construction and on the old generic coloring-to-design theorem only.

## Proof discipline

All domains and ports refer to actual finite child slots. Resource counts are
proved from the maximal-helix/subtree partition. The well-founded measure is
the existing exact subtree pair count. Gluing retains extension stability and
proves disjointness, port preservation, path-local levels, and complete node
coverage. Ordinary kernel-checked case analysis and `decide` may discharge
small concrete color identities; no enumeration or external executable is a
mathematical premise.

The reference documents in `docs/track_b_reference` are copied evidence only.
Their hashes lock the prose inputs, while this canonical specification records
the corrections governing the Lean implementation.
