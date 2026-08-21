# At-most-two-short-helices formalization report

## 1. Release status and provenance

The universal at-most-two theorem is machine checked. The implementation
directly covers global short-helix counts zero, one, and two, including the
all-unpaired target. It does not use the completed exact-one designability
theorem as a premise.

- Frozen downstream base commit:
  `c37eac40ef5a28bf5733fd576ce6d4c44091ee6a`
- Corrected proof-specification commit:
  `020fa8cd54f64c3e7264fd9dcab7ac11e6b671bc`
- Working branch: `at-most-two-short-helices`
- Canonical corrected proof:
  `docs/CANONICAL_AT_MOST_TWO_PROOF.md`
- Canonical proof SHA-256:
  `fb9bee1126791b9ca53b3903c061df27e3856dd20b9c7fc248b7acd4e5326841`
- Implementation commit:
  `b64d9165191a89e692d518c4e8cdaa9beafb61f3`
- Documentation/release commit:
  `<DOCUMENTATION_RELEASE_COMMIT_TO_FILL_AFTER_COMMIT>`
- Clean archive-source commit:
  `<ARCHIVE_SOURCE_COMMIT_TO_FILL_AFTER_COMMIT>`
- Source archive SHA-256:
  `<ARCHIVE_SHA256_TO_FILL_AFTER_ARCHIVE_CREATION>`

The implementation, documentation, and archive values are deliberately left
as placeholders because a commit or archive cannot truthfully contain a hash
that does not exist until after that object is created. The final release
handoff must replace them with the resulting values.

The exact-one model and theorem are inherited from the frozen base without
modification. `UniqueDesigns`, `SecondaryStructure`, complementarity, energy,
the interval-tree conventions, Lean, and Mathlib remain unchanged.

## 2. Exact theorem

The final public proposition is:

```lean
def AtMostTwoShortHelixDesignabilityStatement : Prop :=
  ∀ {n : Nat} (T : SecondaryStructure n),
    InTargetClassKLeTwo T →
      ∃ w : Sequence n, UniqueDesigns w T
```

and the proved declaration is:

```lean
theorem atMostTwoShortHelixDesignability :
    AtMostTwoShortHelixDesignabilityStatement
```

`UniqueDesigns w T` quantifies over every compatible
`S : SecondaryStructure n` on the same complete sequence `w` and requires the
strict inequality `pairCount S < pairCount T` whenever `S ≠ T`.
`atMostTwoShortHelices_uniqueMinimumEnergy` gives the equivalent result for
the unchanged energy `energy = -pairCount`.

## 3. Files and principal declarations added

The downstream Lean development is additive and lives under
`RNA/AtMostTwoShort/`.

- `TargetClass.lean` adds `lengthTwoHelices`, `shortHelixCount`,
  `InTargetClassKLeTwo`, `InTargetClassK2`, the zero/one/two count
  characterizations, and `inTargetClassKLeTwo_of_inTargetClassK`.
- `ShortCount.lean` adds `shortHelixSubtreeCount`,
  `shortHelixSubtreeCount_decomposition`, `loopShortSupport`,
  `rootShortSupport`, their cardinality bounds, and the two-positive-child
  long-helix result.
- `Interface.lean` adds `InF`, `InQ`, `RequiredInterface`, their exact
  interface characterizations, and `requiredInterface_safe`.
- `Transfers.lean` adds `allowedLengthTransfer`, `allowedHelixTransfer`, the
  four explicit long-word constructors, `LongEtaTransfer`, and
  `longTransfer_eta_closesNonGrey_of_Q` with installed-global bridges.
- `ResourceAllocations.lean` adds actual slot permutations,
  `ResourceLoopAllocation`, `completeResourceLoopAllocation`, and
  `completeResourceLoopAllocation_twoSupportActualFacts`.
- `ResourceRoot.lean` adds `ResourceRootAllocation`,
  `RootDegreeZeroCertificate`, `completeResourceRootAllocation`, the actual
  two-positive rows, and
  `completeResourceRootAllocation_twoSupport_certificate`.
- `ResourceCertificate.lean` adds `ResourceSubtreePostcondition`,
  `ResourceSubtreeCertificate`, `CertifiedResourceSubtree`, and
  `AcceptsInterface` without weakening the completed exact-one certificate.
- `SubtreeConstruction.lean` adds `ResourceTransferChoice`,
  `chooseResourceTransfer`, `constructResourceSubtree`, its canonical
  wrappers, and `constructResourceSubtree_resourceInvariant`.
- `GlobalColoring.lean` adds the exact root forest,
  `rootDegreeZeroColoring`, `GlobalColoringCertificateLeTwo`,
  `globalColoringCertificateLeTwo`, and
  `targetClassLeTwo_admits_proper_strongTwoSeparated`.
- `Designability.lean` adds the final unique-design theorem, exact-two,
  exact-one-from-new, all-long, all-unpaired, and energy corollaries.
- `Examples.lean` adds the requested positive construction witnesses and
  negative class controls.
- `AxiomAudit.lean` prints types and transitive kernel dependencies of every
  load-bearing layer.

`RNA.lean` imports the new modules after the completed baseline modules.

The documentation additions include the frozen corrected proof, its hash,
the formalization design, the statement audit, this report, the axiom audit,
and the Track B reference copies and checksums.

## 4. Short-count accounting

`lengthTwoHelices T` is the finite set of all maximal helices whose exact
length is two, and `shortHelixCount T` is its cardinality. The count is tied to
canonical maximal-helix descriptors and is also proved equal to the count of
their injective outer-arc representation.

For a maximal helix `H`, `shortHelixSubtreeCount T H` counts length-two
maximal helices whose heads lie in `pairedHelixSubtree T H`. The load-bearing
equation is:

```lean
theorem shortHelixSubtreeCount_decomposition (H : MaximalHelix T) :
  shortHelixSubtreeCount T H =
    (if H.length = 2 then 1 else 0) +
      ∑ i, shortHelixSubtreeCount T (outgoingHelix T H i)
```

The proof uses the existing exact helix-subtree partition and pairwise
disjoint actual outgoing child subtrees. It establishes:

- every child count is at most the parent count;
- every subtree count is at most two under `InTargetClassKLeTwo`;
- `loopShortSupport` and `rootShortSupport` have cardinality at most two; and
- `loopShortSupport_card_eq_two_length_at_least_three` forces the incoming
  helix to be long when two outgoing subtrees carry positive resource.

At the virtual root, `shortHelixCount_root_decomposition` partitions the
global count exactly among actual root-child helix subtrees. Its empty sum is
the all-unpaired base case.

## 5. Target class and relation to exact one

The target predicate is exactly:

```lean
def InTargetClassKLeTwo (T : SecondaryStructure n) : Prop :=
  shortHelixCount T ≤ 2 ∧
    (∀ H : MaximalHelix T, H.length ≠ 1) ∧
    (∀ H : MaximalHelix T, H.length ≠ 2 → 3 ≤ H.length) ∧
    ¬ HasM5 T ∧
    ¬ HasM3Dot T
```

`InTargetClassK2 T` adds `shortHelixCount T = 2`.
`shortHelixCount_eq_one_of_inTargetClassK` and
`inTargetClassKLeTwo_of_inTargetClassK` relate the completed exact-one class
to the enlarged class. That inclusion is used only downstream to prove
`oneShortHelixDesignability_from_atMostTwo`; the new universal theorem does
not appeal to `oneShortHelixDesignability`.

## 6. F/Q interface resources

For the selected unpaired residue `xi` and gray residue `xi.opposite`:

```lean
def InF (xi entry : Parity) (first : Color) : Prop :=
  first.AdmissibleAt entry xi.opposite

def InQ (xi entry : Parity) (first : Color) : Prop :=
  (entry = xi ∧ first.NonGrey) ∨
    (entry = xi.opposite ∧ first = Color.grey)
```

Thus F is exactly `{xi-B, xi-W, eta-B, eta-W, eta-G}` and Q is exactly
`{xi-B, xi-W, eta-G}`. `inQ_implies_inF` is proved, as are both residues'
complete characterizations. `RequiredInterface T H xi entry first` selects F
when `shortHelixSubtreeCount T H = 0` and Q otherwise.

`requiredInterface_safe` discharges the local transfer precondition. The
short-free branch is long and therefore accepts F; the positive branch uses
Q, which is safe even when the current helix has length two.

## 7. Strengthened long transfer

`longTransfer_eta_closesNonGrey_of_Q` constructs an eta-exiting long transfer
that preserves the requested first color, has a non-gray close, is internally
proper, and puts every gray at eta. It is proved from the four explicit words
required by the corrected specification:

- xi entry, non-gray first, odd length: `a^h`;
- xi entry, non-gray first, even length: `a G a^(h-2)`;
- eta entry, gray first, odd length: `G a^(h-1)`;
- eta entry, gray first, even length: `G G a^(h-2)`.

The definitions `xiOddEtaTransfer`, `xiEvenEtaTransfer`,
`etaGreyOddEtaTransfer`, and `etaGreyEvenEtaTransfer` handle these cases
directly, including lengths three and four. The concrete checks are
`gbbTransfer`, `gwwTransfer`, `etaEvenFourTransfer`,
`xiOddThreeTransfer`, and `xiEvenFourTransfer`.

No theorem claims that the full length-four transition relation equals a
stabilized larger-even relation.

## 8. Resource-aware loop allocations

`ResourceLoopAllocation` assigns colors to actual ordered child slots and
retains properness, each child's `RequiredInterface`, support information, and
the special two-demand close/length facts. `completeResourceLoopAllocation`
handles E, L, and M endpoints.

At an M endpoint, it splits on
`(loopShortSupport T H).card = 0, 1, 2`:

- `r = 0` installs the ordinary rows from the completed allocation layer;
- `r = 1` moves a gray port to the unique positive-short actual slot; and
- `r = 2` uses `twoSlotPerm` to send the two distinct positive actual slots to
  two displayed gray ports. The incoming close is proved non-gray, and for
  degree three the remaining short-free slot receives that closing color.

The named equality `onePositiveMActualExposure_eq` identifies the installed
`r = 1` exposure with its designated table row on any actual positive slot;
`twoPositiveMActualExposure_eq` does the same for `r = 2`. Together with the
inherited ordinary-row equality for `r = 0`, this records exact actual parent
exposure in all three branches, not only properness.

`completeResourceLoopAllocation_twoSupportActualFacts` exposes the actual
two-support ports, proper exposure, long incoming helix, non-gray close, and
the degree-three remaining-slot equation. No overwrite map or
last-update-wins convention is used.

E has no child. L exits at xi, closes non-gray, and gives its optional child
the same non-gray color. Every actual child receives its proved F/Q
requirement.

## 9. Expanded root allocation

`completeResourceRootAllocation` first proves positive root degree is one,
two, three, or four from motif avoidance.

- Degree one uses xi = entry = 0 and row `B`.
- Degree two uses xi = entry = 0 and row `B,W`.
- Degree three or four uses xi = 1 and eta = entry = 0.

For large root degree, the actual support cardinality drives the row:

- `r = 0`: fixed `B,W,G` or `B,W,G,G`;
- `r = 1`: the unique positive-short child receives gray by an actual slot
  permutation; and
- `r = 2`: both positive-short children receive gray, with bases `G,G,B` and
  `G,G,B,W` before permutation.

`completeResourceRootAllocation_twoSupport_certificate` states the large-root
two-support result with its necessary premise `3 ≤ pairedChildCount T none`.
It proves every support slot gray and, at degree three, every non-support slot
black. The explicit large-degree premise is essential: degree two with two
positive subtrees correctly uses the xi row `B,W`, not gray ports.

The separate `RootDegreeZeroCertificate` records the empty root resource.
The total empty coloring and its exact global properties are proved directly
in the global module.

## 10. Extension-stable resource invariant and recursion

`ResourceSubtreeCertificate` is parallel to, and does not weaken, the old
`SubtreeCertificate`. Its `sound` field quantifies over every total coloring
that extends the exact subtree assignment and has the prescribed entry
residue. `ResourceSubtreePostcondition` retains:

- the actual head color and installed helix word;
- proper exposure at every paired node in the subtree;
- all gray paired nodes at `xi.opposite`;
- all target-unpaired nodes at `xi`;
- exact child-port installation;
- the requested terminal residue; and
- the non-gray close facts needed by L and two-demand M terminals.

The formal guaranteed resource theorem is
`constructResourceSubtree_resourceInvariant`: every F interface is accepted
when the subtree short count is zero, and every Q interface is accepted when
the count is one or two.

`constructResourceSubtree` recurses by the existing exact measure
`helixSubtreePairCount T H`. At each step it selects E/L/M, chooses the
ordinary transfer except for the two-demand M branch, allocates actual child
ports, recursively constructs every child certificate, and flattens the
pairwise-disjoint exact domains.

Immediately before recursion, `childShortCountLeTwo` applies the global class
bound to each actual outgoing helix. The positive branch explicitly derives
that its count is one or two; `A.requiredOutgoing` then supplies the selected
port's matching F/Q requirement before the recursive call.

The gluing argument is formal rather than implicit:

- `resource_child_domains_pairwiseDisjoint` separates siblings;
- `resource_parent_domain_disjoint_child` separates the parent word from each
  child;
- the paired and unpaired exact decomposition theorems prove full coverage;
- child heads preserve their assigned actual ports;
- each child's `sound` theorem holds in every total extension, so installing
  another disjoint sibling cannot change the certified result;
- actual parent exposure is proved from its closing color and installed child
  ports; and
- global `entryLevel`, `pairedLevel`, and `unpairedLevel` bridges show that a
  sibling is not on another child's ancestor path.

Local parent properness plus the extension-stable child certificates therefore
gives global subtree properness and strong two-separation.

## 11. Root-degree-zero and global coloring

`GlobalColoring.lean` has an explicit degree-zero branch:

- `noPairedNode_of_rootDegreeZero` uses the exact root-subtree partition to
  prove that root paired degree zero leaves no paired target node;
- `rootDegreeZeroColoring` is therefore the genuinely empty coloring;
- `rootDegreeZeroColoring_proper` proves the empty root exposure proper; and
- `rootDegreeZeroColoring_strongTwoSeparatedWith` proves every unpaired node
  is a root child at exact level zero and that there is no gray paired node.

For positive degree, `constructedResourceRootSubtreeColorings` calls
`constructResourceSubtree` with each actual root port.
`assembledResourceRootColoring` flattens the pairwise-disjoint root forest and
uses the existing root partition to totalize it. The actual root port
exposure proves root properness; every nonroot exposure, gray location, and
subtree unpaired level comes from its unique child certificate. Root-unpaired
positions are separately proved to have exact level zero.

`globalColoringCertificateLeTwo` retains one `xi`, one total coloring,
properness, and `StrongTwoSeparatedWith`. The public coloring results are:

```lean
exists_proper_strongTwoSeparatedWith_leTwo
targetClassLeTwo_admits_proper_strongTwoSeparated
targetClassK2_admits_proper_strongTwoSeparated
```

## 12. Unique designability and corollaries

`GlobalColoringCertificateLeTwo.separated` derives ordinary integer
`Separated` from the named two-residue witness. The theorem
`atMostTwoShortHelices_uniqueDesigns` then applies the unchanged generic
theorem `uniqueDesigns_sequenceOfProperSeparatedColoring` to exactly
`sequenceOfProperColoring C.coloring C.proper`.

The requested corollaries are:

- `exactTwoShortHelices_uniqueDesigns` and
  `exactTwoShortHelixDesignability`;
- `oneShortHelixDesignability_from_atMostTwo`, proved from class inclusion;
- `allLongHelices_uniqueDesigns` and `allLongHelixDesignability`;
- `allUnpairedTarget_uniqueDesigns` and
  `allUnpairedTarget_designability`, proved directly from root degree zero;
  and
- `atMostTwoShortHelices_uniqueMinimumEnergy`.

No sequence-assignment, inventory, prefix-balance, saturation, or no-tie
argument is reproved.

## 13. Kernel-checked examples

`RNA/AtMostTwoShort/Examples.lean` checks:

1. `allUnpairedTarget`: new-class membership, short count zero, the explicit
   empty coloring/root-degree-zero construction, and the all-A unique empty
   fold;
2. the existing `(())` target: exact-one/new-class relation, new global
   certificate, properness, strong two-separation, and unique designability;
3. `twoShortRootTarget` for `(())(())`: exact-two membership and the full new
   global/designability result;
4. `degreeThreeTwoShortTarget` for `(())(())((()))`: exact support cardinality
   two, actual gray/gray/black root ports, proper exposure, strong
   two-separation, and unique designability;
5. `internalTwoDemandTarget` for `(((((((())(()))))((())))))`: exact-two
   membership, the critical internal two-support M terminal, long incoming
   helix, valid Q transfer, non-gray close, both actual child ports gray, and
   the full global/designability result;
6. `threeShortControl` for `((.))((.))((.))`: count three and rejection from
   the class; and
7. `lengthOneControl`: rejection due to a maximal helix of length one.

No minimum-size claim is made for the internal Type-I witness, and no negative
control is claimed undesignable.

## 14. Kernel dependency result

`lake build RNA.AtMostTwoShort.AxiomAudit` succeeds and reports the exact
transitive axiom set of the final theorem as:

```text
[propext, Classical.choice, Quot.sound]
```

The same set is reported for every audited load-bearing declaration. See
`docs/AT_MOST_TWO_AXIOM_AUDIT.md` for the complete list and source-token
classification.

## 15. Validation

The focused implementation builds completed successfully for
`ResourceRoot`, `SubtreeConstruction`, `GlobalColoring`, `Designability`, and
`AxiomAudit`. The release commands are:

```bash
lake clean
lake build
lake build RNA.AtMostTwoShort.AxiomAudit
rg -n --glob '*.lean' '\b(sorry|admit|axiom|unsafe|sorryAx|native_decide)\b' RNA RNA.lean
git diff --check
git status --short
```

Final clean archive-source validation status:
`<FINAL_CLEAN_VALIDATION_TO_FILL_AFTER_RELEASE_COMMIT>`.

The current token-aware source scan finds zero `sorry`, zero `admit` commands,
zero `unsafe`, zero `sorryAx`, and zero `native_decide`. The only standalone
`axiom` token is explanatory text in the inherited `FinalAxiomAudit` comment;
all raw plural `axioms` matches are inspection commands or comments.

## 16. Corrections and deviations from Track B prose

The Lean development follows the corrected canonical specification rather
than treating the external Track B prose or Python output as a proof oracle.
The material corrections are:

1. The theorem is stated for at most two short helices, and one resource
   induction covers counts zero, one, and two.
2. The all-unpaired target is included through an explicit root-degree-zero
   branch.
3. The strengthened long-transfer theorem proves only the four explicit
   sufficient words; it makes no overbroad claim equating the complete
   length-four relation with larger even lengths.
4. The gluing invariant is represented by exact disjoint domains,
   extension-stable child certificates, actual port installation, exact node
   coverage, and global level bridges.
5. Root and loop allocations are functions on actual ordered child slots,
   never anonymous multisets or overwrite maps.
6. The two-support large-root audit theorem explicitly assumes large degree;
   degree two with two positive subtrees correctly remains the xi `B,W` row.
7. The frozen legacy-policy n=26 minimality claim, compression argument,
   Python enumeration counts, and finite K2 search totals are not formalized.
8. The Track B Python certificate and copied references are traceability
   evidence only and do not occur in the logical dependency chain.

There are no mathematical weakenings of the final theorem and no changes to
the locked public RNA model.

## 17. Blockers and remaining scope

There are no unresolved proof blockers for the stated theorem. The complete
universal at-most-two result, its exact-two and inherited specializations, and
the energy corollary are machine checked.

Outside the theorem's scope remain wobble pairs, thermodynamic stacking and
loop energies, pseudoknots, more than two length-two helices, and empirical or
biological validation. These are model extensions, not blockers or omitted
premises of the proved statement.
