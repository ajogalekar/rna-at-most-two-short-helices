# At-most-two-short-helices axiom and dependency audit

## 1. Method and provenance

`RNA/AtMostTwoShort/AxiomAudit.lean` imports the final designability and
example modules, checks the exact public definitions, and asks Lean's kernel
to report transitive axioms for every load-bearing layer.

The source provenance for this audit is:

- frozen downstream base:
  `c37eac40ef5a28bf5733fd576ce6d4c44091ee6a`;
- corrected specification commit:
  `020fa8cd54f64c3e7264fd9dcab7ac11e6b671bc`;
- implementation commit:
  `b64d9165191a89e692d518c4e8cdaa9beafb61f3`;
- documentation/release commit:
  `fcb3bc37db5dddd4bf51b85efaefa644160b19c7`;
- clean archive-source commit:
  `<ARCHIVE_SOURCE_COMMIT_TO_FILL_AFTER_COMMIT>`; and
- source archive SHA-256:
  `<ARCHIVE_SHA256_TO_FILL_AFTER_ARCHIVE_CREATION>`.

The audit command is:

```bash
lake build RNA.AtMostTwoShort.AxiomAudit
```

It completed successfully both in the implementation worktree and after the
documentation/release commit during the from-clean-state release validation.

## 2. Printed public definitions

The audit checks and prints:

- `shortHelixCount`;
- `InTargetClassKLeTwo`;
- `InTargetClassK2`;
- `UniqueDesigns`;
- `AtMostTwoShortHelixDesignabilityStatement`; and
- `atMostTwoShortHelixDesignability`.

The printed final proposition is:

```lean
def AtMostTwoShortHelixDesignabilityStatement : Prop :=
  ∀ {n : Nat} (T : SecondaryStructure n),
    InTargetClassKLeTwo T →
      ∃ w : Sequence n, UniqueDesigns w T
```

and Lean checks:

```text
RNA.atMostTwoShortHelixDesignability :
  AtMostTwoShortHelixDesignabilityStatement
```

## 3. Audited declarations

Short-resource accounting:

- `shortHelixSubtreeCount_decomposition`;
- `loopShortSupport_card_le_two`;
- `rootShortSupport_card_le_two`; and
- `loopShortSupport_card_eq_two_length_at_least_three`.

Strengthened transfer and actual allocations:

- `longTransfer_eta_closesNonGrey_of_Q`;
- `completeResourceLoopAllocation`;
- `onePositiveMActualExposure_eq`;
- `completeResourceLoopAllocation_twoSupportActualFacts`;
- `completeResourceRootAllocation`; and
- `completeResourceRootAllocation_twoSupport_certificate`.

Recursive and global construction:

- `constructResourceSubtree`;
- `constructResourceSubtree_resourceInvariant`;
- `globalColoringCertificateLeTwo`;
- `exists_proper_strongTwoSeparatedWith_leTwo`; and
- `targetClassLeTwo_admits_proper_strongTwoSeparated`.

Unique designability:

- `atMostTwoShortHelices_uniqueDesigns`; and
- `atMostTwoShortHelixDesignability`.

The root two-support declaration is intentionally stated with
`3 ≤ pairedChildCount T none`. Without that premise, support cardinality two
also permits degree two, whose correct root allocation is the xi row `B,W`
rather than two gray ports.

## 4. Kernel-reported transitive dependencies

Lean reports exactly the same transitive axiom set for every audited theorem
and noncomputable construction listed above:

```text
[propext, Classical.choice, Quot.sound]
```

For the final theorem, the audit output is:

```text
'RNA.atMostTwoShortHelixDesignability' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The three dependencies have their standard Lean/Mathlib meanings:

- `propext` is propositional extensionality;
- `Classical.choice` selects witnesses whose existence has been proved,
  including maximal helices, exact finite-slot owners, endpoint types, and
  finite root rows; and
- `Quot.sound` is quotient soundness used transitively through Mathlib data
  structures and the inherited no-tie development.

No project-defined axiom, admitted proposition, external executable, Python
certificate, finite-search oracle, or external RNA-design theorem occurs in
the dependency closure.

When a theorem body is loaded from an `.olean`, `#print` may display
`<not imported>` for the opaque body. This does not indicate a missing proof:
the declaration was compiled before the audit module, and `#print axioms`
still traverses its kernel-checked dependency information.

## 5. Final-theorem dependency path

The new theorem's construction dependency is:

```text
atMostTwoShortHelixDesignability
  → atMostTwoShortHelices_uniqueDesigns
  → globalColoringCertificateLeTwo
  → constructResourceSubtree
  → completeResourceLoopAllocation / chooseResourceTransfer
```

The final unique-design step uses the already checked generic theorem
`uniqueDesigns_sequenceOfProperSeparatedColoring`. The old theorem
`oneShortHelixDesignability` is absent from this path.

Conversely, `oneShortHelixDesignability_from_atMostTwo` is proved after the
new result using `inTargetClassKLeTwo_of_inTargetClassK`, so exact one is a
corollary of the enlarged theorem rather than a premise.

## 6. Source-policy audit

The release policy forbids `sorry`, `admit`, custom `axiom`, mathematical
`unsafe`, `sorryAx`, and `native_decide`. A token-aware scan is:

```bash
rg -n --glob '*.lean' \
  '\b(sorry|admit|axiom|unsafe|sorryAx|native_decide)\b' \
  RNA RNA.lean
```

At documentation-draft time, the classification is:

- `sorry`: zero token or substring occurrences;
- `admit`: zero standalone command tokens. There are 12 raw substring
  occurrences, all in the English words “admit”/“admits” in comments or in
  proved identifiers such as
  `targetClass_admits_proper_strongTwoSeparated` and
  `targetClassLeTwo_admits_proper_strongTwoSeparated`;
- `unsafe`: zero occurrences;
- `sorryAx`: zero occurrences;
- `native_decide`: zero occurrences; and
- `axiom`: one standalone singular token, in the inherited explanatory
  comment of `RNA/FinalAxiomAudit.lean`. There are 121 raw `axiom` substring
  occurrences, consisting of that explanatory text, audit-module names, and
  kernel-inspection commands of the form `#print axioms`. None is an `axiom`
  declaration.

Thus the code-token count for every prohibited construct is zero. The final
release validation should rerun the scan after commit metadata is finalized
and update the raw documentary counts if later comments change.

Ordinary `decide` is used only for kernel-checked finite facts and examples.
Noncomputable definitions use classical choice but do not use mathematical
`unsafe`.

## 7. Build result and release checklist

The focused chain was built successfully through:

```text
RNA.AtMostTwoShort.ResourceRoot
RNA.AtMostTwoShort.SubtreeConstruction
RNA.AtMostTwoShort.GlobalColoring
RNA.AtMostTwoShort.Designability
RNA.AtMostTwoShort.AxiomAudit
```

The required clean release check is:

```bash
lake clean
lake build
lake build RNA.AtMostTwoShort.AxiomAudit
rg -n --glob '*.lean' '\b(sorry|admit|axiom|unsafe|sorryAx|native_decide)\b' RNA RNA.lean
git diff --check
git status --short
```

Final clean validation result:
**PASS (2026-08-20).** From clean commit
`fcb3bc37db5dddd4bf51b85efaefa644160b19c7`, `lake clean && lake build`
completed all 3,070 jobs; the separate audit target completed all 3,056 jobs
and again reported exactly `[propext, Classical.choice, Quot.sound]` for the
final theorem. The token-aware prohibited-source scan returned no matches,
`git diff --check` passed, all copied-reference checksums passed, and the
frozen upstream repository remained clean at the requested base commit.
Warnings were confined to unchanged inherited baseline modules. No new
module emitted a warning or panic.

There are no unresolved logical or proof blockers. The only remaining audit
work at this stage is archive bookkeeping: recording the archive-source
commit and the resulting archive digest.
