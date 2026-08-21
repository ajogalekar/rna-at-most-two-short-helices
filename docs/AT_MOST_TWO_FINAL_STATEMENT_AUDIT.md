# At-most-two final statement audit

## Printed declarations

The release audit module `RNA/AtMostTwoShort/AxiomAudit.lean` checks and prints
the following declarations directly:

```lean
def shortHelixCount (T : SecondaryStructure n) : Nat :=
  (lengthTwoHelices T).card

def InTargetClassKLeTwo (T : SecondaryStructure n) : Prop :=
  shortHelixCount T ≤ 2 ∧
    (∀ H : MaximalHelix T, H.length ≠ 1) ∧
    (∀ H : MaximalHelix T, H.length ≠ 2 → 3 ≤ H.length) ∧
    ¬ HasM5 T ∧
    ¬ HasM3Dot T

def InTargetClassK2 (T : SecondaryStructure n) : Prop :=
  InTargetClassKLeTwo T ∧ shortHelixCount T = 2

def UniqueDesigns (w : Sequence n) (T : SecondaryStructure n) : Prop :=
  StructureCompatible w T ∧
    ∀ S : SecondaryStructure n,
      StructureCompatible w S →
      S ≠ T →
      pairCount S < pairCount T

def AtMostTwoShortHelixDesignabilityStatement : Prop :=
  ∀ {n : Nat} (T : SecondaryStructure n),
    InTargetClassKLeTwo T →
      ∃ w : Sequence n, UniqueDesigns w T

theorem atMostTwoShortHelixDesignability :
  AtMostTwoShortHelixDesignabilityStatement
```

`lengthTwoHelices T` is `maximalHelicesOfLength T 2`, so
`shortHelixCount` counts maximal helices of exact length two rather than arcs,
pairs, or a chosen presentation of a stacked run.

## Scientific translation

For every backbone length and every pseudoknot-free target partial matching on
that backbone, if the target has at most two maximal helices of length two, no
maximal helix of length one, all other maximal helices of length at least
three, and neither forbidden motif, then one complete four-letter sequence
exists on which the target has strictly more pairs than every distinct
compatible pseudoknot-free partial matching.

Because energy is `-pairCount`, this is equivalently a unique-minimum-energy
statement in the locked model.

## Required questions

1. **Does “at most two” include zero, one, and two?** Yes. The condition is
   the natural-number inequality `shortHelixCount T ≤ 2`; the same resource
   construction handles all three values.

2. **Does it include the all-unpaired target?** Yes. With no arcs there are no
   maximal helices, all helix-length clauses are vacuous, the short count is
   zero, and both motif exclusions hold. The global construction has an
   explicit root-degree-zero empty-coloring branch, and `Examples.lean`
   checks the all-A unique empty fold independently.

3. **Are length-one helices excluded?** Yes. The target predicate retains the
   explicit clause `∀ H, H.length ≠ 1`.

4. **Must every non-short helix have length at least three?** Yes. The exact
   clause is `∀ H, H.length ≠ 2 → 3 ≤ H.length`.

5. **Are the definitions of m5 and m3-dot unchanged?** Yes. `HasM5` and
   `HasM3Dot` are imported from the frozen baseline without modification; the
   downstream class merely negates them.

6. **Do all competitors use one fixed complete sequence?** Yes. A single
   witness `w : Sequence n` is chosen before `UniqueDesigns w T` quantifies
   over competitors, and that same `w` occurs in every compatibility premise.

7. **Are competitors arbitrary noncrossing partial matchings?** Yes. The
   competitor variable ranges over every `S : SecondaryStructure n`. That
   public type is an arbitrary finite arc set carrying only partial-matching
   and noncrossing proofs; it is not restricted to a grammar generated from
   the target.

8. **Are adjacent pairings permitted?** Yes. An `Arc n` requires only
   `left < right`; no minimum hairpin distance is imposed. The length-one
   negative control itself uses an adjacent pair.

9. **Are G-U pairs excluded?** Yes. `Compatible x y` means
   `y = x.comp`, with only A-U, U-A, C-G, and G-C complements.

10. **Are ties forbidden?** Yes. Every distinct compatible competitor must
    satisfy the strict inequality `pairCount S < pairCount T`.

11. **Does the proof use the new resource induction directly?** Yes. The
    dependency path is
    `atMostTwoShortHelixDesignability` →
    `atMostTwoShortHelices_uniqueDesigns` →
    `globalColoringCertificateLeTwo` →
    `constructResourceSubtree`. The old exact-one designability theorem is not
    a premise. Conversely, `oneShortHelixDesignability_from_atMostTwo` is
    proved after the new theorem by class inclusion.
