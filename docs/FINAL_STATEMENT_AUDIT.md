# Final statement and model-fidelity audit

This audit quotes the declarations in the handwritten Lean source.  It does
not infer the formal model from the manuscript prose.

## Alphabet and compatibility

From `RNA/Alphabet.lean`:

```lean
inductive Nucleotide where
  | A
  | C
  | G
  | U
  deriving DecidableEq, Repr

def Compatible (x y : Nucleotide) : Prop := y = x.comp
```

Here `Nucleotide.comp` exchanges A with U and C with G.  Thus the alphabet is
exactly A/C/G/U and compatibility is exactly Watson--Crick complementarity;
G--U wobble is absent.

## Secondary structures and sequence compatibility

From `RNA/Structure.lean`:

```lean
structure SecondaryStructure (n : Nat) where
  arcs : Finset (Arc n)
  isPartialMatching : IsPartialMatching arcs
  isNoncrossing : IsNoncrossing arcs

def StructureCompatible (w : Sequence n) (S : SecondaryStructure n) : Prop :=
  ∀ a ∈ S.arcs, Compatible (w a.left) (w a.right)
```

An `Arc n` has ordered endpoints `left < right`.  A
`SecondaryStructure n` is an arbitrary finite partial matching whose arcs do
not strictly interleave.  There is no minimum arc length, so adjacent
positions can pair.  `StructureCompatible` checks every selected arc against
one complete sequence `w : Fin n → Nucleotide`.

## Unique designability

From `RNA/Structure.lean`:

```lean
def UniqueDesigns (w : Sequence n) (T : SecondaryStructure n) : Prop :=
  StructureCompatible w T ∧
    ∀ S : SecondaryStructure n,
      StructureCompatible w S →
      S ≠ T →
      pairCount S < pairCount T
```

The target must be compatible.  Every distinct compatible noncrossing partial
matching on the same complete sequence must have strictly fewer pairs.  In
particular, an equal-pair-count competitor is forbidden.

The energy convention in the same file is:

```lean
def energy (_w : Sequence n) (S : SecondaryStructure n) : Int :=
  -(pairCount S : Int)
```

Thus energy is exactly minus pair count, with no stacking, loop, or sequence
terms.

## Exact target class

From `RNA/TargetClass.lean`:

```lean
def InTargetClassK (T : SecondaryStructure n) : Prop :=
  ∃ h₂ : MaximalHelix T,
    h₂.length = 2 ∧
      (∀ h : MaximalHelix T, h.length = 2 → h = h₂) ∧
      (∀ h : MaximalHelix T, h.length ≠ 1) ∧
      (∀ h : MaximalHelix T, h ≠ h₂ → 3 ≤ h.length) ∧
      ¬ HasM5 T ∧
      ¬ HasM3Dot T
```

The existential witness proves that a length-2 maximal helix actually exists;
the following uniqueness clause says every length-2 maximal helix is that
witness.  Consequently the condition is exactly one, not at most one.

## Milestone-1 proposition and final proof

From `RNA/Statement.lean`:

```lean
def OneShortHelixDesignabilityStatement : Prop :=
  ∀ {n : Nat} (T : SecondaryStructure n),
    InTargetClassK T →
      ∃ w : Sequence n, UniqueDesigns w T
```

From `RNA/OneShortHelixDesignability.lean`:

```lean
theorem oneShortHelixDesignability :
    OneShortHelixDesignabilityStatement := by
  intro n T hK
  exact ⟨(globalSequenceCertificate hK).sequence,
    oneShortHelix_uniqueDesigns hK⟩
```

The theorem proves the original named proposition directly.  Unfolding
`OneShortHelixDesignabilityStatement` and `UniqueDesigns` gives exactly:

```lean
∀ {n : Nat} (T : SecondaryStructure n),
  InTargetClassK T →
  ∃ w : Sequence n,
    StructureCompatible w T ∧
    ∀ S : SecondaryStructure n,
      StructureCompatible w S →
      S ≠ T →
      pairCount S < pairCount T
```

## Explicit answers

1. **Does the target begin as a pairing shape with no nucleotide assignments?**
   Yes.  `T : SecondaryStructure n` contains arcs and their validity proofs,
   but no `Nucleotide` field.
2. **Is one complete sequence chosen jointly for the whole target?** Yes.
   The witness is one function `w : Sequence n`, and the final proof uses the
   exact sequence stored in `globalSequenceCertificate hK`.
3. **Do all competitors use that same sequence?** Yes.  The universally
   quantified `S` is checked by `StructureCompatible w S` with the same `w`.
4. **Are competitors arbitrary noncrossing partial matchings?** Yes.  They are
   arbitrary values of `SecondaryStructure n`; neither saturation nor target
   shape is assumed.
5. **Are adjacent positions permitted to pair?** Yes.  `Arc.ordered` requires
   only `left < right`.
6. **Are pseudoknots excluded?** Yes.  `isNoncrossing` forbids strict arc
   interleaving.
7. **Are G--U pairs excluded?** Yes.  `Compatible` admits only the unique
   Watson--Crick complement.
8. **Is a tie forbidden?** Yes.  every distinct compatible competitor must
   satisfy a strict pair-count inequality.
9. **Is the energy exactly minus pair count?** Yes, as the quoted definition
   shows.
10. **Does class K mean exactly one, not at most one, length-2 maximal helix?**
    Yes: existence and uniqueness are separate conjuncts.
11. **Is the final theorem definitionally or propositionally the same
    statement introduced in Milestone 1?** Definitionally: its declared result
    type is the identical named constant
    `OneShortHelixDesignabilityStatement` introduced in Milestone 1.  No
    replacement, merely equivalent proposition, or weakened restatement is
    used.
