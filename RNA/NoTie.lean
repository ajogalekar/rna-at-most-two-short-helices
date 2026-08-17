module

public import RNA.PairedRestriction
public import RNA.SaturatedUniqueness

@[expose] public section

set_option autoImplicit false

/-!
# The general no-tie theorem

This theorem needs only a proper separated coloring.  Class `K` enters later,
solely to supply such a coloring and the already fixed Milestone-4 sequence.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- **Canonical Theorem 22.** A compatible competitor tying the target pair
count on the sequence of a proper separated coloring is the target itself. -/
theorem noTie_sequenceOfProperSeparatedColoring
    (χ : Coloring T) (hProper : ProperColoring χ)
    (hSeparated : Separated χ)
    (S : SecondaryStructure n)
    (hS : StructureCompatible (sequenceOfProperColoring χ hProper) S)
    (hEq : pairCount S = pairCount T) :
    S = T := by
  let w := sequenceOfProperColoring χ hProper
  have hUnpaired : unpairedPositionSet S = unpairedPositionSet T := by
    exact unpairedPositionSet_eq_of_tied
      χ hProper hSeparated S hS hEq
  have hRestricted :
      competitorPairedRestriction T S hUnpaired =
        targetPairedRestriction T := by
    apply saturated_unique_of_localDistinctness
      (targetPairedRestriction T) (pairedRestrictedSequence T w)
    · exact saturatedStructure_targetPairedRestriction T
    · apply structureCompatible_targetPairedRestriction
      exact structureCompatible_sequenceOfProperColoring χ hProper
    · apply locallyDistinct_targetPairedRestriction
      exact locallyDistinct_sequenceOfProperColoring χ hProper
    · exact saturatedStructure_competitorPairedRestriction T S hUnpaired
    · exact structureCompatible_competitorPairedRestriction
        T S hUnpaired w hS
  exact eq_target_of_competitorPairedRestriction_eq
    T S hUnpaired hRestricted

/-- Readable equality-case alias for the general no-tie theorem. -/
theorem eq_target_of_tied_pairCount
    (χ : Coloring T) (hProper : ProperColoring χ)
    (hSeparated : Separated χ)
    (S : SecondaryStructure n)
    (hS : StructureCompatible (sequenceOfProperColoring χ hProper) S)
    (hEq : pairCount S = pairCount T) :
    S = T :=
  noTie_sequenceOfProperSeparatedColoring
    χ hProper hSeparated S hS hEq

/-- A proper separated coloring yields a complete sequence which strictly
beats every distinct compatible noncrossing partial matching.  This is the
self-contained replacement for any external RNA-design implication. -/
theorem uniqueDesigns_sequenceOfProperSeparatedColoring
    (χ : Coloring T) (hProper : ProperColoring χ)
    (hSeparated : Separated χ) :
    UniqueDesigns (sequenceOfProperColoring χ hProper) T := by
  constructor
  · exact structureCompatible_sequenceOfProperColoring χ hProper
  · intro S hS hST
    have hle : pairCount S ≤ pairCount T :=
      pairCount_le_sequenceOfProperColoring χ hProper S hS
    have hne : pairCount S ≠ pairCount T := by
      intro hEq
      exact hST (noTie_sequenceOfProperSeparatedColoring
        χ hProper hSeparated S hS hEq)
    exact lt_of_le_of_ne hle hne

end RNA
