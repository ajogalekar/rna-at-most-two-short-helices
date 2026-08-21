module

public import RNA.NoTie
public import RNA.Statement
public import RNA.AtMostTwoShort.GlobalColoring

@[expose] public section

set_option autoImplicit false

/-!
# Unique designability with at most two short helices

The only downstream ingredient is the already general no-tie theorem for a
proper separated coloring.  All target-class work is confined to producing
the new global coloring certificate.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Ordinary integer separation obtained from the named two-residue witness. -/
theorem GlobalColoringCertificateLeTwo.separated
    {hK : InTargetClassKLeTwo T}
    (C : GlobalColoringCertificateLeTwo T hK) : Separated C.coloring :=
  strongTwoSeparated_implies_separated C.coloring
    ((strongTwoSeparated_iff_exists_with C.coloring).2 ⟨C.xi, C.strong⟩)

/-- The deterministic sequence of the new global certificate uniquely
designs its target against every compatible noncrossing partial matching. -/
theorem atMostTwoShortHelices_uniqueDesigns
    (hK : InTargetClassKLeTwo T) :
    UniqueDesigns
      (sequenceOfProperColoring
        (globalColoringCertificateLeTwo hK).coloring
        (globalColoringCertificateLeTwo hK).proper)
      T := by
  let C := globalColoringCertificateLeTwo hK
  exact uniqueDesigns_sequenceOfProperSeparatedColoring
    C.coloring C.proper C.separated

/-- Exact public proposition: zero, one, and two short helices all use the
same resource construction. -/
def AtMostTwoShortHelixDesignabilityStatement : Prop :=
  ∀ {n : Nat} (T : SecondaryStructure n),
    InTargetClassKLeTwo T →
      ∃ w : Sequence n, UniqueDesigns w T

/-- Every motif-free target in the enlarged length class is uniquely
designable in the strict four-letter maximum-base-pair model. -/
theorem atMostTwoShortHelixDesignability :
    AtMostTwoShortHelixDesignabilityStatement := by
  intro n T hK
  exact ⟨sequenceOfProperColoring
      (globalColoringCertificateLeTwo hK).coloring
      (globalColoringCertificateLeTwo hK).proper,
    atMostTwoShortHelices_uniqueDesigns hK⟩

/-! ## Requested specializations -/

/-- Exact-two targets inherit the same deterministic witness. -/
theorem exactTwoShortHelices_uniqueDesigns
    (hK : InTargetClassK2 T) :
    UniqueDesigns
      (sequenceOfProperColoring
        (globalColoringCertificateLeTwo hK.1).coloring
        (globalColoringCertificateLeTwo hK.1).proper)
      T :=
  atMostTwoShortHelices_uniqueDesigns hK.1

/-- Universal exact-two specialization of the main theorem. -/
theorem exactTwoShortHelixDesignability :
    ∀ {n : Nat} (T : SecondaryStructure n),
      InTargetClassK2 T → ∃ w : Sequence n, UniqueDesigns w T := by
  intro n T hK
  exact ⟨sequenceOfProperColoring
      (globalColoringCertificateLeTwo hK.1).coloring
      (globalColoringCertificateLeTwo hK.1).proper,
    exactTwoShortHelices_uniqueDesigns hK⟩

/-- The old exact-one proposition follows from the enlarged theorem via the
class-inclusion lemma.  Its proof does not invoke the old designability
theorem. -/
theorem oneShortHelixDesignability_from_atMostTwo :
    OneShortHelixDesignabilityStatement := by
  intro n T hK
  let hLeTwo := inTargetClassKLeTwo_of_inTargetClassK hK
  exact ⟨sequenceOfProperColoring
      (globalColoringCertificateLeTwo hLeTwo).coloring
      (globalColoringCertificateLeTwo hLeTwo).proper,
    atMostTwoShortHelices_uniqueDesigns hLeTwo⟩

/-- Explicit zero-short (all-long) specialization. -/
theorem allLongHelices_uniqueDesigns
    (hK : InTargetClassKLeTwo T) (_hzero : shortHelixCount T = 0) :
    UniqueDesigns
      (sequenceOfProperColoring
        (globalColoringCertificateLeTwo hK).coloring
        (globalColoringCertificateLeTwo hK).proper)
      T :=
  atMostTwoShortHelices_uniqueDesigns hK

/-- Existential designability form of the all-long specialization. -/
theorem allLongHelixDesignability
    (hK : InTargetClassKLeTwo T) (hzero : shortHelixCount T = 0) :
    ∃ w : Sequence n, UniqueDesigns w T :=
  ⟨sequenceOfProperColoring
      (globalColoringCertificateLeTwo hK).coloring
      (globalColoringCertificateLeTwo hK).proper,
    allLongHelices_uniqueDesigns hK hzero⟩

/-- Explicit all-unpaired base case.  Root degree zero proves the coloring
domain empty and supplies residue zero directly; no target-class theorem is
needed for this stronger local statement. -/
theorem allUnpairedTarget_uniqueDesigns
    (hzero : pairedChildCount T none = 0) :
    UniqueDesigns
      (sequenceOfProperColoring
        (rootDegreeZeroColoring hzero)
        (rootDegreeZeroColoring_proper hzero))
      T := by
  apply uniqueDesigns_sequenceOfProperSeparatedColoring
  exact strongTwoSeparated_implies_separated (rootDegreeZeroColoring hzero)
    ((strongTwoSeparated_iff_exists_with (rootDegreeZeroColoring hzero)).2
      ⟨0, rootDegreeZeroColoring_strongTwoSeparatedWith hzero⟩)

/-- Existential all-unpaired designability corollary. -/
theorem allUnpairedTarget_designability
    (hzero : pairedChildCount T none = 0) :
    ∃ w : Sequence n, UniqueDesigns w T :=
  ⟨sequenceOfProperColoring
      (rootDegreeZeroColoring hzero)
      (rootDegreeZeroColoring_proper hzero),
    allUnpairedTarget_uniqueDesigns hzero⟩

/-! ## Energy formulation -/

/-- Equivalent unique-minimum-energy form for `energy = -pairCount`. -/
theorem atMostTwoShortHelices_uniqueMinimumEnergy
    (hK : InTargetClassKLeTwo T) :
    UniqueMinimumEnergy
      (sequenceOfProperColoring
        (globalColoringCertificateLeTwo hK).coloring
        (globalColoringCertificateLeTwo hK).proper)
      T :=
  (uniqueDesigns_iff_uniqueMinimumEnergy
    (sequenceOfProperColoring
      (globalColoringCertificateLeTwo hK).coloring
      (globalColoringCertificateLeTwo hK).proper) T).1
        (atMostTwoShortHelices_uniqueDesigns hK)

end RNA
