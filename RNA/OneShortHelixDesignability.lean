module

public import RNA.NoTie
public import RNA.Statement

@[expose] public section

set_option autoImplicit false

/-!
# Final one-short-helix designability theorem

The witness is exactly the complete sequence retained by the Milestone-4
global certificate.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Every class-K target is uniquely designed by its exact Milestone-4
sequence witness. -/
theorem oneShortHelix_uniqueDesigns
    (hK : InTargetClassK T) :
    UniqueDesigns (globalSequenceCertificate hK).sequence T := by
  let G := globalSequenceCertificate hK
  rw [G.sequence_eq]
  exact uniqueDesigns_sequenceOfProperSeparatedColoring
    G.coloringCertificate.coloring
    G.coloringCertificate.proper
    G.coloringCertificate.separated

/-- **Canonical Theorem 23.** Every target with exactly one length-two
maximal helix and the remaining class-K conditions has one complete sequence
which forbids both improvements and ties among all compatible noncrossing
partial matchings. -/
theorem oneShortHelixDesignability :
    OneShortHelixDesignabilityStatement := by
  intro n T hK
  exact ⟨(globalSequenceCertificate hK).sequence,
    oneShortHelix_uniqueDesigns hK⟩

/-- Equivalent unique-minimum-energy formulation for the exact energy
`E = -pairCount`. -/
theorem oneShortHelix_uniqueMinimumEnergy
    (hK : InTargetClassK T) :
    UniqueMinimumEnergy (globalSequenceCertificate hK).sequence T :=
  (uniqueDesigns_iff_uniqueMinimumEnergy
    (globalSequenceCertificate hK).sequence T).1
      (oneShortHelix_uniqueDesigns hK)

end RNA
