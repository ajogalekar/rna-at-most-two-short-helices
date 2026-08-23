def AtMostTwoShortHelixDesignabilityStatement : Prop :=
  ∀ {n : Nat} (T : SecondaryStructure n),
    InTargetClassKLeTwo T →
      ∃ w : Sequence n, UniqueDesigns w T
theorem atMostTwoShortHelixDesignability :
    AtMostTwoShortHelixDesignabilityStatement := by
  intro n T hK
  exact ⟨sequenceOfProperColoring
      (globalColoringCertificateLeTwo hK).coloring
      (globalColoringCertificateLeTwo hK).proper,
    atMostTwoShortHelices_uniqueDesigns hK⟩
