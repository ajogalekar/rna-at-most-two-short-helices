module

public import RNA.GlobalSequence

@[expose] public section

set_option autoImplicit false

/-!
# Unpaired positions of a tied competitor

For the sequence assigned by a proper separated coloring, the Milestone-4
equality case and target-unpaired pairing obstruction imply that every
target-unpaired position remains unpaired in a compatible competitor tying the
target pair count.  The exact position-role partition then upgrades this
inclusion to equality of the two finite unpaired-position sets.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- The finite set of positions left unpaired by a secondary structure. -/
def unpairedPositionSet (S : SecondaryStructure n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ¬ S.positionPaired i)

@[simp]
theorem mem_unpairedPositionSet {S : SecondaryStructure n} {i : Fin n} :
    i ∈ unpairedPositionSet S ↔ ¬ S.positionPaired i := by
  simp [unpairedPositionSet]

/-- The finite-set count agrees with the existing subtype count. -/
theorem unpairedPositionSet_card_eq_targetUnpairedCount
    (S : SecondaryStructure n) :
    (unpairedPositionSet S).card = targetUnpairedCount S := by
  simpa [unpairedPositionSet, targetUnpairedCount, UnpairedPosition] using
    (Fintype.card_subtype (fun i : Fin n => ¬ S.positionPaired i)).symm

/-- Every position is either unpaired or one of the two endpoints of a unique
pair. -/
theorem targetUnpairedCount_add_two_mul_pairCount
    (S : SecondaryStructure n) :
    targetUnpairedCount S + 2 * pairCount S = n := by
  have hcard := Fintype.card_congr (positionRoleEquiv S)
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hcard
  have hside : Fintype.card EndpointSide = 2 := by decide
  rw [hside] at hcard
  simpa only [targetUnpairedCount, pairCount, PairedNode,
    Fintype.card_coe, Nat.mul_comm] using hcard

/-- Equivalent subtraction form of the exact paired/unpaired position count. -/
theorem targetUnpairedCount_eq_length_sub_two_mul_pairCount
    (S : SecondaryStructure n) :
    targetUnpairedCount S = n - 2 * pairCount S := by
  have hcount := targetUnpairedCount_add_two_mul_pairCount S
  omega

/-- Equal pair counts on the same backbone give equal unpaired-position
counts. -/
theorem targetUnpairedCount_eq_of_pairCount_eq
    (S T : SecondaryStructure n) (hEq : pairCount S = pairCount T) :
    targetUnpairedCount S = targetUnpairedCount T := by
  have hS := targetUnpairedCount_add_two_mul_pairCount S
  have hT := targetUnpairedCount_add_two_mul_pairCount T
  omega

/-- In a tied compatible competitor for a proper separated coloring, every
target-unpaired position remains unpaired. -/
theorem targetUnpaired_subset_competitor_unpaired
    (χ : Coloring T) (hProper : ProperColoring χ)
    (hSeparated : Separated χ)
    (S : SecondaryStructure n)
    (hS : StructureCompatible (sequenceOfProperColoring χ hProper) S)
    (hEq : pairCount S = pairCount T) :
    unpairedPositionSet T ⊆ unpairedPositionSet S := by
  have hLimiting :=
    equality_uses_all_limiting_nucleotides χ hProper S hS hEq
  intro i hiTarget
  rw [mem_unpairedPositionSet] at hiTarget ⊢
  intro hiCompetitor
  obtain ⟨j, hPartner⟩ :=
    (positionPaired_iff_exists_partner S i).1 hiCompetitor
  let u : UnpairedPosition T := ⟨i, hiTarget⟩
  obtain ⟨k, hGC, hkUnpaired⟩ :=
    targetUnpaired_pairing_obstruction
      χ hProper hSeparated S hS u j hPartner
  rcases hGC with hG | hC
  · exact hkUnpaired (hLimiting.2.2 k hG)
  · exact hkUnpaired (hLimiting.2.1 k hC)

/-- A compatible competitor tying the target pair count has exactly the same
unpaired-position set as the target. -/
theorem unpairedPositionSet_eq_of_tied
    (χ : Coloring T) (hProper : ProperColoring χ)
    (hSeparated : Separated χ)
    (S : SecondaryStructure n)
    (hS : StructureCompatible (sequenceOfProperColoring χ hProper) S)
    (hEq : pairCount S = pairCount T) :
    unpairedPositionSet S = unpairedPositionSet T := by
  have hSubset : unpairedPositionSet T ⊆ unpairedPositionSet S :=
    targetUnpaired_subset_competitor_unpaired
      χ hProper hSeparated S hS hEq
  have hCount : targetUnpairedCount S = targetUnpairedCount T :=
    targetUnpairedCount_eq_of_pairCount_eq S T hEq
  symm
  apply Finset.eq_of_subset_of_card_le hSubset
  rw [unpairedPositionSet_card_eq_targetUnpairedCount,
    unpairedPositionSet_card_eq_targetUnpairedCount, hCount]

end RNA
