module

public import RNA.Statement
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

set_option autoImplicit false

/-!
# Kernel-checked model-fidelity examples

All exhaustive claims use the finite `SecondaryStructure n` type, so competitors
range over every noncrossing partial matching on the same complete sequence.
-/

namespace RNA.Examples

open RNA
open Nucleotide

theorem four_position_arc_count : Fintype.card (Arc 4) = 6 := by
  decide

theorem four_position_structure_count :
    Fintype.card (SecondaryStructure 4) = 9 := by
  decide

/-! ## Adjacent positions may pair -/

def adjacentArc : Arc 2 where
  left := 0
  right := 1
  ordered := by decide

def adjacentTarget : SecondaryStructure 2 where
  arcs := {adjacentArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem adjacent_pair_is_present : adjacentArc ∈ adjacentTarget.arcs := by
  decide

/-! ## Interleaving arcs are rejected -/

def crossingArc₁ : Arc 4 where
  left := 0
  right := 2
  ordered := by decide

def crossingArc₂ : Arc 4 where
  left := 1
  right := 3
  ordered := by decide

def crossingArcSet : Finset (Arc 4) :=
  {crossingArc₁, crossingArc₂}

theorem crossingArcSet_is_not_noncrossing :
    ¬ IsNoncrossing crossingArcSet := by
  decide

theorem crossingArcSet_cannot_be_a_secondaryStructure :
    ¬ ∃ S : SecondaryStructure 4, S.arcs = crossingArcSet := by
  rintro ⟨S, hS⟩
  apply crossingArcSet_is_not_noncrossing
  rw [← hS]
  exact S.isNoncrossing

/-! ## The smallest class-K target `(())` -/

def outerArc : Arc 4 where
  left := 0
  right := 3
  ordered := by decide

def innerArc : Arc 4 where
  left := 1
  right := 2
  ordered := by decide

/-- The matching-based four-position target named `(())` in dot-bracket
notation.  The notation is descriptive only; no parser restricts the public
structure type. -/
def nestedTarget : SecondaryStructure 4 where
  arcs := {outerArc, innerArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

theorem nestedTarget_in_classK : InTargetClassK nestedTarget := by
  decide

/-! ## `GGCC` uniquely designs `(())` -/

def ggcc : Sequence 4 := ![G, G, C, C]

/-- Exhaustive over every compatible noncrossing partial matching on all four
positions. -/
theorem ggcc_unique_design : UniqueDesigns ggcc nestedTarget := by
  decide

/-! ## `AUAU` ties via `()()` -/

def leftAdjacentArc : Arc 4 where
  left := 0
  right := 1
  ordered := by decide

def rightAdjacentArc : Arc 4 where
  left := 2
  right := 3
  ordered := by decide

def disjointTarget : SecondaryStructure 4 where
  arcs := {leftAdjacentArc, rightAdjacentArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

def auau : Sequence 4 := ![A, U, A, U]

theorem auau_disjoint_tie :
    StructureCompatible auau nestedTarget ∧
      StructureCompatible auau disjointTarget ∧
      disjointTarget ≠ nestedTarget ∧
      pairCount disjointTarget = pairCount nestedTarget := by
  decide

theorem auau_not_unique_design : ¬ UniqueDesigns auau nestedTarget := by
  intro hdesign
  have hlt := hdesign.2 disjointTarget
    auau_disjoint_tie.2.1 auau_disjoint_tie.2.2.1
  exact (Nat.ne_of_lt hlt) auau_disjoint_tie.2.2.2

/-! ## Energy and pair-count conventions -/

#check energy_lt_iff_pairCount_gt
#check uniqueDesigns_iff_maximum_and_unique_count
#check uniqueDesigns_iff_uniqueMinimumEnergy
#check uniqueMinimumEnergy_iff_maximum_and_unique_count

end RNA.Examples
