module

public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# The black/white/grey colour algebra

This module contains the local, structure-independent part of the colouring
theory in Sections 3 and 8--10 of the canonical manuscript.  Integer values are
kept in `Color.delta`; their images in `Parity = ZMod 2` are used only for the
two residue classes in strong 2-separation and in the local helix lemmas.
-/

namespace RNA

/-- The three colours assigned to nonroot paired interval-tree nodes. -/
inductive Color where
  | black
  | white
  | grey
  deriving DecidableEq, Repr

instance : Fintype Color where
  elems := {Color.black, Color.white, Color.grey}
  complete := by
    intro c
    cases c <;> simp

namespace Color

/-- Exchange black and white and fix grey. -/
@[simp]
def inv : Color → Color
  | black => white
  | white => black
  | grey => grey

/-- The signed contribution of one coloured pair to its inclusive level. -/
@[simp]
def delta : Color → Int
  | black => 1
  | white => -1
  | grey => 0

@[simp]
theorem inv_inv (c : Color) : c.inv.inv = c := by
  cases c <;> rfl

@[simp]
theorem inv_eq_self_iff (c : Color) : c.inv = c ↔ c = grey := by
  cases c <;> decide

@[simp]
theorem inv_eq_grey_iff (c : Color) : c.inv = grey ↔ c = grey := by
  cases c <;> decide

@[simp]
theorem delta_inv (c : Color) : c.inv.delta = -c.delta := by
  cases c <;> decide

/-- A colour is non-grey exactly when it is black or white. -/
def NonGrey (c : Color) : Prop := c ≠ grey

instance (c : Color) : Decidable c.NonGrey := by
  unfold NonGrey
  infer_instance

@[simp]
theorem nonGrey_iff (c : Color) : c.NonGrey ↔ c = black ∨ c = white := by
  cases c <;> simp [NonGrey]

@[simp]
theorem black_nonGrey : black.NonGrey := by
  decide

@[simp]
theorem white_nonGrey : white.NonGrey := by
  decide

@[simp]
theorem not_grey_nonGrey : ¬ grey.NonGrey := by
  decide

end Color

/-- The exact two-element residue type used by strong 2-separation. -/
abbrev Parity := ZMod 2

namespace Parity

@[simp]
theorem zero_ne_one : (0 : Parity) ≠ 1 := by
  decide

@[simp]
theorem one_ne_zero : (1 : Parity) ≠ 0 := by
  decide

@[simp]
theorem add_zero (r : Parity) : r + 0 = r := by
  exact _root_.add_zero r

@[simp]
theorem zero_add (r : Parity) : 0 + r = r := by
  exact _root_.zero_add r

@[simp]
theorem one_add_one : (1 : Parity) + 1 = 0 := by
  decide

/-- The residue opposite to `r`. -/
def opposite (r : Parity) : Parity := r + 1

theorem add_one_eq_opposite (r : Parity) : r + 1 = r.opposite := by
  rfl

@[simp]
theorem opposite_opposite (r : Parity) : r.opposite.opposite = r := by
  have htwo : (1 : Parity) + 1 = 0 := by decide
  simp only [opposite, add_assoc, htwo, add_zero]

@[simp]
theorem add_one_add_one (r : Parity) : r + 1 + 1 = r := by
  exact r.opposite_opposite

@[simp]
theorem opposite_add_one (r : Parity) : r.opposite + 1 = r := by
  exact r.opposite_opposite

@[simp]
theorem opposite_ne (r : Parity) : r.opposite ≠ r := by
  simp [opposite]

@[simp]
theorem ne_opposite (r : Parity) : r ≠ r.opposite := by
  exact r.opposite_ne.symm

/-- Every residue is either `r` or its unique opposite. -/
theorem eq_or_eq_opposite (r s : Parity) : s = r ∨ s = r.opposite := by
  fin_cases r <;> fin_cases s <;> unfold opposite
  all_goals first | exact Or.inl rfl | exact Or.inr rfl

/-- Inequality in `Parity` determines the opposite residue. -/
theorem eq_opposite_of_ne {r s : Parity} (h : s ≠ r) : s = r.opposite := by
  exact (r.eq_or_eq_opposite s).resolve_left h

end Parity

namespace Color

/-- The parity contribution of a colour, obtained from its integer delta. -/
def deltaParity (c : Color) : Parity := (c.delta : Parity)

@[simp]
theorem deltaParity_black : black.deltaParity = 1 := by
  rfl

@[simp]
theorem deltaParity_white : white.deltaParity = 1 := by
  decide

@[simp]
theorem deltaParity_grey : grey.deltaParity = 0 := by
  rfl

@[simp]
theorem deltaParity_inv (c : Color) : c.inv.deltaParity = c.deltaParity := by
  cases c <;> simp [deltaParity]

@[simp]
theorem deltaParity_eq_zero_iff (c : Color) : c.deltaParity = 0 ↔ c = grey := by
  cases c <;> decide

@[simp]
theorem deltaParity_eq_one_iff (c : Color) : c.deltaParity = 1 ↔ c.NonGrey := by
  cases c <;> decide

/-- A first helix colour is admissible at `entry` (relative to grey residue
`eta`) when it is non-grey, or when it is grey and enters at `eta`. -/
def AdmissibleAt (c : Color) (entry eta : Parity) : Prop :=
  c.NonGrey ∨ (c = grey ∧ entry = eta)

instance (c : Color) (entry eta : Parity) : Decidable (c.AdmissibleAt entry eta) := by
  unfold AdmissibleAt
  infer_instance

@[simp]
theorem admissibleAt_black (entry eta : Parity) : black.AdmissibleAt entry eta := by
  simp [AdmissibleAt]

@[simp]
theorem admissibleAt_white (entry eta : Parity) : white.AdmissibleAt entry eta := by
  simp [AdmissibleAt]

@[simp]
theorem admissibleAt_grey_iff (entry eta : Parity) :
    grey.AdmissibleAt entry eta ↔ entry = eta := by
  simp [AdmissibleAt, NonGrey]

end Color

/-- The capacity predicate for an exposed multiset: one black, one white, and
two grey entries at most. -/
def ProperExposure (X : Multiset Color) : Prop :=
  X.count Color.black ≤ 1 ∧
    X.count Color.white ≤ 1 ∧
      X.count Color.grey ≤ 2

/-- Exposure capacity is inherited by submultisets. -/
theorem ProperExposure.mono {X Y : Multiset Color}
    (hXY : X ≤ Y) (hY : ProperExposure Y) : ProperExposure X := by
  rcases hY with ⟨hblack, hwhite, hgrey⟩
  exact ⟨
    (Multiset.count_le_of_le Color.black hXY).trans hblack,
    (Multiset.count_le_of_le Color.white hXY).trans hwhite,
    (Multiset.count_le_of_le Color.grey hXY).trans hgrey⟩

instance (X : Multiset Color) : Decidable (ProperExposure X) := by
  unfold ProperExposure
  infer_instance

/-- The exposed multiset at the outer member of an adjacent helix pair. -/
def adjacentExposure (outer inner : Color) : Multiset Color :=
  {outer.inv, inner}

/-- Local properness between two consecutive members of one helix. -/
def ProperAdjacent (outer inner : Color) : Prop :=
  ProperExposure (adjacentExposure outer inner)

instance (outer inner : Color) : Decidable (ProperAdjacent outer inner) := by
  unfold ProperAdjacent
  infer_instance

/-- The only improper adjacent colour pairs are black-white and white-black. -/
theorem properAdjacent_iff (outer inner : Color) :
    ProperAdjacent outer inner ↔
      (outer, inner) ≠ (Color.black, Color.white) ∧
      (outer, inner) ≠ (Color.white, Color.black) := by
  cases outer <;> cases inner <;> decide

@[simp]
theorem not_properAdjacent_black_white :
    ¬ ProperAdjacent Color.black Color.white := by
  decide

@[simp]
theorem not_properAdjacent_white_black :
    ¬ ProperAdjacent Color.white Color.black := by
  decide

@[simp]
theorem properAdjacent_black_black :
    ProperAdjacent Color.black Color.black := by
  decide

@[simp]
theorem properAdjacent_black_grey :
    ProperAdjacent Color.black Color.grey := by
  decide

@[simp]
theorem properAdjacent_grey_black :
    ProperAdjacent Color.grey Color.black := by
  decide

@[simp]
theorem properAdjacent_grey_grey :
    ProperAdjacent Color.grey Color.grey := by
  decide

end RNA
