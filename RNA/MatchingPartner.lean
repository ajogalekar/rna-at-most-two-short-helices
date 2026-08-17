module

public import RNA.Structure

@[expose] public section

set_option autoImplicit false

/-!
# Exact partners in a finite partial matching

This neutral helper retains the partner hidden by `positionPaired` and is used
for both inventory saturation and the noncrossing interior argument.
-/

namespace RNA

variable {n : Nat}

/-- Positions `i` and `j` are the two oppositely ordered endpoints of one
actual arc of `S`. -/
def PositionPartner (S : SecondaryStructure n) (i j : Fin n) : Prop :=
  ∃ a ∈ S.arcs,
    (i = a.left ∧ j = a.right) ∨
      (i = a.right ∧ j = a.left)

instance (S : SecondaryStructure n) (i j : Fin n) :
    Decidable (PositionPartner S i j) := by
  unfold PositionPartner
  infer_instance

theorem positionPartner_symm {S : SecondaryStructure n} {i j : Fin n}
    (h : PositionPartner S i j) : PositionPartner S j i := by
  obtain ⟨a, ha, horder⟩ := h
  refine ⟨a, ha, ?_⟩
  rcases horder with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

theorem positionPartner_ne {S : SecondaryStructure n} {i j : Fin n}
    (h : PositionPartner S i j) : i ≠ j := by
  obtain ⟨a, _ha, horder⟩ := h
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact a.left_ne_right
  · exact a.right_ne_left

theorem positionPartner_positionPaired_left
    {S : SecondaryStructure n} {i j : Fin n}
    (h : PositionPartner S i j) : S.positionPaired i := by
  obtain ⟨a, ha, horder⟩ := h
  refine ⟨a, ha, ?_⟩
  rcases horder with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact a.incident_left
  · exact a.incident_right

theorem positionPartner_positionPaired_right
    {S : SecondaryStructure n} {i j : Fin n}
    (h : PositionPartner S i j) : S.positionPaired j :=
  positionPartner_positionPaired_left (positionPartner_symm h)

/-- A position is paired exactly when it has a retained partner. -/
theorem positionPaired_iff_exists_partner (S : SecondaryStructure n)
    (i : Fin n) :
    S.positionPaired i ↔ ∃ j : Fin n, PositionPartner S i j := by
  constructor
  · rintro ⟨a, ha, hi⟩
    rcases hi with hleft | hright
    · exact ⟨a.right, ⟨a, ha, Or.inl ⟨hleft, rfl⟩⟩⟩
    · exact ⟨a.left, ⟨a, ha, Or.inr ⟨hright, rfl⟩⟩⟩
  · rintro ⟨j, hij⟩
    exact positionPartner_positionPaired_left hij

/-- A partial matching gives each paired position at most one partner. -/
theorem positionPartner_unique {S : SecondaryStructure n} {i j k : Fin n}
    (hij : PositionPartner S i j) (hik : PositionPartner S i k) : j = k := by
  obtain ⟨a, ha, haorder⟩ := hij
  obtain ⟨b, hb, hborder⟩ := hik
  have hai : a.Incident i := by
    rcases haorder with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hbi : b.Incident i := by
    rcases hborder with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hab : a = b := S.eq_of_mem_of_incident ha hb hai hbi
  subst b
  rcases haorder with ⟨hileft, hjright⟩ | ⟨hiright, hjleft⟩ <;>
    rcases hborder with ⟨hileft', hkright⟩ | ⟨hiright', hkleft⟩
  · exact hjright.trans hkright.symm
  · exfalso
    exact a.left_ne_right (hileft.symm.trans hiright')
  · exfalso
    exact a.right_ne_left (hiright.symm.trans hileft')
  · exact hjleft.trans hkleft.symm

/-- Compatibility of a structure gives compatibility in either partner
orientation. -/
theorem positionPartner_compatible {w : Sequence n}
    {S : SecondaryStructure n} (hS : StructureCompatible w S)
    {i j : Fin n} (hij : PositionPartner S i j) :
    Compatible (w i) (w j) := by
  obtain ⟨a, ha, horder⟩ := hij
  have hcompat := hS a ha
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hcompat
  · exact compatible_symm hcompat

/-- The actual normalized arc joining partners has endpoints `min i j` and
`max i j`. -/
theorem positionPartner_has_ordered_arc {S : SecondaryStructure n}
    {i j : Fin n} (hij : PositionPartner S i j) :
    ∃ a ∈ S.arcs,
      a.left = min i j ∧ a.right = max i j := by
  obtain ⟨a, ha, horder⟩ := hij
  refine ⟨a, ha, ?_⟩
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [le_of_lt a.ordered]
  · simp [le_of_lt a.ordered]

/-- Deterministic partner selected from proved pairedness. -/
noncomputable def partnerOf (S : SecondaryStructure n) (i : Fin n)
    (hi : S.positionPaired i) : Fin n :=
  Classical.choose ((positionPaired_iff_exists_partner S i).1 hi)

theorem partnerOf_spec (S : SecondaryStructure n) (i : Fin n)
    (hi : S.positionPaired i) :
    PositionPartner S i (partnerOf S i hi) :=
  Classical.choose_spec ((positionPaired_iff_exists_partner S i).1 hi)

theorem partnerOf_ne (S : SecondaryStructure n) (i : Fin n)
    (hi : S.positionPaired i) : partnerOf S i hi ≠ i :=
  (positionPartner_ne (partnerOf_spec S i hi)).symm

theorem partnerOf_positionPaired (S : SecondaryStructure n) (i : Fin n)
    (hi : S.positionPaired i) : S.positionPaired (partnerOf S i hi) :=
  positionPartner_positionPaired_right (partnerOf_spec S i hi)

/-- Partner selection is involutive; proof arguments cannot affect the unique
partner. -/
theorem partnerOf_partnerOf (S : SecondaryStructure n) (i : Fin n)
    (hi : S.positionPaired i) :
    partnerOf S (partnerOf S i hi) (partnerOf_positionPaired S i hi) = i := by
  apply positionPartner_unique
    (partnerOf_spec S (partnerOf S i hi) (partnerOf_positionPaired S i hi))
  exact positionPartner_symm (partnerOf_spec S i hi)

end RNA
