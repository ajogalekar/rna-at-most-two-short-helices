module

public import RNA.IntervalTree

@[expose] public section

set_option autoImplicit false

/-!
# Unique backbone-position roles

Every position of a partial matching is either target-unpaired or is exactly
one endpoint of exactly one target pair.  The equivalence in this file is the
shared representation used by sequence assignment, counting, and prefix
scans.  In particular, endpoint lookup never manufactures a default arc.
-/

namespace RNA

variable {n : Nat}

/-- Which endpoint of a normalized target arc occupies a position. -/
inductive EndpointSide where
  | left
  | right
  deriving DecidableEq, Repr

instance instFintypeEndpointSide : Fintype EndpointSide where
  elems := {EndpointSide.left, EndpointSide.right}
  complete := by intro s; cases s <;> simp

/-- The three disjoint kinds of role occupied by a backbone position. -/
abbrev PositionRole (T : SecondaryStructure n) :=
  UnpairedPosition T ⊕ (PairedNode T × EndpointSide)

/-- The actual backbone position occupied by a role. -/
def positionOfRole (T : SecondaryStructure n) : PositionRole T → Fin n
  | Sum.inl u => u.val
  | Sum.inr (v, EndpointSide.left) => v.val.left
  | Sum.inr (v, EndpointSide.right) => v.val.right

/-- No target left endpoint can also be a target right endpoint. -/
theorem no_left_right_endpoint (T : SecondaryStructure n)
    (v q : PairedNode T) : v.val.left ≠ q.val.right := by
  intro h
  have hvq : v.val = q.val :=
    T.eq_of_mem_of_incident v.property q.property
      v.val.incident_left (Or.inr h)
  have hsame : v.val.left = v.val.right := by
    calc
      v.val.left = q.val.right := h
      _ = v.val.right := congrArg Arc.right hvq.symm
  exact v.val.left_ne_right hsame

/-- The explicit role-to-position map is injective by partial matching. -/
theorem positionOfRole_injective (T : SecondaryStructure n) :
    Function.Injective (positionOfRole T) := by
  intro r s hrs
  cases r with
  | inl u =>
      cases s with
      | inl v =>
          exact congrArg Sum.inl (Subtype.ext hrs)
      | inr ve =>
          rcases ve with ⟨v, side⟩
          exfalso
          apply u.property
          refine ⟨v.val, v.property, ?_⟩
          cases side with
          | left =>
              change u.val = v.val.left at hrs
              exact Or.inl hrs
          | right =>
              change u.val = v.val.right at hrs
              exact Or.inr hrs
  | inr ve =>
      rcases ve with ⟨v, vside⟩
      cases s with
      | inl u =>
          exfalso
          apply u.property
          refine ⟨v.val, v.property, ?_⟩
          cases vside with
          | left =>
              change v.val.left = u.val at hrs
              exact Or.inl hrs.symm
          | right =>
              change v.val.right = u.val at hrs
              exact Or.inr hrs.symm
      | inr qe =>
          rcases qe with ⟨q, qside⟩
          cases vside <;> cases qside
          · have hvq : v = q := by
              apply Subtype.ext
              exact T.eq_of_mem_of_incident v.property q.property
                v.val.incident_left (Or.inl hrs)
            subst q
            rfl
          · exact False.elim ((no_left_right_endpoint T v q) hrs)
          · exact False.elim ((no_left_right_endpoint T q v) hrs.symm)
          · have hvq : v = q := by
              apply Subtype.ext
              exact T.eq_of_mem_of_incident v.property q.property
                v.val.incident_right (Or.inr hrs)
            subst q
            rfl

/-- Every backbone position is occupied by one of the explicit roles. -/
theorem positionOfRole_surjective (T : SecondaryStructure n) :
    Function.Surjective (positionOfRole T) := by
  intro i
  by_cases hi : T.positionPaired i
  · obtain ⟨a, ha, hia⟩ := hi
    let v : PairedNode T := ⟨a, ha⟩
    rcases hia with hleft | hright
    · exact ⟨Sum.inr (v, EndpointSide.left), hleft.symm⟩
    · exact ⟨Sum.inr (v, EndpointSide.right), hright.symm⟩
  · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩

/-- Finite equivalence expressing the exact role partition of the backbone. -/
noncomputable def positionRoleEquiv (T : SecondaryStructure n) :
    PositionRole T ≃ Fin n :=
  Equiv.ofBijective (positionOfRole T)
    ⟨positionOfRole_injective T, positionOfRole_surjective T⟩

/-- The unique role occupied by `i`. -/
noncomputable def positionRoleAt (T : SecondaryStructure n) (i : Fin n) :
    PositionRole T :=
  (positionRoleEquiv T).symm i

@[simp]
theorem positionOfRole_positionRoleAt (T : SecondaryStructure n) (i : Fin n) :
    positionOfRole T (positionRoleAt T i) = i :=
  (positionRoleEquiv T).apply_symm_apply i

@[simp]
theorem positionRoleAt_positionOfRole (T : SecondaryStructure n)
    (r : PositionRole T) :
    positionRoleAt T (positionOfRole T r) = r :=
  (positionRoleEquiv T).symm_apply_apply r

@[simp]
theorem positionRoleAt_unpaired (T : SecondaryStructure n)
    (u : UnpairedPosition T) :
    positionRoleAt T u.val = Sum.inl u := by
  change positionRoleAt T (positionOfRole T (Sum.inl u)) = Sum.inl u
  exact positionRoleAt_positionOfRole T (Sum.inl u)

@[simp]
theorem positionRoleAt_left (T : SecondaryStructure n)
    (v : PairedNode T) :
    positionRoleAt T v.val.left = Sum.inr (v, EndpointSide.left) := by
  change positionRoleAt T
    (positionOfRole T (Sum.inr (v, EndpointSide.left))) =
      Sum.inr (v, EndpointSide.left)
  exact positionRoleAt_positionOfRole T
    (Sum.inr (v, EndpointSide.left))

@[simp]
theorem positionRoleAt_right (T : SecondaryStructure n)
    (v : PairedNode T) :
    positionRoleAt T v.val.right = Sum.inr (v, EndpointSide.right) := by
  change positionRoleAt T
    (positionOfRole T (Sum.inr (v, EndpointSide.right))) =
      Sum.inr (v, EndpointSide.right)
  exact positionRoleAt_positionOfRole T
    (Sum.inr (v, EndpointSide.right))

/-- Every position has exactly one explicit role. -/
theorem existsUnique_positionRole (T : SecondaryStructure n) (i : Fin n) :
    ∃! r : PositionRole T, positionOfRole T r = i := by
  refine ⟨positionRoleAt T i, positionOfRole_positionRoleAt T i, ?_⟩
  intro r hr
  exact positionOfRole_injective T (hr.trans
    (positionOfRole_positionRoleAt T i).symm)

/-- A paired position belongs to a unique target pair. -/
theorem unique_pair_of_positionPaired (T : SecondaryStructure n) (i : Fin n)
    (hi : T.positionPaired i) :
    ∃! v : PairedNode T, v.val.Incident i := by
  obtain ⟨a, ha, hai⟩ := hi
  refine ⟨⟨a, ha⟩, hai, ?_⟩
  intro q hqi
  apply Subtype.ext
  exact T.eq_of_mem_of_incident q.property ha hqi hai

/-- Optional left-endpoint lookup with no default arc. -/
noncomputable def leftEndpointNode? (T : SecondaryStructure n) (i : Fin n) :
    Option (PairedNode T) :=
  match positionRoleAt T i with
  | Sum.inr (v, EndpointSide.left) => some v
  | _ => none

/-- Optional right-endpoint lookup with no default arc. -/
noncomputable def rightEndpointNode? (T : SecondaryStructure n) (i : Fin n) :
    Option (PairedNode T) :=
  match positionRoleAt T i with
  | Sum.inr (v, EndpointSide.right) => some v
  | _ => none

@[simp]
theorem leftEndpointNode?_left (T : SecondaryStructure n) (v : PairedNode T) :
    leftEndpointNode? T v.val.left = some v := by
  simp [leftEndpointNode?]

@[simp]
theorem leftEndpointNode?_right (T : SecondaryStructure n) (v : PairedNode T) :
    leftEndpointNode? T v.val.right = none := by
  simp [leftEndpointNode?]

@[simp]
theorem leftEndpointNode?_unpaired (T : SecondaryStructure n)
    (u : UnpairedPosition T) :
    leftEndpointNode? T u.val = none := by
  simp [leftEndpointNode?]

@[simp]
theorem rightEndpointNode?_right (T : SecondaryStructure n) (v : PairedNode T) :
    rightEndpointNode? T v.val.right = some v := by
  simp [rightEndpointNode?]

@[simp]
theorem rightEndpointNode?_left (T : SecondaryStructure n) (v : PairedNode T) :
    rightEndpointNode? T v.val.left = none := by
  simp [rightEndpointNode?]

@[simp]
theorem rightEndpointNode?_unpaired (T : SecondaryStructure n)
    (u : UnpairedPosition T) :
    rightEndpointNode? T u.val = none := by
  simp [rightEndpointNode?]

end RNA
