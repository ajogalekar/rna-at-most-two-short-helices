module

public import RNA.Color
public import RNA.IntervalTree

@[expose] public section

set_option autoImplicit false

/-!
# Colourings, exposed multisets, and exact levels

A `Coloring T` has domain `PairedNode T`, so the type itself prevents colours
from being assigned to the virtual root, an unpaired position, or a non-target
arc.  Integer levels are retained as finite ancestor sums.  Reduction modulo
two is confined to `levelParity` and `StrongTwoSeparated`.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- A colour on every, and only, target paired node. -/
abbrev Coloring (T : SecondaryStructure n) := PairedNode T → Color

/-- The multiset of colours on the paired children of an interface. -/
def childColorMultiset (χ : Coloring T) (p : PairedOrRootNode T) : Multiset Color :=
  (pairedChildren T p).val.map χ

@[simp]
theorem childColorMultiset_card (χ : Coloring T) (p : PairedOrRootNode T) :
    (childColorMultiset χ p).card = pairedChildCount T p := by
  simp [childColorMultiset, pairedChildCount]

theorem mem_childColorMultiset_iff (χ : Coloring T)
    (p : PairedOrRootNode T) (c : Color) :
    c ∈ childColorMultiset χ p ↔
      ∃ v ∈ pairedChildren T p, χ v = c := by
  simp [childColorMultiset]

/-- The manuscript exposure at the root or at a nonroot paired node. -/
def exposedMultiset (χ : Coloring T) : PairedOrRootNode T → Multiset Color
  | none => childColorMultiset χ none
  | some p => {Color.inv (χ p)} + childColorMultiset χ (some p)

@[simp]
theorem exposedMultiset_root (χ : Coloring T) :
    exposedMultiset χ none = childColorMultiset χ none := rfl

@[simp]
theorem exposedMultiset_paired (χ : Coloring T) (p : PairedNode T) :
    exposedMultiset χ (some p) = {Color.inv (χ p)} +
      childColorMultiset χ (some p) := rfl

/-- Properness is exactly the componentwise `(1,1,2)` exposure capacity at
every paired node and at the virtual root. -/
def ProperColoring (χ : Coloring T) : Prop :=
  ∀ p : PairedOrRootNode T, ProperExposure (exposedMultiset χ p)

instance (χ : Coloring T) : Decidable (ProperColoring χ) := by
  unfold ProperColoring
  infer_instance

private theorem color_count_sum (X : Multiset Color) :
    X.count Color.black + X.count Color.white + X.count Color.grey = X.card := by
  induction X using Multiset.induction_on with
  | empty => simp
  | cons c X ih =>
      cases c <;> simp_all <;> omega

/-- Any proper exposure of cardinality at least three contains grey. -/
theorem grey_mem_of_properExposure_of_three_le_card (X : Multiset Color)
    (hproper : ProperExposure X) (hcard : 3 ≤ X.card) :
    Color.grey ∈ X := by
  by_contra hgrey
  have hzero : X.count Color.grey = 0 := Multiset.count_eq_zero.mpr hgrey
  have hsum := color_count_sum X
  rcases hproper with ⟨hblack, hwhite, _hgreyCap⟩
  omega

/-- Every proper exposure contains at most four entries. -/
theorem card_le_four_of_properExposure (X : Multiset Color)
    (hproper : ProperExposure X) : X.card ≤ 4 := by
  have hsum := color_count_sum X
  rcases hproper with ⟨hblack, hwhite, hgrey⟩
  omega

/-- Strict paired ancestors of `v`; laminarity makes this the root-to-parent
path, represented without making an arbitrary recursive traversal choice. -/
def pairedAncestors (v : PairedNode T) : Finset (PairedNode T) :=
  Finset.univ.filter (fun p =>
    PairedNode.StrictlyContains T p (Sum.inl v))

/-- Exact integer level at the interface where `v` is entered. -/
def entryLevel (χ : Coloring T) (v : PairedNode T) : Int :=
  ∑ p ∈ pairedAncestors v, Color.delta (χ p)

/-- Exact inclusive integer level of a paired node. -/
def pairedLevel (χ : Coloring T) (v : PairedNode T) : Int :=
  entryLevel χ v + Color.delta (χ v)

/-- The virtual root has integer level zero. -/
def rootLevel (_χ : Coloring T) : Int := 0

/-- Level of a root/paired interface. -/
def interfaceLevel (χ : Coloring T) : PairedOrRootNode T → Int
  | none => 0
  | some p => pairedLevel χ p

/-- An unpaired node has the level of its paired parent, or zero when its
parent is the virtual root. -/
def unpairedLevel (χ : Coloring T) (u : UnpairedPosition T) : Int :=
  interfaceLevel χ (parent T (Sum.inr u))

/-- Level on the complete interval-node type. -/
def nodeLevel (χ : Coloring T) : IntervalNode T → Int
  | none => 0
  | some (Sum.inl p) => pairedLevel χ p
  | some (Sum.inr u) => unpairedLevel χ u

@[simp]
theorem rootLevel_eq_zero (χ : Coloring T) : rootLevel χ = 0 := rfl

@[simp]
theorem pairedLevel_eq_entry_add_delta (χ : Coloring T) (v : PairedNode T) :
    pairedLevel χ v = entryLevel χ v + Color.delta (χ v) := rfl

private theorem strictlyContains_paired_trans
    {a b c : PairedNode T}
    (hab : PairedNode.StrictlyContains T a (Sum.inl b))
    (hbc : PairedNode.StrictlyContains T b (Sum.inl c)) :
    PairedNode.StrictlyContains T a (Sum.inl c) := by
  simp only [PairedNode.StrictlyContains] at hab hbc ⊢
  omega

private theorem pairedAncestors_eq_insert_of_parent
    {v p : PairedNode T} (hp : parent T (Sum.inl v) = some p) :
    pairedAncestors v = insert p (pairedAncestors p) := by
  ext q
  simp only [pairedAncestors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · intro hq
    exact (parent_pair_smallest T hp).2 q hq
  · intro hq
    rcases hq with rfl | hq
    · exact parent_pair_contains T hp
    · exact strictlyContains_paired_trans hq (parent_pair_contains T hp)

private theorem pairedAncestors_eq_empty_of_root
    {v : PairedNode T} (hp : parent T (Sum.inl v) = none) :
    pairedAncestors v = ∅ := by
  ext q
  constructor
  · intro hq
    have hcontains : PairedNode.StrictlyContains T q (Sum.inl v) := by
      simpa [pairedAncestors] using hq
    exact False.elim (((parent_eq_root_iff T (Sum.inl v)).1 hp q) hcontains)
  · simp

/-- The ancestor-sum entry level is exactly the level of the computed paired
parent. -/
theorem entryLevel_eq_parentLevel (χ : Coloring T) {v p : PairedNode T}
    (hp : parent T (Sum.inl v) = some p) :
    entryLevel χ v = pairedLevel χ p := by
  rw [entryLevel, pairedAncestors_eq_insert_of_parent hp]
  have hpnot : p ∉ pairedAncestors p := by
    intro hmem
    have hstrict := (Finset.mem_filter.1 hmem).2
    simp only [PairedNode.StrictlyContains] at hstrict
    omega
  rw [Finset.sum_insert hpnot]
  simp only [pairedLevel, entryLevel]
  omega

/-- A paired child of the root has entry level zero. -/
theorem entryLevel_eq_zero_of_parent_root (χ : Coloring T) {v : PairedNode T}
    (hp : parent T (Sum.inl v) = none) : entryLevel χ v = 0 := by
  rw [entryLevel, pairedAncestors_eq_empty_of_root hp]
  simp

/-- Parent-interface formula for every paired target node. -/
theorem entryLevel_eq_interfaceLevel (χ : Coloring T) (v : PairedNode T) :
    entryLevel χ v = interfaceLevel χ (parent T (Sum.inl v)) := by
  cases hp : parent T (Sum.inl v) with
  | none => simpa [interfaceLevel] using entryLevel_eq_zero_of_parent_root χ hp
  | some p => simpa [interfaceLevel] using entryLevel_eq_parentLevel χ hp

/-- A paired child enters at its paired parent's inclusive level. -/
theorem entryLevel_of_mem_pairedChildren (χ : Coloring T)
    {p v : PairedNode T} (hv : v ∈ pairedChildren T (some p)) :
    entryLevel χ v = pairedLevel χ p := by
  have hp : parent T (Sum.inl v) = some p := by
    simpa [pairedChildren] using hv
  exact entryLevel_eq_parentLevel χ hp

/-- A root paired child enters at level zero. -/
theorem entryLevel_of_mem_rootChildren (χ : Coloring T)
    {v : PairedNode T} (hv : v ∈ pairedChildren T none) :
    entryLevel χ v = 0 := by
  have hp : parent T (Sum.inl v) = none := by
    simpa [pairedChildren] using hv
  exact entryLevel_eq_zero_of_parent_root χ hp

/-- An unpaired child has exactly its stated interface level. -/
theorem unpairedLevel_eq_interface (χ : Coloring T) (u : UnpairedPosition T) :
    unpairedLevel χ u = interfaceLevel χ (parent T (Sum.inr u)) := rfl

theorem unpairedLevel_of_mem_pairedChildren (χ : Coloring T)
    {p : PairedNode T} {u : UnpairedPosition T}
    (hu : u ∈ unpairedChildren T (some p)) :
    unpairedLevel χ u = pairedLevel χ p := by
  have hp : parent T (Sum.inr u) = some p := by
    simpa [unpairedChildren] using hu
  simp [unpairedLevel, interfaceLevel, hp]

theorem unpairedLevel_of_mem_rootChildren (χ : Coloring T)
    {u : UnpairedPosition T} (hu : u ∈ unpairedChildren T none) :
    unpairedLevel χ u = 0 := by
  have hp : parent T (Sum.inr u) = none := by
    simpa [unpairedChildren] using hu
  simp [unpairedLevel, interfaceLevel, hp]

/-- Reduce an exact integer level only when a parity statement is needed. -/
def levelParity (z : Int) : Parity := (z : Parity)

/-- Ordinary separation: grey-pair integer levels and unpaired integer levels
are disjoint. -/
def Separated (χ : Coloring T) : Prop :=
  ∀ g : PairedNode T, χ g = Color.grey →
    ∀ u : UnpairedPosition T, pairedLevel χ g ≠ unpairedLevel χ u

instance (χ : Coloring T) : Decidable (Separated χ) := by
  unfold Separated
  infer_instance

/-- Strong two-separation with unpaired residue `xi` and grey residue
`xi.opposite = xi + 1`.  In particular, when there are no grey nodes the
unpaired-residue clause remains nonvacuous. -/
def StrongTwoSeparated (χ : Coloring T) : Prop :=
  ∃ xi : Parity,
    (∀ u : UnpairedPosition T, levelParity (unpairedLevel χ u) = xi) ∧
    (∀ g : PairedNode T, χ g = Color.grey →
      levelParity (pairedLevel χ g) = xi.opposite)

instance (χ : Coloring T) : Decidable (StrongTwoSeparated χ) := by
  unfold StrongTwoSeparated
  infer_instance

/-- Strong two-separation implies exact integer separation. -/
theorem strongTwoSeparated_implies_separated (χ : Coloring T)
    (hstrong : StrongTwoSeparated χ) : Separated χ := by
  obtain ⟨xi, hunpaired, hgrey⟩ := hstrong
  intro g hg u heq
  have hgr := hgrey g hg
  have hur := hunpaired u
  rw [heq] at hgr
  exact xi.ne_opposite (hur.symm.trans hgr)

end RNA
