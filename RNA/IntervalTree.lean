module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option
public import RNA.Structure

@[expose] public section

set_option autoImplicit false

/-!
# The interval tree derived from a matching

The public target remains `SecondaryStructure`.  This file derives the
manuscript's interval tree from that matching: one node for every target pair,
one node for every target-unpaired position, and a virtual root.  A nonroot
node's parent is the target pair with greatest left endpoint among the pairs
that strictly enclose it; laminarity proves that this is exactly the unique
smallest enclosing interval.
-/

namespace RNA

variable {n : Nat} (T : SecondaryStructure n)

/-- A paired interval-tree node is exactly a target arc. -/
abbrev PairedNode := {a : Arc n // a ∈ T.arcs}

/-- An unpaired interval-tree node is exactly a target-unpaired position. -/
abbrev UnpairedPosition := {i : Fin n // ¬ T.positionPaired i}

/-- Every genuine (nonvirtual) interval-tree node.  The left summand is paired
and the right summand is unpaired. -/
abbrev NonRootNode := PairedNode T ⊕ UnpairedPosition T

/-- All interval-tree nodes.  `none` is the virtual root `[0,n+1]`; a `some`
value is a target pair or target-unpaired singleton. -/
abbrev IntervalNode := Option (NonRootNode T)

/-- Nodes at which paired degree is defined.  `none` is the virtual root and
`some p` is a target paired node. -/
abbrev PairedOrRootNode := Option (PairedNode T)

namespace PairedNode

theorem left_injective :
    Function.Injective (fun p : PairedNode T => p.val.left) := by
  intro a b hleft
  apply Subtype.ext
  exact T.eq_of_mem_of_incident a.property b.property
    a.val.incident_left (Or.inl hleft)

/-- Target paired nodes are ordered by left endpoint.  Partial-matching
endpoint uniqueness makes this key injective. -/
instance instLinearOrder : LinearOrder (PairedNode T) :=
  LinearOrder.lift' (fun p : PairedNode T => p.val.left) (left_injective T)

/-- A target pair strictly contains a nonroot interval-tree node. -/
def StrictlyContains (p : PairedNode T) : NonRootNode T → Prop
  | Sum.inl q => p.val.left < q.val.left ∧ q.val.right < p.val.right
  | Sum.inr u => p.val.left < u.val ∧ u.val < p.val.right

instance instDecidableStrictlyContains (p : PairedNode T) (c : NonRootNode T) :
    Decidable (StrictlyContains T p c) := by
  cases c <;> simp only [StrictlyContains] <;> infer_instance

end PairedNode

namespace NonRootNode

/-- First occupied backbone position, used to order siblings. -/
def start : NonRootNode T → Fin n
  | Sum.inl p => p.val.left
  | Sum.inr u => u.val

theorem start_injective : Function.Injective (start T) := by
  intro x y h
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          exact congrArg Sum.inl (PairedNode.left_injective T h)
      | inr u =>
          exfalso
          change a.val.left = u.val at h
          exact u.property ⟨a.val, a.property, Or.inl h.symm⟩
  | inr u =>
      cases y with
      | inl b =>
          exfalso
          change u.val = b.val.left at h
          exact u.property ⟨b.val, b.property, Or.inl h⟩
      | inr v =>
          exact congrArg Sum.inr (Subtype.ext h)

/-- Nonroot nodes inherit the exact backbone order of their first positions. -/
instance instLinearOrder : LinearOrder (NonRootNode T) :=
  LinearOrder.lift' (start T) (start_injective T)

end NonRootNode

/-- The virtual root node. -/
def IntervalNode.root : IntervalNode T := none

/-- Embed a target pair as an interval-tree node. -/
def IntervalNode.paired (p : PairedNode T) : IntervalNode T := some (Sum.inl p)

/-- Embed a target-unpaired position as an interval-tree node. -/
def IntervalNode.unpaired (u : UnpairedPosition T) : IntervalNode T := some (Sum.inr u)

/-- Every target pair strictly enclosing `c`. -/
def enclosingPairs (c : NonRootNode T) : Finset (PairedNode T) :=
  Finset.univ.filter (fun p => PairedNode.StrictlyContains T p c)

/-- The smallest enclosing target pair, if one exists; otherwise the virtual
root.  Greatest left endpoint is smallest enclosing interval because target
arcs are laminar. -/
def parent (c : NonRootNode T) : PairedOrRootNode T :=
  if h : (enclosingPairs T c).Nonempty then
    some ((enclosingPairs T c).max' h)
  else
    none

/-- Independent mathematical specification of the parent: the root is parent
exactly when no pair encloses the child; a paired parent is an enclosing pair
contained in every other enclosing target interval. -/
def IsParent (p : PairedOrRootNode T) (c : NonRootNode T) : Prop :=
  match p with
  | none =>
      ∀ q : PairedNode T, ¬ PairedNode.StrictlyContains T q c
  | some a =>
      PairedNode.StrictlyContains T a c ∧
        ∀ q : PairedNode T,
          PairedNode.StrictlyContains T q c →
            q = a ∨ PairedNode.StrictlyContains T q (Sum.inl a)

instance instDecidableIsParent (p : PairedOrRootNode T) (c : NonRootNode T) :
    Decidable (IsParent T p c) := by
  cases p <;> simp only [IsParent] <;> infer_instance

/-- Distinct target pairs are disjoint or strictly nested.  This is the
laminarity fact obtained from partial matching plus noncrossingness. -/
theorem pairedNode_laminar (a b : PairedNode T) :
    a = b ∨
      a.val.right < b.val.left ∨
      b.val.right < a.val.left ∨
      (a.val.left < b.val.left ∧ b.val.right < a.val.right) ∨
      (b.val.left < a.val.left ∧ a.val.right < b.val.right) := by
  by_cases hab : a = b
  · exact Or.inl hab
  · right
    have hll : a.val.left ≠ b.val.left := by
      intro h
      apply hab
      apply Subtype.ext
      exact T.eq_of_mem_of_incident a.property b.property
        a.val.incident_left (Or.inl h)
    have hlr : a.val.left ≠ b.val.right := by
      intro h
      have hab' := T.eq_of_mem_of_incident a.property b.property
        a.val.incident_left (Or.inr h)
      exact hab (Subtype.ext hab')
    have hrl : a.val.right ≠ b.val.left := by
      intro h
      have hab' := T.eq_of_mem_of_incident a.property b.property
        a.val.incident_right (Or.inl h)
      exact hab (Subtype.ext hab')
    have hrr : a.val.right ≠ b.val.right := by
      intro h
      have hab' := T.eq_of_mem_of_incident a.property b.property
        a.val.incident_right (Or.inr h)
      exact hab (Subtype.ext hab')
    have hnc := T.not_crossing a.property b.property
    unfold Arc.Crosses at hnc
    have ha := a.val.ordered
    have hb := b.val.ordered
    omega

/-- Two target pairs enclosing the same node are themselves nested. -/
theorem enclosingPairs_nested (c : NonRootNode T) (a b : PairedNode T)
    (ha : PairedNode.StrictlyContains T a c)
    (hb : PairedNode.StrictlyContains T b c) :
    a = b ∨
      PairedNode.StrictlyContains T a (Sum.inl b) ∨
      PairedNode.StrictlyContains T b (Sum.inl a) := by
  have hlam := pairedNode_laminar T a b
  cases c with
  | inl c =>
      have hc := c.val.ordered
      simp only [PairedNode.StrictlyContains] at ha hb ⊢
      rcases hlam with hab | hd₁ | hd₂ | hn₁ | hn₂
      · exact Or.inl hab
      · omega
      · omega
      · exact Or.inr (Or.inl hn₁)
      · exact Or.inr (Or.inr hn₂)
  | inr u =>
      simp only [PairedNode.StrictlyContains] at ha hb ⊢
      rcases hlam with hab | hd₁ | hd₂ | hn₁ | hn₂
      · exact Or.inl hab
      · omega
      · omega
      · exact Or.inr (Or.inl hn₁)
      · exact Or.inr (Or.inr hn₂)

/-- The parent is the root exactly when no target pair encloses the node. -/
theorem parent_eq_root_iff (c : NonRootNode T) :
    parent T c = none ↔
      ∀ p : PairedNode T, ¬ PairedNode.StrictlyContains T p c := by
  unfold parent
  split
  · rename_i h
    constructor
    · intro hnone
      simp at hnone
    · intro hall
      obtain ⟨p, hp⟩ := h
      have hp' : PairedNode.StrictlyContains T p c := by
        simpa [enclosingPairs] using hp
      exact False.elim (hall p hp')
  · rename_i h
    constructor
    · intro _ p hp
      apply h
      exact ⟨p, by simpa [enclosingPairs] using hp⟩
    · intro _
      rfl

/-- A paired value returned by `parent` really is a target pair that strictly
encloses the child. -/
theorem parent_pair_contains {c : NonRootNode T} {p : PairedNode T}
    (hparent : parent T c = some p) :
    PairedNode.StrictlyContains T p c := by
  unfold parent at hparent
  split at hparent
  · rename_i h
    have hm := Finset.max'_mem (enclosingPairs T c) h
    have heq : (enclosingPairs T c).max' h = p := Option.some.inj hparent
    rw [heq] at hm
    simpa [enclosingPairs] using hm
  · simp at hparent

/-- Every enclosing pair starts no later than the paired parent. -/
theorem enclosing_left_le_parent {c : NonRootNode T} {p : PairedNode T}
    (hparent : parent T c = some p) (q : PairedNode T)
    (hq : PairedNode.StrictlyContains T q c) :
    q.val.left ≤ p.val.left := by
  unfold parent at hparent
  split at hparent
  · rename_i h
    have hqmem : q ∈ enclosingPairs T c := by
      simpa [enclosingPairs] using hq
    have hle := Finset.le_max' (enclosingPairs T c) q hqmem
    have heq : (enclosingPairs T c).max' h = p := Option.some.inj hparent
    rw [heq] at hle
    exact hle
  · simp at hparent

/-- A paired parent is the unique smallest enclosing paired interval: every
other enclosing target pair is equal to it or strictly contains it. -/
theorem parent_pair_smallest {c : NonRootNode T} {p : PairedNode T}
    (hparent : parent T c = some p) :
    PairedNode.StrictlyContains T p c ∧
      ∀ q : PairedNode T,
        PairedNode.StrictlyContains T q c →
          q = p ∨ PairedNode.StrictlyContains T q (Sum.inl p) := by
  refine ⟨parent_pair_contains T hparent, ?_⟩
  intro q hq
  have hp := parent_pair_contains T hparent
  have hnested := enclosingPairs_nested T c q p hq hp
  rcases hnested with hqp | hqContains | hpContains
  · exact Or.inl hqp
  · exact Or.inr hqContains
  · have hle := enclosing_left_le_parent T hparent q hq
    simp only [PairedNode.StrictlyContains] at hpContains
    omega

/-- The executable parent satisfies the independent smallest-encloser
specification. -/
theorem parent_isParent (c : NonRootNode T) :
    IsParent T (parent T c) c := by
  cases hparent : parent T c with
  | none =>
      simpa [IsParent] using (parent_eq_root_iff T c).1 hparent
  | some p =>
      simpa [IsParent] using parent_pair_smallest T hparent

/-- The independent smallest-encloser specification has at most one solution. -/
theorem isParent_unique {c : NonRootNode T} {p q : PairedOrRootNode T}
    (hp : IsParent T p c) (hq : IsParent T q c) : p = q := by
  cases p with
  | none =>
      cases q with
      | none => rfl
      | some b =>
          simp only [IsParent] at hp hq
          exact False.elim (hp b hq.1)
  | some a =>
      cases q with
      | none =>
          simp only [IsParent] at hp hq
          exact False.elim (hq a hp.1)
      | some b =>
          simp only [IsParent] at hp hq
          rcases hp.2 b hq.1 with hba | hbContains
          · subst b
            rfl
          · rcases hq.2 a hp.1 with hab | haContains
            · subst b
              rfl
            · simp only [PairedNode.StrictlyContains] at hbContains haContains
              omega

/-- The computed equality and independent parent specification coincide. -/
theorem parent_eq_iff_isParent (c : NonRootNode T) (p : PairedOrRootNode T) :
    parent T c = p ↔ IsParent T p c := by
  constructor
  · intro h
    rw [← h]
    exact parent_isParent T c
  · intro hp
    exact (isParent_unique T hp (parent_isParent T c)).symm

/-- Every nonroot node has exactly one mathematically specified parent, which
is necessarily the value returned by `parent`. -/
theorem parent_wellDefined_unique (c : NonRootNode T) :
    ∃! p : PairedOrRootNode T, IsParent T p c := by
  refine ⟨parent T c, parent_isParent T c, ?_⟩
  intro p hp
  exact isParent_unique T hp (parent_isParent T c)

/-- Paired children of a paired node or the virtual root. -/
def pairedChildren (p : PairedOrRootNode T) : Finset (PairedNode T) :=
  Finset.univ.filter (fun c => parent T (Sum.inl c) = p)

/-- Unpaired singleton children of a paired node or the virtual root. -/
def unpairedChildren (p : PairedOrRootNode T) : Finset (UnpairedPosition T) :=
  Finset.univ.filter (fun c => parent T (Sum.inr c) = p)

/-- All children, without changing their paired/unpaired tags. -/
def children (p : PairedOrRootNode T) : Finset (NonRootNode T) :=
  Finset.univ.filter (fun c => parent T c = p)

/-- Children in increasing backbone order. -/
def orderedChildren (p : PairedOrRootNode T) : List (NonRootNode T) :=
  (children T p).sort

theorem orderedChildren_sorted (p : PairedOrRootNode T) :
    (orderedChildren T p).SortedLT := by
  exact Finset.sortedLT_sort (children T p)

/-- The number of paired children.  Unpaired children do not contribute. -/
def pairedChildCount (p : PairedOrRootNode T) : Nat :=
  (pairedChildren T p).card

/-- Manuscript paired degree: root degree counts paired children only; a
nonroot paired node also has one paired incidence to its parent. -/
def pairedDegree : PairedOrRootNode T → Nat
  | none => pairedChildCount T none
  | some p => 1 + pairedChildCount T (some p)

end RNA
