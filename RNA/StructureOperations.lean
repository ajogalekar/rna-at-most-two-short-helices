module

public import Mathlib.Data.Fin.Tuple.Basic
public import RNA.MatchingPartner
public import RNA.Saturable
public import RNA.StructureTransport

@[expose] public section

set_option autoImplicit false

/-!
# Structural operations on consecutive RNA backbones

This module supplies the exact constructors used by the atomic-word proof:
disjoint concatenation, wrapping by one outer pair, and restriction to
order-convex intervals.
-/

namespace RNA

variable {m n : Nat}

namespace Fin

/-- The first block in a backbone of length `m + n`. -/
abbrev leftBlockOrderEmbedding (m n : Nat) : Fin m ↪o Fin (m + n) :=
  Fin.castAddOrderEmb n

/-- The second block in a backbone of length `m + n`. -/
abbrev rightBlockOrderEmbedding (m n : Nat) : Fin n ↪o Fin (m + n) :=
  Fin.natAddOrderEmb m

@[simp]
theorem leftBlockOrderEmbedding_val (i : Fin m) :
    (leftBlockOrderEmbedding m n i).val = i.val := rfl

@[simp]
theorem rightBlockOrderEmbedding_val (i : Fin n) :
    (rightBlockOrderEmbedding m n i).val = m + i.val := rfl

/-- The first word block, with the list-length equality built into the
codomain. -/
def appendLeftOrderEmbedding (x y : Word) :
    Fin x.length ↪o Fin (x ++ y).length :=
  (leftBlockOrderEmbedding x.length y.length).trans
    (Fin.castOrderIso (by simp)).toOrderEmbedding

/-- The second word block, with the list-length equality built into the
codomain. -/
def appendRightOrderEmbedding (x y : Word) :
    Fin y.length ↪o Fin (x ++ y).length :=
  (rightBlockOrderEmbedding x.length y.length).trans
    (Fin.castOrderIso (by simp)).toOrderEmbedding

@[simp]
theorem appendLeftOrderEmbedding_val (x y : Word) (i : Fin x.length) :
    (appendLeftOrderEmbedding x y i).val = i.val := rfl

@[simp]
theorem appendRightOrderEmbedding_val (x y : Word) (i : Fin y.length) :
    (appendRightOrderEmbedding x y i).val = x.length + i.val := rfl

/-- Insert one new position on either side of an `n`-position backbone. -/
def interiorOrderEmbedding (n : Nat) : Fin n ↪o Fin (n + 2) :=
  OrderEmbedding.ofStrictMono
    (fun i : Fin n => ⟨i.val + 1, by omega⟩)
    (by intro i j hij; simp only [Fin.mk_lt_mk] at hij ⊢; omega)

@[simp]
theorem interiorOrderEmbedding_val (i : Fin n) :
    (interiorOrderEmbedding n i).val = i.val + 1 := rfl

/-- The old positions inside a wrapped word, with its list-length equality
built into the codomain. -/
def wrapInteriorOrderEmbedding (a b : Nucleotide) (z : Word) :
    Fin z.length ↪o Fin (Word.wrap a b z).length :=
  (interiorOrderEmbedding z.length).trans
    (Fin.castOrderIso (Word.length_wrap a b z).symm).toOrderEmbedding

@[simp]
theorem wrapInteriorOrderEmbedding_val (a b : Nucleotide) (z : Word)
    (i : Fin z.length) :
    (wrapInteriorOrderEmbedding a b z i).val = i.val + 1 := rfl

/-- The order embedding of a consecutive half-open interval
`[start, start + len)` into a finite backbone. -/
def intervalOrderEmbedding (start len total : Nat)
    (h : start + len ≤ total) : Fin len ↪o Fin total :=
  OrderEmbedding.ofStrictMono
    (fun i : Fin len => ⟨start + i.val, by omega⟩)
    (by intro i j hij; simp only [Fin.mk_lt_mk] at hij ⊢; omega)

@[simp]
theorem intervalOrderEmbedding_val (start len total : Nat)
    (h : start + len ≤ total) (i : Fin len) :
    (intervalOrderEmbedding start len total h i).val = start + i.val := rfl

theorem exists_intervalOrderEmbedding_eq_iff (start len total : Nat)
    (h : start + len ≤ total) (j : Fin total) :
    (∃ i : Fin len, intervalOrderEmbedding start len total h i = j) ↔
      start ≤ j.val ∧ j.val < start + len := by
  constructor
  · rintro ⟨i, rfl⟩
    simp only [intervalOrderEmbedding_val]
    exact ⟨Nat.le_add_right _ _, by have hi := i.isLt; omega⟩
  · rintro ⟨hleft, hright⟩
    let i : Fin len := ⟨j.val - start, by omega⟩
    refine ⟨i, Fin.ext ?_⟩
    simp only [intervalOrderEmbedding_val, i]
    omega

end Fin

namespace Arc

private theorem left_right_not_shareEndpoint
    (a : Arc m) (b : Arc n) :
    ¬ (a.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n)).ShareEndpoint
      (b.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n)) := by
  rintro ⟨p, hp, hq⟩
  rcases hp with hp | hp <;> rcases hq with hq | hq
  all_goals
    have hpval := congrArg Fin.val hp
    have hqval := congrArg Fin.val hq
    simp only [mapOrderEmbedding_left, mapOrderEmbedding_right,
      Fin.leftBlockOrderEmbedding_val,
      Fin.rightBlockOrderEmbedding_val] at hpval hqval
    omega

private theorem left_right_not_crosses
    (a : Arc m) (b : Arc n) :
    ¬ (a.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n)).Crosses
      (b.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n)) := by
  intro h
  change
    (a.left.val < m + b.left.val ∧
        m + b.left.val < a.right.val ∧
        a.right.val < m + b.right.val) ∨
      (m + b.left.val < a.left.val ∧
        a.left.val < m + b.right.val ∧
        m + b.right.val < a.right.val) at h
  have hal := a.left.isLt
  have har := a.right.isLt
  omega

private theorem rightBlock_not_incident_leftPosition
    (b : Arc n) (i : Fin m) :
    ¬ (b.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n)).Incident
      (Fin.castAdd n i) := by
  intro h
  rcases h with h | h
  all_goals
    have hval := congrArg Fin.val h
    simp only [mapOrderEmbedding_left, mapOrderEmbedding_right,
      Fin.val_castAdd, Fin.rightBlockOrderEmbedding_val] at hval
    have hi := i.isLt
    omega

private theorem leftBlock_not_incident_rightPosition
    (a : Arc m) (i : Fin n) :
    ¬ (a.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n)).Incident
      (Fin.natAdd m i) := by
  intro h
  rcases h with h | h
  all_goals
    have hval := congrArg Fin.val h
    simp only [mapOrderEmbedding_left, mapOrderEmbedding_right,
      Fin.val_natAdd, Fin.leftBlockOrderEmbedding_val] at hval
    have hal := a.left.isLt
    have har := a.right.isLt
    omega

/-- The positional outer arc on a backbone with `n` interior positions. -/
def outer (n : Nat) : Arc (n + 2) where
  left := (⟨0, by omega⟩ : Fin (n + 2))
  right := (⟨n + 1, by omega⟩ : Fin (n + 2))
  ordered := by simp only [Fin.mk_lt_mk]; omega

@[simp]
theorem outer_left_val (n : Nat) : (outer n).left.val = 0 := rfl

@[simp]
theorem outer_right_val (n : Nat) : (outer n).right.val = n + 1 := rfl

/-- The positional outer arc, reindexed to the list length of a wrapped
word. -/
def wrapWordOuter (a b : Nucleotide) (z : Word) :
    Arc (Word.wrap a b z).length :=
  (outer z.length).mapOrderEmbedding
    (Fin.castOrderIso (Word.length_wrap a b z).symm).toOrderEmbedding

@[simp]
theorem wrapWordOuter_left_val (a b : Nucleotide) (z : Word) :
    (wrapWordOuter a b z).left.val = 0 := rfl

@[simp]
theorem wrapWordOuter_right_val (a b : Nucleotide) (z : Word) :
    (wrapWordOuter a b z).right.val = z.length + 1 := rfl

private theorem outer_not_shareEndpoint_interior (a : Arc n) :
    ¬ (outer n).ShareEndpoint
      (a.mapOrderEmbedding (Fin.interiorOrderEmbedding n)) := by
  rintro ⟨p, hp, hq⟩
  rcases hp with hp | hp <;> rcases hq with hq | hq
  all_goals
    have hpval := congrArg Fin.val hp
    have hqval := congrArg Fin.val hq
    simp only [outer_left_val, outer_right_val, mapOrderEmbedding_left,
      mapOrderEmbedding_right, Fin.interiorOrderEmbedding_val] at hpval hqval
    have hal := a.left.isLt
    have har := a.right.isLt
    omega

private theorem outer_not_crosses_interior (a : Arc n) :
    ¬ (outer n).Crosses
      (a.mapOrderEmbedding (Fin.interiorOrderEmbedding n)) := by
  intro h
  change
    (0 < a.left.val + 1 ∧
        a.left.val + 1 < n + 1 ∧
        n + 1 < a.right.val + 1) ∨
      (a.left.val + 1 < 0 ∧
        0 < a.right.val + 1 ∧
        a.right.val + 1 < n + 1) at h
  have hal := a.left.isLt
  have har := a.right.isLt
  omega

private theorem outer_not_incident_interiorPosition (i : Fin n) :
    ¬ (outer n).Incident (Fin.interiorOrderEmbedding n i) := by
  intro h
  rcases h with h | h
  all_goals
    have hval := congrArg Fin.val h
    simp only [outer_left_val, outer_right_val,
      Fin.interiorOrderEmbedding_val] at hval
    have hi := i.isLt
    omega

/-! Consecutive intervals determined by an arc. -/

/-- Number of positions strictly between the endpoints of an arc. -/
def openLength (a : Arc n) : Nat := a.right.val - a.left.val - 1

/-- Number of positions from the left endpoint through the right endpoint. -/
def closedLength (a : Arc n) : Nat := a.right.val - a.left.val + 1

/-- Strict positional membership between the endpoints of an arc. -/
def PositionInOpenInterval (a : Arc n) (i : Fin n) : Prop :=
  a.left < i ∧ i < a.right

/-- Positional membership in the inclusive interval of an arc. -/
def PositionInClosedInterval (a : Arc n) (i : Fin n) : Prop :=
  a.left ≤ i ∧ i ≤ a.right

/-- The consecutive positions strictly enclosed by an arc. -/
def openIntervalOrderEmbedding (a : Arc n) : Fin a.openLength ↪o Fin n :=
  Fin.intervalOrderEmbedding (a.left.val + 1) a.openLength n (by
    have horder := a.ordered
    have hright := a.right.isLt
    change a.left.val < a.right.val at horder
    change a.right.val < n at hright
    change a.left.val + 1 + a.openLength ≤ n
    unfold openLength
    omega)

/-- The consecutive positions from an arc's left endpoint through its right
endpoint. -/
def closedIntervalOrderEmbedding (a : Arc n) : Fin a.closedLength ↪o Fin n :=
  Fin.intervalOrderEmbedding a.left.val a.closedLength n (by
    have horder := a.ordered
    have hright := a.right.isLt
    change a.left.val < a.right.val at horder
    change a.right.val < n at hright
    change a.left.val + a.closedLength ≤ n
    unfold closedLength
    omega)

@[simp]
theorem openIntervalOrderEmbedding_val (a : Arc n) (i : Fin a.openLength) :
    (a.openIntervalOrderEmbedding i).val = a.left.val + 1 + i.val := rfl

@[simp]
theorem closedIntervalOrderEmbedding_val (a : Arc n)
    (i : Fin a.closedLength) :
    (a.closedIntervalOrderEmbedding i).val = a.left.val + i.val := rfl

theorem exists_openIntervalOrderEmbedding_eq_iff (a : Arc n) (j : Fin n) :
    (∃ i : Fin a.openLength, a.openIntervalOrderEmbedding i = j) ↔
      a.PositionInOpenInterval j := by
  constructor
  · rintro ⟨i, hi⟩
    have hival := congrArg Fin.val hi
    simp only [openIntervalOrderEmbedding_val] at hival
    unfold PositionInOpenInterval
    change a.left.val < j.val ∧ j.val < a.right.val
    have hii := i.isLt
    unfold openLength at hii
    have horder := a.ordered
    change a.left.val < a.right.val at horder
    omega
  · intro hj
    unfold PositionInOpenInterval at hj
    change a.left.val < j.val ∧ j.val < a.right.val at hj
    let i : Fin a.openLength := ⟨j.val - a.left.val - 1, by
      unfold openLength
      omega⟩
    refine ⟨i, Fin.ext ?_⟩
    simp only [openIntervalOrderEmbedding_val, i]
    omega

theorem exists_closedIntervalOrderEmbedding_eq_iff (a : Arc n) (j : Fin n) :
    (∃ i : Fin a.closedLength, a.closedIntervalOrderEmbedding i = j) ↔
      a.PositionInClosedInterval j := by
  constructor
  · rintro ⟨i, hi⟩
    have hival := congrArg Fin.val hi
    simp only [closedIntervalOrderEmbedding_val] at hival
    unfold PositionInClosedInterval
    change a.left.val ≤ j.val ∧ j.val ≤ a.right.val
    have hii := i.isLt
    unfold closedLength at hii
    have horder := a.ordered
    change a.left.val < a.right.val at horder
    omega
  · intro hj
    unfold PositionInClosedInterval at hj
    change a.left.val ≤ j.val ∧ j.val ≤ a.right.val at hj
    let i : Fin a.closedLength := ⟨j.val - a.left.val, by
      unfold closedLength
      omega⟩
    refine ⟨i, Fin.ext ?_⟩
    simp only [closedIntervalOrderEmbedding_val, i]
    omega

end Arc

namespace SecondaryStructure

/-! ## Consecutive concatenation -/

/-- Concatenate two structures on consecutive backbone blocks. -/
def appendConsecutive (S : SecondaryStructure m) (T : SecondaryStructure n) :
    SecondaryStructure (m + n) where
  arcs :=
    (S.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n)).arcs ∪
      (T.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n)).arcs
  isPartialMatching := by
    intro a ha b hb hshare
    simp only [Finset.mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (S.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n)).isPartialMatching
        ha hb hshare
    · obtain ⟨a₀, ha₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.leftBlockOrderEmbedding m n) S a).1 ha
      obtain ⟨b₀, hb₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.rightBlockOrderEmbedding m n) T b).1 hb
      exact False.elim (Arc.left_right_not_shareEndpoint a₀ b₀ hshare)
    · obtain ⟨a₀, ha₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.rightBlockOrderEmbedding m n) T a).1 ha
      obtain ⟨b₀, hb₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.leftBlockOrderEmbedding m n) S b).1 hb
      exact False.elim (Arc.left_right_not_shareEndpoint b₀ a₀
        ((Arc.shareEndpoint_symm).2 hshare))
    · exact (T.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n)).isPartialMatching
        ha hb hshare
  isNoncrossing := by
    intro a ha b hb hcross
    simp only [Finset.mem_union] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (S.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n)).isNoncrossing
        ha hb hcross
    · obtain ⟨a₀, ha₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.leftBlockOrderEmbedding m n) S a).1 ha
      obtain ⟨b₀, hb₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.rightBlockOrderEmbedding m n) T b).1 hb
      exact Arc.left_right_not_crosses a₀ b₀ hcross
    · obtain ⟨a₀, ha₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.rightBlockOrderEmbedding m n) T a).1 ha
      obtain ⟨b₀, hb₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.leftBlockOrderEmbedding m n) S b).1 hb
      exact Arc.left_right_not_crosses b₀ a₀
        ((Arc.crosses_symm).2 hcross)
    · exact (T.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n)).isNoncrossing
        ha hb hcross

theorem mem_appendConsecutive_iff (S : SecondaryStructure m)
    (T : SecondaryStructure n) (a : Arc (m + n)) :
    a ∈ (appendConsecutive S T).arcs ↔
      (∃ b ∈ S.arcs,
        b.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n) = a) ∨
      (∃ c ∈ T.arcs,
        c.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n) = a) := by
  simp only [appendConsecutive, Finset.mem_union, mem_mapOrderEmbedding_iff]

@[simp]
theorem left_mem_appendConsecutive_iff (S : SecondaryStructure m)
    (T : SecondaryStructure n) (a : Arc m) :
    a.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n) ∈
        (appendConsecutive S T).arcs ↔ a ∈ S.arcs := by
  constructor
  · intro h
    rcases (mem_appendConsecutive_iff S T _).1 h with h | h
    · obtain ⟨b, hb, heq⟩ := h
      exact (Arc.mapOrderEmbedding_injective _ heq).symm ▸ hb
    · obtain ⟨b, hb, heq⟩ := h
      exfalso
      apply Arc.left_right_not_shareEndpoint a b
      rw [heq]
      exact (a.mapOrderEmbedding _).shareEndpoint_self
  · intro ha
    exact (mem_appendConsecutive_iff S T _).2
      (Or.inl ⟨a, ha, rfl⟩)

@[simp]
theorem right_mem_appendConsecutive_iff (S : SecondaryStructure m)
    (T : SecondaryStructure n) (a : Arc n) :
    a.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n) ∈
        (appendConsecutive S T).arcs ↔ a ∈ T.arcs := by
  constructor
  · intro h
    rcases (mem_appendConsecutive_iff S T _).1 h with h | h
    · obtain ⟨b, hb, heq⟩ := h
      exfalso
      apply Arc.left_right_not_shareEndpoint b a
      rw [heq]
      exact (a.mapOrderEmbedding _).shareEndpoint_self
    · obtain ⟨b, hb, heq⟩ := h
      exact (Arc.mapOrderEmbedding_injective _ heq).symm ▸ hb
  · intro ha
    exact (mem_appendConsecutive_iff S T _).2
      (Or.inr ⟨a, ha, rfl⟩)

private theorem appendConsecutive_arcFinsets_disjoint
    (S : SecondaryStructure m) (T : SecondaryStructure n) :
    Disjoint
      (S.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n)).arcs
      (T.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n)).arcs := by
  rw [Finset.disjoint_left]
  intro a haS haT
  obtain ⟨b, hb, rfl⟩ :=
    (mem_mapOrderEmbedding_iff (Fin.leftBlockOrderEmbedding m n) S a).1 haS
  obtain ⟨c, hc, heq⟩ :=
    (mem_mapOrderEmbedding_iff (Fin.rightBlockOrderEmbedding m n) T _).1 haT
  exact Arc.left_right_not_shareEndpoint b c
    (by rw [heq]; exact (b.mapOrderEmbedding _).shareEndpoint_self)

@[simp]
theorem pairCount_appendConsecutive (S : SecondaryStructure m)
    (T : SecondaryStructure n) :
    pairCount (appendConsecutive S T) = pairCount S + pairCount T := by
  unfold pairCount
  change
    ((S.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n)).arcs ∪
      (T.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n)).arcs).card =
        S.arcs.card + T.arcs.card
  rw [Finset.card_union_of_disjoint (appendConsecutive_arcFinsets_disjoint S T)]
  simp [SecondaryStructure.mapOrderEmbedding]

theorem structureCompatible_appendConsecutive_iff
    (S : SecondaryStructure m) (T : SecondaryStructure n)
    (w : Sequence (m + n)) :
    StructureCompatible w (appendConsecutive S T) ↔
      StructureCompatible (fun i => w (Fin.castAdd n i)) S ∧
      StructureCompatible (fun i => w (Fin.natAdd m i)) T := by
  constructor
  · intro h
    constructor
    · intro a ha
      simpa using h (a.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n))
        ((left_mem_appendConsecutive_iff S T a).2 ha)
    · intro a ha
      simpa using h (a.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n))
        ((right_mem_appendConsecutive_iff S T a).2 ha)
  · rintro ⟨hS, hT⟩ a ha
    rcases (mem_appendConsecutive_iff S T a).1 ha with h | h
    · obtain ⟨b, hb, rfl⟩ := h
      simpa using hS b hb
    · obtain ⟨b, hb, rfl⟩ := h
      simpa using hT b hb

theorem positionPaired_appendConsecutive_left_iff
    (S : SecondaryStructure m) (T : SecondaryStructure n) (i : Fin m) :
    (appendConsecutive S T).positionPaired (Fin.castAdd n i) ↔
      S.positionPaired i := by
  constructor
  · rintro ⟨a, ha, hi⟩
    rcases (mem_appendConsecutive_iff S T a).1 ha with h | h
    · obtain ⟨b, hb, rfl⟩ := h
      exact ⟨b, hb,
        (Arc.mapOrderEmbedding_incident_iff
          (Fin.leftBlockOrderEmbedding m n) b i).1 hi⟩
    · obtain ⟨b, hb, rfl⟩ := h
      exfalso
      exact Arc.rightBlock_not_incident_leftPosition b i hi
  · rintro ⟨a, ha, hi⟩
    exact ⟨a.mapOrderEmbedding (Fin.leftBlockOrderEmbedding m n),
      (left_mem_appendConsecutive_iff S T a).2 ha,
      (Arc.mapOrderEmbedding_incident_iff _ a i).2 hi⟩

theorem positionPaired_appendConsecutive_right_iff
    (S : SecondaryStructure m) (T : SecondaryStructure n) (i : Fin n) :
    (appendConsecutive S T).positionPaired (Fin.natAdd m i) ↔
      T.positionPaired i := by
  constructor
  · rintro ⟨a, ha, hi⟩
    rcases (mem_appendConsecutive_iff S T a).1 ha with h | h
    · obtain ⟨b, hb, rfl⟩ := h
      exfalso
      exact Arc.leftBlock_not_incident_rightPosition b i hi
    · obtain ⟨b, hb, rfl⟩ := h
      exact ⟨b, hb,
        (Arc.mapOrderEmbedding_incident_iff
          (Fin.rightBlockOrderEmbedding m n) b i).1 hi⟩
  · rintro ⟨a, ha, hi⟩
    exact ⟨a.mapOrderEmbedding (Fin.rightBlockOrderEmbedding m n),
      (right_mem_appendConsecutive_iff S T a).2 ha,
      (Arc.mapOrderEmbedding_incident_iff _ a i).2 hi⟩

theorem saturated_appendConsecutive_iff
    (S : SecondaryStructure m) (T : SecondaryStructure n) :
    SaturatedStructure (appendConsecutive S T) ↔
      SaturatedStructure S ∧ SaturatedStructure T := by
  constructor
  · intro h
    exact ⟨fun i => (positionPaired_appendConsecutive_left_iff S T i).1
      (h (Fin.castAdd n i)),
      fun i => (positionPaired_appendConsecutive_right_iff S T i).1
        (h (Fin.natAdd m i))⟩
  · rintro ⟨hS, hT⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact (positionPaired_appendConsecutive_left_iff S T j).2 (hS j)
    · exact (positionPaired_appendConsecutive_right_iff S T j).2 (hT j)

/-! ## Transport of saturation along order isomorphisms -/

theorem positionPaired_reindexOrderIso_iff
    (e : Fin m ≃o Fin n) (S : SecondaryStructure m) (i : Fin m) :
    (S.reindexOrderIso e).positionPaired (e i) ↔ S.positionPaired i := by
  constructor
  · rintro ⟨a, ha, hi⟩
    obtain ⟨b, hb, rfl⟩ :=
      (mem_mapOrderEmbedding_iff e.toOrderEmbedding S a).1 ha
    exact ⟨b, hb, (Arc.mapOrderEmbedding_incident_iff
      e.toOrderEmbedding b i).1 hi⟩
  · rintro ⟨a, ha, hi⟩
    exact ⟨a.mapOrderEmbedding e.toOrderEmbedding,
      (mapOrderEmbedding_mem_iff e.toOrderEmbedding S a).2 ha,
      (Arc.mapOrderEmbedding_incident_iff e.toOrderEmbedding a i).2 hi⟩

theorem saturated_reindexOrderIso_iff
    (e : Fin m ≃o Fin n) (S : SecondaryStructure m) :
    SaturatedStructure (S.reindexOrderIso e) ↔ SaturatedStructure S := by
  constructor
  · intro h i
    exact (positionPaired_reindexOrderIso_iff e S i).1 (h (e i))
  · intro h j
    simpa using
      (positionPaired_reindexOrderIso_iff e S (e.symm j)).2 (h (e.symm j))

/-! ## Partner and saturation pullback -/

/-- Exact partner transport through a pullback.  Unlike mere arc membership,
this records the orientation of the two endpoints as well. -/
theorem positionPartner_pullbackOrderEmbedding_iff
    (e : Fin m ↪o Fin n) (S : SecondaryStructure n) (i j : Fin m) :
    PositionPartner (S.pullbackOrderEmbedding e) i j ↔
      PositionPartner S (e i) (e j) := by
  constructor
  · rintro ⟨a, ha, horder⟩
    refine ⟨a.mapOrderEmbedding e,
      (mem_pullbackOrderEmbedding_iff e S a).1 ha, ?_⟩
    rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro ⟨a, ha, horder⟩
    rcases horder with ⟨hileft, hjright⟩ | ⟨hiright, hjleft⟩
    · have hijMap : e i < e j := by simpa [hileft, hjright] using a.ordered
      let b : Arc m := ⟨i, j, e.lt_iff_lt.mp hijMap⟩
      refine ⟨b, ?_, Or.inl ⟨rfl, rfl⟩⟩
      rw [mem_pullbackOrderEmbedding_iff]
      have hba : b.mapOrderEmbedding e = a := by
        apply Arc.ext
        · exact hileft
        · exact hjright
      rw [hba]
      exact ha
    · have hjiMap : e j < e i := by simpa [hjleft, hiright] using a.ordered
      let b : Arc m := ⟨j, i, e.lt_iff_lt.mp hjiMap⟩
      refine ⟨b, ?_, Or.inr ⟨rfl, rfl⟩⟩
      rw [mem_pullbackOrderEmbedding_iff]
      have hba : b.mapOrderEmbedding e = a := by
        apply Arc.ext
        · exact hjleft
        · exact hiright
      rw [hba]
      exact ha

/-- A saturated structure restricts to a saturated embedded sub-backbone when
that sub-backbone is closed under partners. -/
theorem saturated_pullbackOrderEmbedding_of_partnerClosed
    (e : Fin m ↪o Fin n) (S : SecondaryStructure n)
    (hSat : SaturatedStructure S)
    (hClosed : ∀ (i : Fin m) (j : Fin n),
      PositionPartner S (e i) j → ∃ k : Fin m, e k = j) :
    SaturatedStructure (S.pullbackOrderEmbedding e) := by
  intro i
  obtain ⟨j, hij⟩ := (positionPaired_iff_exists_partner S (e i)).1 (hSat (e i))
  obtain ⟨k, hk⟩ := hClosed i j hij
  apply (positionPaired_iff_exists_partner (S.pullbackOrderEmbedding e) i).2
  refine ⟨k, (positionPartner_pullbackOrderEmbedding_iff e S i k).2 ?_⟩
  simpa [hk] using hij

/-! ## Word-indexed consecutive concatenation -/

/-- Concatenate structures indexed by the two words.  The harmless order
isomorphism accounts for the definitional presentation of list length. -/
def appendWords (x y : Word)
    (S : SecondaryStructure x.length) (T : SecondaryStructure y.length) :
    SecondaryStructure (x ++ y).length :=
  (appendConsecutive S T).reindexOrderIso
    (Fin.castOrderIso (by simp))

theorem mem_appendWords_iff (x y : Word)
    (S : SecondaryStructure x.length) (T : SecondaryStructure y.length)
    (a : Arc (x ++ y).length) :
    a ∈ (appendWords x y S T).arcs ↔
      (∃ b ∈ S.arcs,
        b.mapOrderEmbedding (Fin.appendLeftOrderEmbedding x y) = a) ∨
      (∃ c ∈ T.arcs,
        c.mapOrderEmbedding (Fin.appendRightOrderEmbedding x y) = a) := by
  constructor
  · intro ha
    obtain ⟨d, hd, rfl⟩ :=
      (mem_mapOrderEmbedding_iff
        (Fin.castOrderIso (by simp)).toOrderEmbedding
        (appendConsecutive S T) a).1 ha
    rcases (mem_appendConsecutive_iff S T d).1 hd with h | h
    · obtain ⟨b, hb, rfl⟩ := h
      exact Or.inl ⟨b, hb, rfl⟩
    · obtain ⟨c, hc, rfl⟩ := h
      exact Or.inr ⟨c, hc, rfl⟩
  · intro ha
    rcases ha with h | h
    · obtain ⟨b, hb, rfl⟩ := h
      change
        (b.mapOrderEmbedding
          (Fin.leftBlockOrderEmbedding x.length y.length)).mapOrderEmbedding
            (Fin.castOrderIso (by simp)).toOrderEmbedding ∈
          ((appendConsecutive S T).mapOrderEmbedding
            (Fin.castOrderIso (by simp)).toOrderEmbedding).arcs
      apply (mapOrderEmbedding_mem_iff
        (Fin.castOrderIso (by simp)).toOrderEmbedding
        (appendConsecutive S T) _).2
      exact (left_mem_appendConsecutive_iff S T b).2 hb
    · obtain ⟨c, hc, rfl⟩ := h
      change
        (c.mapOrderEmbedding
          (Fin.rightBlockOrderEmbedding x.length y.length)).mapOrderEmbedding
            (Fin.castOrderIso (by simp)).toOrderEmbedding ∈
          ((appendConsecutive S T).mapOrderEmbedding
            (Fin.castOrderIso (by simp)).toOrderEmbedding).arcs
      apply (mapOrderEmbedding_mem_iff
        (Fin.castOrderIso (by simp)).toOrderEmbedding
        (appendConsecutive S T) _).2
      exact (right_mem_appendConsecutive_iff S T c).2 hc

@[simp]
theorem left_mem_appendWords_iff (x y : Word)
    (S : SecondaryStructure x.length) (T : SecondaryStructure y.length)
    (a : Arc x.length) :
    a.mapOrderEmbedding (Fin.appendLeftOrderEmbedding x y) ∈
        (appendWords x y S T).arcs ↔ a ∈ S.arcs := by
  change
    (a.mapOrderEmbedding (Fin.leftBlockOrderEmbedding x.length y.length)).mapOrderEmbedding
        (Fin.castOrderIso (by simp)).toOrderEmbedding ∈
      ((appendConsecutive S T).mapOrderEmbedding
        (Fin.castOrderIso (by simp)).toOrderEmbedding).arcs ↔ a ∈ S.arcs
  rw [mapOrderEmbedding_mem_iff, left_mem_appendConsecutive_iff]

@[simp]
theorem right_mem_appendWords_iff (x y : Word)
    (S : SecondaryStructure x.length) (T : SecondaryStructure y.length)
    (a : Arc y.length) :
    a.mapOrderEmbedding (Fin.appendRightOrderEmbedding x y) ∈
        (appendWords x y S T).arcs ↔ a ∈ T.arcs := by
  change
    (a.mapOrderEmbedding (Fin.rightBlockOrderEmbedding x.length y.length)).mapOrderEmbedding
        (Fin.castOrderIso (by simp)).toOrderEmbedding ∈
      ((appendConsecutive S T).mapOrderEmbedding
        (Fin.castOrderIso (by simp)).toOrderEmbedding).arcs ↔ a ∈ T.arcs
  rw [mapOrderEmbedding_mem_iff, right_mem_appendConsecutive_iff]

@[simp]
theorem pairCount_appendWords (x y : Word)
    (S : SecondaryStructure x.length) (T : SecondaryStructure y.length) :
    pairCount (appendWords x y S T) = pairCount S + pairCount T := by
  simp [appendWords]

theorem structureCompatible_appendWords_iff (x y : Word)
    (S : SecondaryStructure x.length) (T : SecondaryStructure y.length) :
    StructureCompatible (x ++ y).toSequence (appendWords x y S T) ↔
      StructureCompatible x.toSequence S ∧
        StructureCompatible y.toSequence T := by
  rw [appendWords, structureCompatible_reindexOrderIso_iff,
    structureCompatible_appendConsecutive_iff]
  constructor <;> rintro ⟨hS, hT⟩ <;> constructor
  · intro a ha
    simpa using hS a ha
  · intro a ha
    simpa using hT a ha
  · intro a ha
    simpa using hS a ha
  · intro a ha
    simpa using hT a ha

@[simp]
theorem saturated_appendWords_iff (x y : Word)
    (S : SecondaryStructure x.length) (T : SecondaryStructure y.length) :
    SaturatedStructure (appendWords x y S T) ↔
      SaturatedStructure S ∧ SaturatedStructure T := by
  rw [appendWords, saturated_reindexOrderIso_iff,
    saturated_appendConsecutive_iff]

/-! ## Wrapping by a complementary outer pair -/

/-- Insert one new position at either end and add the positional outer arc. -/
def wrapOuter (S : SecondaryStructure n) : SecondaryStructure (n + 2) where
  arcs := insert (Arc.outer n)
    (S.mapOrderEmbedding (Fin.interiorOrderEmbedding n)).arcs
  isPartialMatching := by
    intro a ha b hb hshare
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · obtain ⟨b₀, hb₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.interiorOrderEmbedding n) S b).1 hb
      exact False.elim (Arc.outer_not_shareEndpoint_interior b₀ hshare)
    · obtain ⟨a₀, ha₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.interiorOrderEmbedding n) S a).1 ha
      exact False.elim (Arc.outer_not_shareEndpoint_interior a₀
        ((Arc.shareEndpoint_symm).2 hshare))
    · exact (S.mapOrderEmbedding
        (Fin.interiorOrderEmbedding n)).isPartialMatching ha hb hshare
  isNoncrossing := by
    intro a ha b hb hcross
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact (Arc.not_crosses_self (Arc.outer n)) hcross
    · obtain ⟨b₀, hb₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.interiorOrderEmbedding n) S b).1 hb
      exact Arc.outer_not_crosses_interior b₀ hcross
    · obtain ⟨a₀, ha₀, rfl⟩ :=
        (mem_mapOrderEmbedding_iff (Fin.interiorOrderEmbedding n) S a).1 ha
      exact Arc.outer_not_crosses_interior a₀
        ((Arc.crosses_symm).2 hcross)
    · exact (S.mapOrderEmbedding
        (Fin.interiorOrderEmbedding n)).isNoncrossing ha hb hcross

theorem mem_wrapOuter_iff (S : SecondaryStructure n) (a : Arc (n + 2)) :
    a ∈ (wrapOuter S).arcs ↔
      a = Arc.outer n ∨
        ∃ b ∈ S.arcs,
          b.mapOrderEmbedding (Fin.interiorOrderEmbedding n) = a := by
  simp only [wrapOuter, Finset.mem_insert, mem_mapOrderEmbedding_iff]

@[simp]
theorem outer_mem_wrapOuter (S : SecondaryStructure n) :
    Arc.outer n ∈ (wrapOuter S).arcs := by
  simp [wrapOuter]

@[simp]
theorem interior_mem_wrapOuter_iff (S : SecondaryStructure n) (a : Arc n) :
    a.mapOrderEmbedding (Fin.interiorOrderEmbedding n) ∈
        (wrapOuter S).arcs ↔ a ∈ S.arcs := by
  constructor
  · intro h
    rcases (mem_wrapOuter_iff S _).1 h with heq | hmap
    · exfalso
      exact Arc.outer_not_shareEndpoint_interior a
        ⟨(Arc.outer n).left, (Arc.outer n).incident_left,
          by rw [heq]; exact (Arc.outer n).incident_left⟩
    · obtain ⟨b, hb, heq⟩ := hmap
      exact (Arc.mapOrderEmbedding_injective _ heq).symm ▸ hb
  · intro ha
    exact (mem_wrapOuter_iff S _).2 (Or.inr ⟨a, ha, rfl⟩)

private theorem outer_not_mem_mappedInterior (S : SecondaryStructure n) :
    Arc.outer n ∉
      (S.mapOrderEmbedding (Fin.interiorOrderEmbedding n)).arcs := by
  intro h
  obtain ⟨a, ha, heq⟩ :=
    (mem_mapOrderEmbedding_iff (Fin.interiorOrderEmbedding n) S _).1 h
  exact Arc.outer_not_shareEndpoint_interior a
    ⟨(Arc.outer n).left, (Arc.outer n).incident_left,
      by rw [heq]; exact (Arc.outer n).incident_left⟩

@[simp]
theorem pairCount_wrapOuter (S : SecondaryStructure n) :
    pairCount (wrapOuter S) = pairCount S + 1 := by
  unfold pairCount
  change
    (insert (Arc.outer n)
      (S.mapOrderEmbedding (Fin.interiorOrderEmbedding n)).arcs).card =
        S.arcs.card + 1
  rw [Finset.card_insert_of_notMem (outer_not_mem_mappedInterior S)]
  simp [SecondaryStructure.mapOrderEmbedding, Nat.add_comm]

theorem structureCompatible_wrapOuter_iff
    (S : SecondaryStructure n) (w : Sequence (n + 2)) :
    StructureCompatible w (wrapOuter S) ↔
      Compatible (w (Arc.outer n).left) (w (Arc.outer n).right) ∧
        StructureCompatible
          (fun i => w (Fin.interiorOrderEmbedding n i)) S := by
  constructor
  · intro h
    constructor
    · exact h (Arc.outer n) (outer_mem_wrapOuter S)
    · intro a ha
      simpa using h (a.mapOrderEmbedding (Fin.interiorOrderEmbedding n))
        ((interior_mem_wrapOuter_iff S a).2 ha)
  · rintro ⟨hOuter, hS⟩ a ha
    rcases (mem_wrapOuter_iff S a).1 ha with rfl | hmap
    · exact hOuter
    · obtain ⟨b, hb, rfl⟩ := hmap
      simpa using hS b hb

theorem positionPaired_wrapOuter_interior_iff
    (S : SecondaryStructure n) (i : Fin n) :
    (wrapOuter S).positionPaired (Fin.interiorOrderEmbedding n i) ↔
      S.positionPaired i := by
  constructor
  · rintro ⟨a, ha, hi⟩
    rcases (mem_wrapOuter_iff S a).1 ha with rfl | hmap
    · exact False.elim (Arc.outer_not_incident_interiorPosition i hi)
    · obtain ⟨b, hb, rfl⟩ := hmap
      exact ⟨b, hb, (Arc.mapOrderEmbedding_incident_iff
        (Fin.interiorOrderEmbedding n) b i).1 hi⟩
  · rintro ⟨a, ha, hi⟩
    exact ⟨a.mapOrderEmbedding (Fin.interiorOrderEmbedding n),
      (interior_mem_wrapOuter_iff S a).2 ha,
      (Arc.mapOrderEmbedding_incident_iff
        (Fin.interiorOrderEmbedding n) a i).2 hi⟩

theorem saturated_wrapOuter_iff (S : SecondaryStructure n) :
    SaturatedStructure (wrapOuter S) ↔ SaturatedStructure S := by
  constructor
  · intro h i
    exact (positionPaired_wrapOuter_interior_iff S i).1
      (h (Fin.interiorOrderEmbedding n i))
  · intro h i
    by_cases hzero : i.val = 0
    · have hi : i = (Arc.outer n).left := Fin.ext hzero
      exact ⟨Arc.outer n, outer_mem_wrapOuter S, Or.inl hi⟩
    by_cases hlast : i.val = n + 1
    · have hi : i = (Arc.outer n).right := Fin.ext hlast
      exact ⟨Arc.outer n, outer_mem_wrapOuter S, Or.inr hi⟩
    · let j : Fin n := ⟨i.val - 1, by
        have hi := i.isLt
        omega⟩
      have hij : Fin.interiorOrderEmbedding n j = i := by
        apply Fin.ext
        simp only [Fin.interiorOrderEmbedding_val, j]
        omega
      rw [← hij]
      exact (positionPaired_wrapOuter_interior_iff S j).2 (h j)

/-- Word-indexed wrapping, retaining exactly the positional constructor above. -/
def wrapWord (a b : Nucleotide) (z : Word)
    (S : SecondaryStructure z.length) :
    SecondaryStructure (Word.wrap a b z).length :=
  (wrapOuter S).reindexOrderIso
    (Fin.castOrderIso (Word.length_wrap a b z).symm)

theorem mem_wrapWord_iff (a b : Nucleotide) (z : Word)
    (S : SecondaryStructure z.length)
    (c : Arc (Word.wrap a b z).length) :
    c ∈ (wrapWord a b z S).arcs ↔
      c = Arc.wrapWordOuter a b z ∨
        ∃ d ∈ S.arcs,
          d.mapOrderEmbedding (Fin.wrapInteriorOrderEmbedding a b z) = c := by
  constructor
  · intro hc
    obtain ⟨d, hd, rfl⟩ :=
      (mem_mapOrderEmbedding_iff
        (Fin.castOrderIso (Word.length_wrap a b z).symm).toOrderEmbedding
        (wrapOuter S) c).1 hc
    rcases (mem_wrapOuter_iff S d).1 hd with rfl | h
    · exact Or.inl rfl
    · obtain ⟨e, he, rfl⟩ := h
      exact Or.inr ⟨e, he, rfl⟩
  · intro hc
    rcases hc with rfl | h
    · change
        (Arc.outer z.length).mapOrderEmbedding
            (Fin.castOrderIso (Word.length_wrap a b z).symm).toOrderEmbedding ∈
          ((wrapOuter S).mapOrderEmbedding
            (Fin.castOrderIso
              (Word.length_wrap a b z).symm).toOrderEmbedding).arcs
      exact (mapOrderEmbedding_mem_iff _ (wrapOuter S) _).2
        (outer_mem_wrapOuter S)
    · obtain ⟨d, hd, rfl⟩ := h
      change
        (d.mapOrderEmbedding
          (Fin.interiorOrderEmbedding z.length)).mapOrderEmbedding
            (Fin.castOrderIso (Word.length_wrap a b z).symm).toOrderEmbedding ∈
          ((wrapOuter S).mapOrderEmbedding
            (Fin.castOrderIso
              (Word.length_wrap a b z).symm).toOrderEmbedding).arcs
      exact (mapOrderEmbedding_mem_iff _ (wrapOuter S) _).2
        ((interior_mem_wrapOuter_iff S d).2 hd)

@[simp]
theorem outer_mem_wrapWord (a b : Nucleotide) (z : Word)
    (S : SecondaryStructure z.length) :
    Arc.wrapWordOuter a b z ∈ (wrapWord a b z S).arcs :=
  (mem_wrapWord_iff a b z S _).2 (Or.inl rfl)

@[simp]
theorem interior_mem_wrapWord_iff (a b : Nucleotide) (z : Word)
    (S : SecondaryStructure z.length) (c : Arc z.length) :
    c.mapOrderEmbedding (Fin.wrapInteriorOrderEmbedding a b z) ∈
        (wrapWord a b z S).arcs ↔ c ∈ S.arcs := by
  change
    (c.mapOrderEmbedding
      (Fin.interiorOrderEmbedding z.length)).mapOrderEmbedding
        (Fin.castOrderIso (Word.length_wrap a b z).symm).toOrderEmbedding ∈
      ((wrapOuter S).mapOrderEmbedding
        (Fin.castOrderIso
          (Word.length_wrap a b z).symm).toOrderEmbedding).arcs ↔ c ∈ S.arcs
  rw [mapOrderEmbedding_mem_iff, interior_mem_wrapOuter_iff]

@[simp]
theorem pairCount_wrapWord (a b : Nucleotide) (z : Word)
    (S : SecondaryStructure z.length) :
    pairCount (wrapWord a b z S) = pairCount S + 1 := by
  simp [wrapWord]

@[simp]
theorem saturated_wrapWord_iff (a b : Nucleotide) (z : Word)
    (S : SecondaryStructure z.length) :
    SaturatedStructure (wrapWord a b z S) ↔ SaturatedStructure S := by
  rw [wrapWord, saturated_reindexOrderIso_iff, saturated_wrapOuter_iff]

private theorem wrapWord_left_value (a b : Nucleotide) (z : Word) :
    (Word.wrap a b z).toSequence
      ((Fin.castOrderIso (Word.length_wrap a b z).symm)
        (Arc.outer z.length).left) = a := by
  have hi :
      (Fin.castOrderIso (Word.length_wrap a b z).symm)
          (Arc.outer z.length).left =
        (⟨0, by simp [Word.wrap]⟩ : Fin (Word.wrap a b z).length) := by
    apply Fin.ext
    rfl
  rw [hi]
  simp [Word.wrap, Word.toSequence, List.get_eq_getElem]

private theorem wrapWord_right_value (a b : Nucleotide) (z : Word) :
    (Word.wrap a b z).toSequence
      ((Fin.castOrderIso (Word.length_wrap a b z).symm)
        (Arc.outer z.length).right) = b := by
  have hi :
      (Fin.castOrderIso (Word.length_wrap a b z).symm)
          (Arc.outer z.length).right =
        (⟨z.length + 1, by simp [Word.wrap]⟩ :
          Fin (Word.wrap a b z).length) := by
    apply Fin.ext
    rfl
  rw [hi]
  simp [Word.wrap, Word.toSequence, List.get_eq_getElem]

private theorem wrapWord_interior_value (a b : Nucleotide) (z : Word)
    (i : Fin z.length) :
    (Word.wrap a b z).toSequence
      ((Fin.castOrderIso (Word.length_wrap a b z).symm)
        (Fin.interiorOrderEmbedding z.length i)) = z.toSequence i := by
  have hi :
      (Fin.castOrderIso (Word.length_wrap a b z).symm)
          (Fin.interiorOrderEmbedding z.length i) =
        (⟨i.val + 1, by simp [Word.wrap]; omega⟩ :
          Fin (Word.wrap a b z).length) := by
    apply Fin.ext
    rfl
  rw [hi]
  simp [Word.wrap, Word.toSequence, List.get_eq_getElem]

theorem structureCompatible_wrapWord_iff (a b : Nucleotide) (z : Word)
    (S : SecondaryStructure z.length) :
    StructureCompatible (Word.wrap a b z).toSequence (wrapWord a b z S) ↔
      Compatible a b ∧ StructureCompatible z.toSequence S := by
  rw [wrapWord, structureCompatible_reindexOrderIso_iff,
    structureCompatible_wrapOuter_iff]
  constructor <;> rintro ⟨hOuter, hS⟩ <;> constructor
  · simpa only [wrapWord_left_value, wrapWord_right_value] using hOuter
  · intro c hc
    simpa only [wrapWord_interior_value] using hS c hc
  · simpa only [wrapWord_left_value, wrapWord_right_value] using hOuter
  · intro c hc
    simpa only [wrapWord_interior_value] using hS c hc

/-! ## Restrictions to consecutive intervals -/

/-- Pull a structure back to a consecutive half-open interval. -/
def restrictInterval (S : SecondaryStructure n) (start len : Nat)
    (h : start + len ≤ n) : SecondaryStructure len :=
  S.pullbackOrderEmbedding (Fin.intervalOrderEmbedding start len n h)

/-- Pull a structure back to its first `k` positions. -/
def restrictPrefix (S : SecondaryStructure n) (k : Nat) (h : k ≤ n) :
    SecondaryStructure k :=
  S.restrictInterval 0 k (by omega)

/-- Pull a structure back to the positions strictly enclosed by `a`. -/
def restrictOpenArc (S : SecondaryStructure n) (a : Arc n) :
    SecondaryStructure a.openLength :=
  S.pullbackOrderEmbedding a.openIntervalOrderEmbedding

/-- Pull a structure back to the inclusive interval of `a`. -/
def restrictClosedArc (S : SecondaryStructure n) (a : Arc n) :
    SecondaryStructure a.closedLength :=
  S.pullbackOrderEmbedding a.closedIntervalOrderEmbedding

@[simp]
theorem mem_restrictInterval_iff (S : SecondaryStructure n)
    (start len : Nat) (h : start + len ≤ n) (a : Arc len) :
    a ∈ (S.restrictInterval start len h).arcs ↔
      a.mapOrderEmbedding (Fin.intervalOrderEmbedding start len n h) ∈ S.arcs := by
  exact mem_pullbackOrderEmbedding_iff _ _ _

@[simp]
theorem mem_restrictPrefix_iff (S : SecondaryStructure n)
    (k : Nat) (h : k ≤ n) (a : Arc k) :
    a ∈ (S.restrictPrefix k h).arcs ↔
      a.mapOrderEmbedding (Fin.intervalOrderEmbedding 0 k n (by omega)) ∈
        S.arcs := by
  exact mem_pullbackOrderEmbedding_iff _ _ _

@[simp]
theorem mem_restrictOpenArc_iff (S : SecondaryStructure n)
    (outer : Arc n) (a : Arc outer.openLength) :
    a ∈ (S.restrictOpenArc outer).arcs ↔
      a.mapOrderEmbedding outer.openIntervalOrderEmbedding ∈ S.arcs := by
  exact mem_pullbackOrderEmbedding_iff _ _ _

@[simp]
theorem mem_restrictClosedArc_iff (S : SecondaryStructure n)
    (outer : Arc n) (a : Arc outer.closedLength) :
    a ∈ (S.restrictClosedArc outer).arcs ↔
      a.mapOrderEmbedding outer.closedIntervalOrderEmbedding ∈ S.arcs := by
  exact mem_pullbackOrderEmbedding_iff _ _ _

theorem structureCompatible_restrictInterval
    (S : SecondaryStructure n) (w : Sequence n)
    (start len : Nat) (h : start + len ≤ n)
    (hCompat : StructureCompatible w S) :
    StructureCompatible
      (fun i => w (Fin.intervalOrderEmbedding start len n h i))
      (S.restrictInterval start len h) :=
  structureCompatible_pullbackOrderEmbedding _ S w hCompat

theorem structureCompatible_restrictPrefix
    (S : SecondaryStructure n) (w : Sequence n) (k : Nat) (h : k ≤ n)
    (hCompat : StructureCompatible w S) :
    StructureCompatible
      (fun i => w (Fin.intervalOrderEmbedding 0 k n (by omega) i))
      (S.restrictPrefix k h) :=
  structureCompatible_pullbackOrderEmbedding _ S w hCompat

theorem structureCompatible_restrictOpenArc
    (S : SecondaryStructure n) (w : Sequence n) (outer : Arc n)
    (hCompat : StructureCompatible w S) :
    StructureCompatible (fun i => w (outer.openIntervalOrderEmbedding i))
      (S.restrictOpenArc outer) :=
  structureCompatible_pullbackOrderEmbedding _ S w hCompat

theorem structureCompatible_restrictClosedArc
    (S : SecondaryStructure n) (w : Sequence n) (outer : Arc n)
    (hCompat : StructureCompatible w S) :
    StructureCompatible (fun i => w (outer.closedIntervalOrderEmbedding i))
      (S.restrictClosedArc outer) :=
  structureCompatible_pullbackOrderEmbedding _ S w hCompat

theorem pairCount_restrictInterval_le (S : SecondaryStructure n)
    (start len : Nat) (h : start + len ≤ n) :
    pairCount (S.restrictInterval start len h) ≤ pairCount S :=
  pairCount_pullbackOrderEmbedding_le _ S

theorem pairCount_restrictPrefix_le (S : SecondaryStructure n)
    (k : Nat) (h : k ≤ n) :
    pairCount (S.restrictPrefix k h) ≤ pairCount S :=
  pairCount_pullbackOrderEmbedding_le _ S

theorem pairCount_restrictOpenArc_le (S : SecondaryStructure n)
    (outer : Arc n) :
    pairCount (S.restrictOpenArc outer) ≤ pairCount S :=
  pairCount_pullbackOrderEmbedding_le _ S

theorem pairCount_restrictClosedArc_le (S : SecondaryStructure n)
    (outer : Arc n) :
    pairCount (S.restrictClosedArc outer) ≤ pairCount S :=
  pairCount_pullbackOrderEmbedding_le _ S

/-- A partner of a position strictly enclosed by an actual arc remains
strictly enclosed.  This is the elementary noncrossing closure fact. -/
theorem positionPartner_inOpenInterval_of_enclosingArc
    (S : SecondaryStructure n) (outer : Arc n) (hOuter : outer ∈ S.arcs)
    {i j : Fin n} (hi : outer.PositionInOpenInterval i)
    (hij : PositionPartner S i j) :
    outer.PositionInOpenInterval j := by
  obtain ⟨inner, hInner, horder⟩ := hij
  have hne : outer ≠ inner := by
    intro heq
    subst inner
    rcases horder with ⟨hileft, _⟩ | ⟨hiright, _⟩
    · rw [hileft] at hi
      exact (lt_irrefl outer.left) hi.1
    · rw [hiright] at hi
      exact (lt_irrefl outer.right) hi.2
  have hnoShare : ¬ outer.ShareEndpoint inner := by
    intro hshare
    exact hne (S.eq_of_mem_of_shareEndpoint hOuter hInner hshare)
  have hnc := S.not_crossing hOuter hInner
  rcases horder with ⟨hileft, hjright⟩ | ⟨hiright, hjleft⟩
  · subst i
    subst j
    have hrightNe : inner.right ≠ outer.right := by
      intro hright
      apply hnoShare
      exact ⟨outer.right, outer.incident_right, Or.inr hright.symm⟩
    have hnotOut : ¬ outer.right < inner.right := by
      intro hout
      apply hnc
      exact Or.inl ⟨hi.1, hi.2, hout⟩
    exact ⟨hi.1.trans inner.ordered,
      lt_of_le_of_ne (le_of_not_gt hnotOut) hrightNe⟩
  · subst i
    subst j
    have hleftNe : outer.left ≠ inner.left := by
      intro hleft
      apply hnoShare
      exact ⟨outer.left, outer.incident_left, Or.inl hleft⟩
    have hnotOut : ¬ inner.left < outer.left := by
      intro hout
      apply hnc
      exact Or.inr ⟨hout, hi.1, hi.2⟩
    exact ⟨lt_of_le_of_ne (le_of_not_gt hnotOut) hleftNe,
      inner.ordered.trans hi.2⟩

/-- The strict interior of an arc in a saturated noncrossing matching is
saturated after restriction. -/
theorem saturated_restrictOpenArc (S : SecondaryStructure n)
    (outer : Arc n) (hOuter : outer ∈ S.arcs)
    (hSat : SaturatedStructure S) :
    SaturatedStructure (S.restrictOpenArc outer) := by
  apply saturated_pullbackOrderEmbedding_of_partnerClosed
    outer.openIntervalOrderEmbedding S hSat
  intro i j hij
  have hi : outer.PositionInOpenInterval (outer.openIntervalOrderEmbedding i) :=
    (Arc.exists_openIntervalOrderEmbedding_eq_iff outer _).1 ⟨i, rfl⟩
  have hj := positionPartner_inOpenInterval_of_enclosingArc S outer hOuter hi hij
  exact (Arc.exists_openIntervalOrderEmbedding_eq_iff outer j).2 hj

/-- The inclusive interval of an arc in a saturated noncrossing matching is
saturated after restriction. -/
theorem saturated_restrictClosedArc (S : SecondaryStructure n)
    (outer : Arc n) (hOuter : outer ∈ S.arcs)
    (hSat : SaturatedStructure S) :
    SaturatedStructure (S.restrictClosedArc outer) := by
  apply saturated_pullbackOrderEmbedding_of_partnerClosed
    outer.closedIntervalOrderEmbedding S hSat
  intro i j hij
  have hiClosed :
      outer.PositionInClosedInterval (outer.closedIntervalOrderEmbedding i) :=
    (Arc.exists_closedIntervalOrderEmbedding_eq_iff outer _).1 ⟨i, rfl⟩
  by_cases hleft : outer.closedIntervalOrderEmbedding i = outer.left
  · have hOuterPartner : PositionPartner S
        (outer.closedIntervalOrderEmbedding i) outer.right := by
      exact ⟨outer, hOuter, Or.inl ⟨hleft, rfl⟩⟩
    have hj : j = outer.right := positionPartner_unique hij hOuterPartner
    subst j
    apply (Arc.exists_closedIntervalOrderEmbedding_eq_iff outer _).2
    exact ⟨le_of_lt outer.ordered, le_rfl⟩
  by_cases hright : outer.closedIntervalOrderEmbedding i = outer.right
  · have hOuterPartner : PositionPartner S
        (outer.closedIntervalOrderEmbedding i) outer.left := by
      exact ⟨outer, hOuter, Or.inr ⟨hright, rfl⟩⟩
    have hj : j = outer.left := positionPartner_unique hij hOuterPartner
    subst j
    apply (Arc.exists_closedIntervalOrderEmbedding_eq_iff outer _).2
    exact ⟨le_rfl, le_of_lt outer.ordered⟩
  · have hiOpen :
        outer.PositionInOpenInterval (outer.closedIntervalOrderEmbedding i) := by
      exact ⟨lt_of_le_of_ne hiClosed.1 (Ne.symm hleft),
        lt_of_le_of_ne hiClosed.2 hright⟩
    have hjOpen :=
      positionPartner_inOpenInterval_of_enclosingArc S outer hOuter hiOpen hij
    apply (Arc.exists_closedIntervalOrderEmbedding_eq_iff outer _).2
    exact ⟨le_of_lt hjOpen.1, le_of_lt hjOpen.2⟩

/-- Prefix saturation under the exact partner-closure hypothesis.  The
enclosed-arc theorem above is the common way this hypothesis is discharged. -/
theorem saturated_restrictPrefix_of_partnerClosed
    (S : SecondaryStructure n) (k : Nat) (h : k ≤ n)
    (hSat : SaturatedStructure S)
    (hClosed : ∀ (i : Fin k) (j : Fin n),
      PositionPartner S (Fin.intervalOrderEmbedding 0 k n (by omega) i) j →
        ∃ q : Fin k, Fin.intervalOrderEmbedding 0 k n (by omega) q = j) :
    SaturatedStructure (S.restrictPrefix k h) :=
  saturated_pullbackOrderEmbedding_of_partnerClosed _ S hSat hClosed

/-! ## Splitting at an isolated saturated prefix block -/

/-- If a saturated matching contains an outer arc around the complete first
word block, noncrossingness and partial matching make that arc a barrier: the
matching is exactly the concatenation of saturated restrictions to the two
blocks. -/
theorem splitAtOuterPrefix (x y : Word) (hx : x ≠ [])
    (P : SecondaryStructure (x ++ y).length)
    (q : Arc (x ++ y).length) (hq : q ∈ P.arcs)
    (hql : q.left.val = 0) (hqr : q.right.val + 1 = x.length)
    (hSat : SaturatedStructure P) :
    ∃ PL : SecondaryStructure x.length,
      ∃ PR : SecondaryStructure y.length,
        SaturatedStructure PL ∧ SaturatedStructure PR ∧
          P = appendWords x y PL PR := by
  let eL := Fin.appendLeftOrderEmbedding x y
  let eR := Fin.appendRightOrderEmbedding x y
  let PL := P.pullbackOrderEmbedding eL
  let PR := P.pullbackOrderEmbedding eR
  have hxPos : 0 < x.length := (List.length_pos_iff).2 hx
  have hqPartner : PositionPartner P q.left q.right :=
    ⟨q, hq, Or.inl ⟨rfl, rfl⟩⟩
  have hLeftPartner : ∀ (p : Fin (x ++ y).length),
      p.val < x.length → ∀ (j : Fin (x ++ y).length),
        PositionPartner P p j → j.val < x.length := by
    intro p hp j hpj
    by_cases hpl : p = q.left
    · have hpq : PositionPartner P p q.right := by
        simpa [hpl] using hqPartner
      have hj : j = q.right := positionPartner_unique hpj hpq
      rw [hj]
      omega
    by_cases hpr : p = q.right
    · have hpq : PositionPartner P p q.left := by
        simpa [hpr] using positionPartner_symm hqPartner
      have hj : j = q.left := positionPartner_unique hpj hpq
      rw [hj]
      omega
    · have hpOpen : q.PositionInOpenInterval p := by
        unfold Arc.PositionInOpenInterval
        change q.left.val < p.val ∧ p.val < q.right.val
        omega
      have hjOpen :=
        positionPartner_inOpenInterval_of_enclosingArc P q hq hpOpen hpj
      unfold Arc.PositionInOpenInterval at hjOpen
      change q.left.val < j.val ∧ j.val < q.right.val at hjOpen
      omega
  have hPLSat : SaturatedStructure PL := by
    apply saturated_pullbackOrderEmbedding_of_partnerClosed eL P hSat
    intro i j hij
    have hjlt : j.val < x.length :=
      hLeftPartner (eL i) (by simp [eL]) j hij
    let k : Fin x.length := ⟨j.val, hjlt⟩
    exact ⟨k, Fin.ext (by simp [eL, k])⟩
  have hPRSat : SaturatedStructure PR := by
    apply saturated_pullbackOrderEmbedding_of_partnerClosed eR P hSat
    intro i j hij
    have hjge : x.length ≤ j.val := by
      by_contra hnot
      have hjlt : j.val < x.length := Nat.lt_of_not_ge hnot
      have hPartner := hLeftPartner j hjlt (eR i)
        (positionPartner_symm hij)
      have hlt := hPartner
      simp only [eR, Fin.appendRightOrderEmbedding_val] at hlt
      omega
    let k : Fin y.length := ⟨j.val - x.length, by
      have hjBound := j.isLt
      simp only [List.length_append] at hjBound
      omega⟩
    exact ⟨k, Fin.ext (by simp [eR, k]; omega)⟩
  refine ⟨PL, PR, hPLSat, hPRSat, ?_⟩
  apply SecondaryStructure.ext
  ext a
  constructor
  · intro ha
    by_cases hleft : a.left.val < x.length
    · have hright : a.right.val < x.length :=
        hLeftPartner a.left hleft a.right
          ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩
      let b : Arc x.length :=
        ⟨⟨a.left.val, hleft⟩, ⟨a.right.val, hright⟩, a.ordered⟩
      have hba : b.mapOrderEmbedding eL = a := by
        apply Arc.ext <;> apply Fin.ext <;> simp [b, eL]
      rw [← hba]
      exact (left_mem_appendWords_iff x y PL PR b).2
        ((mem_pullbackOrderEmbedding_iff eL P b).2 (by simpa [hba]))
    · have hleftGe : x.length ≤ a.left.val := Nat.le_of_not_gt hleft
      have hrightGe : x.length ≤ a.right.val :=
        hleftGe.trans (le_of_lt a.ordered)
      have hleftBound : a.left.val < x.length + y.length := by
        simpa only [List.length_append] using a.left.isLt
      have hrightBound : a.right.val < x.length + y.length := by
        simpa only [List.length_append] using a.right.isLt
      have hleftSmall : a.left.val - x.length < y.length := by omega
      have hrightSmall : a.right.val - x.length < y.length := by omega
      have hordered :
          a.left.val - x.length < a.right.val - x.length := by
        have haOrdered := a.ordered
        change a.left.val < a.right.val at haOrdered
        omega
      let b : Arc y.length :=
        ⟨⟨a.left.val - x.length, hleftSmall⟩,
          ⟨a.right.val - x.length, hrightSmall⟩, hordered⟩
      have hba : b.mapOrderEmbedding eR = a := by
        apply Arc.ext <;> apply Fin.ext <;> simp [b, eR] <;> omega
      rw [← hba]
      exact (right_mem_appendWords_iff x y PL PR b).2
        ((mem_pullbackOrderEmbedding_iff eR P b).2 (by simpa [hba]))
  · intro ha
    rcases (mem_appendWords_iff x y PL PR a).1 ha with h | h
    · obtain ⟨b, hb, rfl⟩ := h
      exact (mem_pullbackOrderEmbedding_iff eL P b).1 hb
    · obtain ⟨b, hb, rfl⟩ := h
      exact (mem_pullbackOrderEmbedding_iff eR P b).1 hb

/-- If a saturated matching on a wrapped word contains the full positional
outer pair, its interior pullback is saturated and reconstructs the complete
matching by the canonical wrapping constructor. -/
theorem splitOuterWrap (a b : Nucleotide) (z : Word)
    (P : SecondaryStructure (Word.wrap a b z).length)
    (q : Arc (Word.wrap a b z).length) (hq : q ∈ P.arcs)
    (hql : q.left.val = 0)
    (hqr : q.right.val + 1 = (Word.wrap a b z).length)
    (hSat : SaturatedStructure P) :
    ∃ Q : SecondaryStructure z.length,
      SaturatedStructure Q ∧ P = wrapWord a b z Q := by
  let e := Fin.wrapInteriorOrderEmbedding a b z
  let Q := P.pullbackOrderEmbedding e
  have hqRight : q.right.val = z.length + 1 := by
    have hlen := Word.length_wrap a b z
    omega
  have hqExpected : q = Arc.wrapWordOuter a b z := by
    apply Arc.ext <;> apply Fin.ext
    · simpa using hql
    · simpa using hqRight
  have hQSat : SaturatedStructure Q := by
    apply saturated_pullbackOrderEmbedding_of_partnerClosed e P hSat
    intro i j hij
    have hiOpen : q.PositionInOpenInterval (e i) := by
      unfold Arc.PositionInOpenInterval
      change q.left.val < (e i).val ∧ (e i).val < q.right.val
      have hi := i.isLt
      simp only [e, Fin.wrapInteriorOrderEmbedding_val]
      omega
    have hjOpen :=
      positionPartner_inOpenInterval_of_enclosingArc P q hq hiOpen hij
    unfold Arc.PositionInOpenInterval at hjOpen
    change q.left.val < j.val ∧ j.val < q.right.val at hjOpen
    let k : Fin z.length := ⟨j.val - 1, by omega⟩
    exact ⟨k, Fin.ext (by simp [e, k]; omega)⟩
  refine ⟨Q, hQSat, ?_⟩
  apply SecondaryStructure.ext
  ext c
  constructor
  · intro hc
    by_cases hcq : c = q
    · subst c
      rw [hqExpected]
      exact outer_mem_wrapWord a b z Q
    · have hNoShare : ¬ q.ShareEndpoint c := by
        intro hshare
        exact hcq (P.eq_of_mem_of_shareEndpoint hq hc hshare).symm
      have hleftNe : c.left ≠ q.left := by
        intro h
        apply hNoShare
        exact ⟨q.left, q.incident_left, Or.inl h.symm⟩
      have hrightNe : c.right ≠ q.right := by
        intro h
        apply hNoShare
        exact ⟨q.right, q.incident_right, Or.inr h.symm⟩
      have hcLeftPos : 0 < c.left.val := by
        have hneVal : c.left.val ≠ 0 := by
          intro hzero
          apply hleftNe
          apply Fin.ext
          omega
        omega
      have hcRightLt : c.right.val < z.length + 1 := by
        have hcBound := c.right.isLt
        have hlen := Word.length_wrap a b z
        have hneVal : c.right.val ≠ z.length + 1 := by
          intro heq
          apply hrightNe
          apply Fin.ext
          omega
        omega
      have hcLeftSmall : c.left.val - 1 < z.length := by
        have hcOrdered := c.ordered
        change c.left.val < c.right.val at hcOrdered
        omega
      have hcRightSmall : c.right.val - 1 < z.length := by omega
      have hcOrdered : c.left.val - 1 < c.right.val - 1 := by
        have hord := c.ordered
        change c.left.val < c.right.val at hord
        omega
      let d : Arc z.length :=
        ⟨⟨c.left.val - 1, hcLeftSmall⟩,
          ⟨c.right.val - 1, hcRightSmall⟩, hcOrdered⟩
      have hdc : d.mapOrderEmbedding e = c := by
        apply Arc.ext <;> apply Fin.ext <;> simp [d, e] <;> omega
      rw [← hdc]
      exact (interior_mem_wrapWord_iff a b z Q d).2
        ((mem_pullbackOrderEmbedding_iff e P d).2 (by simpa [hdc]))
  · intro hc
    rcases (mem_wrapWord_iff a b z Q c).1 hc with hcOuter | h
    · rw [hcOuter, ← hqExpected]
      exact hq
    · obtain ⟨d, hd, rfl⟩ := h
      exact (mem_pullbackOrderEmbedding_iff e P d).1 hd

end SecondaryStructure

end RNA
