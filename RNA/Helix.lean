module

public import Mathlib.Data.Fintype.Prod
public import RNA.Structure

@[expose] public section

set_option autoImplicit false

/-!
# Exact maximal stacked runs

A candidate consists of an outer arc and a natural length bounded by `n`.
Membership requires every exact offset pair.  Maximality independently forbids
an outward predecessor and the next inward offset, so arbitrary subchains do
not count as helices.
-/

namespace RNA

variable {n : Nat}

/-- The exact endpoint equations for the pair at offset `k` inside `outer`.
Using addition on the right equation avoids truncated subtraction. -/
def Arc.StackOffset (outer inner : Arc n) (k : Nat) : Prop :=
  inner.left.val = outer.left.val + k ∧
    inner.right.val + k = outer.right.val

instance Arc.instDecidableStackOffset (outer inner : Arc n) (k : Nat) :
    Decidable (outer.StackOffset inner k) := by
  unfold Arc.StackOffset
  infer_instance

/-- Consecutive stacked target pairs `(i,j)` and `(i+1,j-1)`. -/
def Arc.Stacked (outer inner : Arc n) : Prop :=
  outer.StackOffset inner 1

instance Arc.instDecidableStacked (outer inner : Arc n) :
    Decidable (outer.Stacked inner) := by
  unfold Arc.Stacked
  infer_instance

theorem Arc.stackOffset_zero_iff (outer inner : Arc n) :
    outer.StackOffset inner 0 ↔ inner = outer := by
  constructor
  · rintro ⟨hl, hr⟩
    apply Arc.ext
    · apply Fin.ext
      simpa using hl
    · apply Fin.ext
      simpa using hr
  · rintro rfl
    simp [Arc.StackOffset]

theorem Arc.stackOffset_arc_unique {outer a b : Arc n} {k : Nat}
    (ha : outer.StackOffset a k) (hb : outer.StackOffset b k) : a = b := by
  unfold Arc.StackOffset at ha hb
  apply Arc.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

theorem Arc.stackOffset_index_unique {outer a : Arc n} {k l : Nat}
    (hk : outer.StackOffset a k) (hl : outer.StackOffset a l) : k = l := by
  unfold Arc.StackOffset at hk hl
  omega

/-- A finite descriptor.  `Fin (n+1)` contains every possible run length on an
`n`-position backbone; positivity is part of `IsMaximalHelix`. -/
abbrev HelixCandidate (n : Nat) := Arc n × Fin (n + 1)

namespace HelixCandidate

def outer (H : HelixCandidate n) : Arc n := H.1

def length (H : HelixCandidate n) : Nat := H.2.val

theorem length_le_backbone (H : HelixCandidate n) : H.length ≤ n := by
  have h := H.2.isLt
  simp only [length] at h ⊢
  omega

end HelixCandidate

/-- The target contains the exact pair at offset `k` from `outer`. -/
def HasStackOffset (T : SecondaryStructure n) (outer : Arc n) (k : Nat) : Prop :=
  ∃ a ∈ T.arcs, outer.StackOffset a k

instance instDecidableHasStackOffset (T : SecondaryStructure n) (outer : Arc n) (k : Nat) :
    Decidable (HasStackOffset T outer k) := by
  unfold HasStackOffset
  infer_instance

/-- The unrestricted mathematical predicate for an exact maximal run of
natural length `h`. -/
def IsMaximalHelixRun (T : SecondaryStructure n) (outer : Arc n) (h : Nat) : Prop :=
  0 < h ∧
    outer ∈ T.arcs ∧
    (¬ ∃ a ∈ T.arcs, a.Stacked outer) ∧
    (∀ k : Fin h, HasStackOffset T outer k.val) ∧
    ¬ HasStackOffset T outer h

instance instDecidableIsMaximalHelixRun (T : SecondaryStructure n)
    (outer : Arc n) (h : Nat) : Decidable (IsMaximalHelixRun T outer h) := by
  unfold IsMaximalHelixRun
  infer_instance

/-- Every genuine run length fits the finite descriptor.  Thus the `Fin (n+1)`
enumeration does not discard any mathematical maximal run. -/
theorem isMaximalHelixRun_length_le (T : SecondaryStructure n) (outer : Arc n)
    (h : Nat) (hRun : IsMaximalHelixRun T outer h) : h ≤ n := by
  rcases hRun with ⟨hpos, _houter, _hnoOut, hOffsets, _hnoIn⟩
  let k : Fin h := ⟨h - 1, by omega⟩
  obtain ⟨a, _haT, ha⟩ := hOffsets k
  have hale := a.left.isLt
  unfold Arc.StackOffset at ha
  dsimp [k] at ha
  omega

/-- The finite candidate version of the unrestricted maximal-run predicate. -/
def IsMaximalHelix (T : SecondaryStructure n) (H : HelixCandidate n) : Prop :=
  IsMaximalHelixRun T H.outer H.length

instance instDecidableIsMaximalHelix (T : SecondaryStructure n) (H : HelixCandidate n) :
    Decidable (IsMaximalHelix T H) := by
  unfold IsMaximalHelix
  infer_instance

/-- A maximal helix is a candidate carrying the exact maximal-run property. -/
abbrev MaximalHelix (T : SecondaryStructure n) :=
  {H : HelixCandidate n // IsMaximalHelix T H}

/-- Finite descriptors are complete for the unrestricted natural-length
maximal-run definition. -/
theorem exists_maximalHelix_iff_run (T : SecondaryStructure n)
    (outer : Arc n) (h : Nat) :
    (∃ H : MaximalHelix T, H.val.outer = outer ∧ H.val.length = h) ↔
      IsMaximalHelixRun T outer h := by
  constructor
  · rintro ⟨H, houter, hlength⟩
    simpa [IsMaximalHelix, houter, hlength] using H.property
  · intro hRun
    have hle := isMaximalHelixRun_length_le T outer h hRun
    let boundedLength : Fin (n + 1) := ⟨h, by omega⟩
    let candidate : HelixCandidate n := (outer, boundedLength)
    refine ⟨⟨candidate, ?_⟩, ?_, ?_⟩
    · simpa [IsMaximalHelix, candidate, boundedLength,
        HelixCandidate.outer, HelixCandidate.length] using hRun
    · rfl
    · rfl

namespace MaximalHelix

def outer {T : SecondaryStructure n} (H : MaximalHelix T) : Arc n := H.val.outer

def length {T : SecondaryStructure n} (H : MaximalHelix T) : Nat := H.val.length

theorem positive {T : SecondaryStructure n} (H : MaximalHelix T) : 0 < H.length :=
  H.property.1

theorem length_le_backbone {T : SecondaryStructure n} (H : MaximalHelix T) :
    H.length ≤ n :=
  H.val.length_le_backbone

theorem outer_mem {T : SecondaryStructure n} (H : MaximalHelix T) :
    H.outer ∈ T.arcs :=
  H.property.2.1

theorem no_outward {T : SecondaryStructure n} (H : MaximalHelix T) :
    ¬ ∃ a ∈ T.arcs, a.Stacked H.outer :=
  H.property.2.2.1

theorem has_offset {T : SecondaryStructure n} (H : MaximalHelix T)
    (k : Fin H.length) : HasStackOffset T H.outer k.val :=
  H.property.2.2.2.1 k

theorem no_inward {T : SecondaryStructure n} (H : MaximalHelix T) :
    ¬ HasStackOffset T H.outer H.length :=
  H.property.2.2.2.2

/-- For a fixed outermost pair, maximality determines the run length. -/
theorem length_eq_of_outer_eq {T : SecondaryStructure n} (H K : MaximalHelix T)
    (houter : H.outer = K.outer) : H.length = K.length := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · let k : Fin K.length := ⟨H.length, hlt⟩
    have hk := K.has_offset k
    have : HasStackOffset T H.outer H.length := by
      simpa [k, houter] using hk
    exact H.no_inward this
  · let k : Fin H.length := ⟨K.length, hgt⟩
    have hk := H.has_offset k
    have : HasStackOffset T K.outer K.length := by
      simpa [k, houter] using hk
    exact K.no_inward this

/-- Canonicality: maximal helices with the same outermost pair are equal. -/
@[ext]
theorem ext_outer {T : SecondaryStructure n} {H K : MaximalHelix T}
    (houter : H.outer = K.outer) : H = K := by
  apply Subtype.ext
  apply Prod.ext
  · exact houter
  · apply Fin.ext
    exact length_eq_of_outer_eq H K houter

theorem outer_injective {T : SecondaryStructure n} :
    Function.Injective (outer : MaximalHelix T → Arc n) := by
  intro H K h
  exact ext_outer h

end MaximalHelix

/-- The finite set of all exact maximal helices. -/
def maximalHelices (T : SecondaryStructure n) : Finset (MaximalHelix T) :=
  Finset.univ

/-- Maximal helices of one specified length. -/
def maximalHelicesOfLength (T : SecondaryStructure n) (h : Nat) :
    Finset (MaximalHelix T) :=
  (maximalHelices T).filter (fun H => H.length = h)

/-- Exactly the target arcs in one maximal run. -/
def helixMembers (T : SecondaryStructure n) (H : MaximalHelix T) : Finset (Arc n) :=
  T.arcs.filter (fun a =>
    ∃ k : Fin H.length, H.outer.StackOffset a k.val)

@[simp]
theorem mem_maximalHelices (T : SecondaryStructure n) (H : MaximalHelix T) :
    H ∈ maximalHelices T := by
  simp [maximalHelices]

@[simp]
theorem mem_maximalHelicesOfLength_iff (T : SecondaryStructure n)
    (H : MaximalHelix T) (h : Nat) :
    H ∈ maximalHelicesOfLength T h ↔ H.length = h := by
  simp [maximalHelicesOfLength]

namespace MaximalHelix

/-- The uniquely determined target arc at one offset of a maximal helix. -/
noncomputable def offsetArc {T : SecondaryStructure n} (H : MaximalHelix T)
    (k : Fin H.length) : Arc n :=
  Classical.choose (H.has_offset k)

theorem offsetArc_mem {T : SecondaryStructure n} (H : MaximalHelix T)
    (k : Fin H.length) : H.offsetArc k ∈ T.arcs :=
  (Classical.choose_spec (H.has_offset k)).1

theorem offsetArc_stackOffset {T : SecondaryStructure n} (H : MaximalHelix T)
    (k : Fin H.length) : H.outer.StackOffset (H.offsetArc k) k.val :=
  (Classical.choose_spec (H.has_offset k)).2

theorem offsetArc_injective {T : SecondaryStructure n} (H : MaximalHelix T) :
    Function.Injective H.offsetArc := by
  intro k l hkl
  apply Fin.ext
  apply Arc.stackOffset_index_unique (H.offsetArc_stackOffset k)
  rw [hkl]
  exact H.offsetArc_stackOffset l

noncomputable def offsetEmbedding {T : SecondaryStructure n} (H : MaximalHelix T) :
    Fin H.length ↪ Arc n where
  toFun := H.offsetArc
  inj' := H.offsetArc_injective

theorem helixMembers_eq_offset_image {T : SecondaryStructure n} (H : MaximalHelix T) :
    helixMembers T H = Finset.univ.map H.offsetEmbedding := by
  ext a
  simp only [helixMembers, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map]
  constructor
  · rintro ⟨_haT, k, hk⟩
    refine ⟨k, ?_⟩
    exact Arc.stackOffset_arc_unique (H.offsetArc_stackOffset k) hk
  · rintro ⟨k, hk⟩
    rw [← hk]
    exact ⟨H.offsetArc_mem k, k, H.offsetArc_stackOffset k⟩

/-- A maximal helix descriptor contains exactly its declared number of pairs. -/
theorem helixMembers_card {T : SecondaryStructure n} (H : MaximalHelix T) :
    (helixMembers T H).card = H.length := by
  rw [H.helixMembers_eq_offset_image]
  simp

/-- Two maximal runs sharing a target arc are the same maximal helix. -/
theorem eq_of_common_member {T : SecondaryStructure n} {H K : MaximalHelix T}
    {a : Arc n} (haH : a ∈ helixMembers T H) (haK : a ∈ helixMembers T K) :
    H = K := by
  simp only [helixMembers, Finset.mem_filter] at haH haK
  obtain ⟨_haT, k, hk⟩ := haH
  obtain ⟨_haT', l, hl⟩ := haK
  rcases Nat.lt_trichotomy k.val l.val with hkl | hkeq | hlk
  · let predecessorOffset : Fin K.length :=
      ⟨l.val - k.val - 1, by omega⟩
    obtain ⟨b, hbT, hb⟩ := K.has_offset predecessorOffset
    have hstacked : b.Stacked H.outer := by
      unfold Arc.Stacked Arc.StackOffset
      dsimp [predecessorOffset] at hb ⊢
      unfold Arc.StackOffset at hk hl hb
      omega
    exact False.elim (H.no_outward ⟨b, hbT, hstacked⟩)
  · have houter : H.outer = K.outer := by
      apply Arc.ext
      · apply Fin.ext
        unfold Arc.StackOffset at hk hl
        omega
      · apply Fin.ext
        unfold Arc.StackOffset at hk hl
        omega
    exact MaximalHelix.ext_outer houter
  · let predecessorOffset : Fin H.length :=
      ⟨k.val - l.val - 1, by omega⟩
    obtain ⟨b, hbT, hb⟩ := H.has_offset predecessorOffset
    have hstacked : b.Stacked K.outer := by
      unfold Arc.Stacked Arc.StackOffset
      dsimp [predecessorOffset] at hb ⊢
      unfold Arc.StackOffset at hk hl hb
      omega
    exact False.elim (K.no_outward ⟨b, hbT, hstacked⟩)

/-- Distinct maximal helices have disjoint target-pair sets. -/
theorem eq_or_disjoint_members {T : SecondaryStructure n} (H K : MaximalHelix T) :
    H = K ∨ Disjoint (helixMembers T H) (helixMembers T K) := by
  by_cases hHK : H = K
  · exact Or.inl hHK
  · right
    rw [Finset.disjoint_left]
    intro a haH haK
    exact hHK (eq_of_common_member haH haK)

end MaximalHelix

end RNA
