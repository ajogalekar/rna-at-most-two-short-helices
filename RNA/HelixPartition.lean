module

public import RNA.TargetClass

@[expose] public section

set_option autoImplicit false

/-!
# Canonical maximal-helix partition

This module completes the coverage side of the maximal-run representation from
`RNA.Helix`.  The existence proof maximizes only *genuine consecutive
segments*: every intermediate offset is required to be a target pair and the
distinguished target pair must occur at one of those offsets.  Thus the finite
argument cannot jump across a gap in a stack.
-/

namespace RNA

variable {n : Nat}

namespace Arc

/-- Exact stack offsets compose by addition. -/
theorem stackOffset_trans {a b c : Arc n} {k l : Nat}
    (hab : a.StackOffset b k) (hbc : b.StackOffset c l) :
    a.StackOffset c (k + l) := by
  unfold StackOffset at hab hbc ⊢
  omega

end Arc

/-- A finite consecutive segment of target pairs that contains a distinguished
target pair.  Unlike a mere collection of diagonal pairs, all offsets below
the declared length are required to occur. -/
def IsHelixSegmentContaining (T : SecondaryStructure n) (a : Arc n)
    (H : HelixCandidate n) : Prop :=
  0 < H.length ∧
    (∀ k : Fin H.length, HasStackOffset T H.outer k.val) ∧
    ∃ k : Fin H.length, H.outer.StackOffset a k.val

instance instDecidableIsHelixSegmentContaining (T : SecondaryStructure n)
    (a : Arc n) (H : HelixCandidate n) :
    Decidable (IsHelixSegmentContaining T a H) := by
  unfold IsHelixSegmentContaining
  infer_instance

/-- Consecutive target segments containing `a`, used internally by the
coverage proof. -/
abbrev HelixSegmentContaining (T : SecondaryStructure n) (a : Arc n) :=
  {H : HelixCandidate n // IsHelixSegmentContaining T a H}

namespace HelixSegmentContaining

private def singleton (T : SecondaryStructure n) (a : Arc n)
    (ha : a ∈ T.arcs) : HelixSegmentContaining T a := by
  have hn : 1 < n + 1 := by
    have := a.right.isLt
    omega
  let one : Fin (n + 1) := ⟨1, hn⟩
  refine ⟨(a, one), ?_⟩
  refine ⟨by simp [HelixCandidate.length, one], ?_, ?_⟩
  · intro k
    have hk : k.val = 0 := by
      have := k.isLt
      simpa [HelixCandidate.length, one] using this
    refine ⟨a, ha, ?_⟩
    change a.StackOffset a k.val
    simpa [hk] using (Arc.stackOffset_zero_iff a a).2 rfl
  · let zero : Fin (HelixCandidate.length (a, one)) :=
      ⟨0, by simp [HelixCandidate.length, one]⟩
    refine ⟨zero, ?_⟩
    change a.StackOffset a zero.val
    simpa [zero] using (Arc.stackOffset_zero_iff a a).2 rfl

private theorem extendInward (T : SecondaryStructure n) (a : Arc n)
    (S : HelixSegmentContaining T a)
    (hin : HasStackOffset T S.val.outer S.val.length) :
    ∃ S' : HelixSegmentContaining T a, S.val.length < S'.val.length := by
  obtain ⟨c, hcT, hc⟩ := hin
  have hlt : S.val.length < n := by
    have hcLeft := c.left.isLt
    unfold Arc.StackOffset at hc
    omega
  let nextLength : Fin (n + 1) := ⟨S.val.length + 1, by omega⟩
  let next : HelixCandidate n := (S.val.outer, nextLength)
  have hnextLength : next.length = S.val.length + 1 := rfl
  refine ⟨⟨next, ?_⟩, by simp [hnextLength]⟩
  refine ⟨by have := S.property.1; omega, ?_, ?_⟩
  · intro k
    by_cases hk : k.val < S.val.length
    · exact S.property.2.1 ⟨k.val, hk⟩
    · have hkeq : k.val = S.val.length := by
        have := k.isLt
        dsimp [next, nextLength, HelixCandidate.length] at this
        omega
      change HasStackOffset T S.val.outer k.val
      rw [hkeq]
      exact ⟨c, hcT, hc⟩
  · obtain ⟨k, hk⟩ := S.property.2.2
    let k' : Fin next.length := ⟨k.val, by
      dsimp [next, nextLength, HelixCandidate.length]
      omega⟩
    exact ⟨k', hk⟩

private theorem extendOutward (T : SecondaryStructure n) (a : Arc n)
    (S : HelixSegmentContaining T a)
    (hout : ∃ b ∈ T.arcs, b.Stacked S.val.outer) :
    ∃ S' : HelixSegmentContaining T a, S.val.length < S'.val.length := by
  obtain ⟨b, hbT, hb⟩ := hout
  have hpos := S.property.1
  let last : Fin S.val.length := ⟨S.val.length - 1, by omega⟩
  obtain ⟨c, hcT, hc⟩ := S.property.2.1 last
  have hbc : b.StackOffset c S.val.length := by
    have hcomp := Arc.stackOffset_trans hb hc
    dsimp [Arc.Stacked, last] at hb hcomp
    have hindex : 1 + (S.val.length - 1) = S.val.length := by omega
    simpa [hindex] using hcomp
  have hlt : S.val.length < n := by
    have hcLeft := c.left.isLt
    unfold Arc.StackOffset at hbc
    omega
  let nextLength : Fin (n + 1) := ⟨S.val.length + 1, by omega⟩
  let next : HelixCandidate n := (b, nextLength)
  have hnextLength : next.length = S.val.length + 1 := rfl
  refine ⟨⟨next, ?_⟩, by simp [hnextLength]⟩
  refine ⟨by omega, ?_, ?_⟩
  · intro k
    by_cases hk0 : k.val = 0
    · refine ⟨b, hbT, ?_⟩
      change b.StackOffset b k.val
      simpa [hk0] using (Arc.stackOffset_zero_iff b b).2 rfl
    · have hkOld : k.val - 1 < S.val.length := by
        have hklt : k.val < S.val.length + 1 := by
          simpa [next, nextLength, HelixCandidate.length] using k.isLt
        omega
      obtain ⟨d, hdT, hd⟩ := S.property.2.1 ⟨k.val - 1, hkOld⟩
      refine ⟨d, hdT, ?_⟩
      have hcomp := Arc.stackOffset_trans hb hd
      dsimp [Arc.Stacked] at hb hcomp
      change b.StackOffset d k.val
      have hindex : 1 + (k.val - 1) = k.val := by omega
      simpa [hindex] using hcomp
  · obtain ⟨k, hk⟩ := S.property.2.2
    let k' : Fin next.length := ⟨k.val + 1, by
      change k.val + 1 < S.val.length + 1
      exact Nat.add_lt_add_right k.isLt 1⟩
    refine ⟨k', ?_⟩
    have hcomp := Arc.stackOffset_trans hb hk
    change b.StackOffset a k'.val
    simpa [k', Arc.Stacked, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcomp

end HelixSegmentContaining

/-- Every target pair lies in some exact maximal consecutive run. -/
theorem exists_maximalHelix_containing (T : SecondaryStructure n) (a : Arc n)
    (ha : a ∈ T.arcs) :
    ∃ H : MaximalHelix T, a ∈ helixMembers T H := by
  let initial : HelixSegmentContaining T a :=
    HelixSegmentContaining.singleton T a ha
  obtain ⟨S, _hSuniv, hmax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (HelixSegmentContaining T a))
      (fun S => S.val.length) ⟨initial, Finset.mem_univ initial⟩
  have hrun : IsMaximalHelix T S.val := by
    refine ⟨S.property.1, ?_, ?_, S.property.2.1, ?_⟩
    · let zero : Fin S.val.length := ⟨0, S.property.1⟩
      obtain ⟨b, hbT, hb⟩ := S.property.2.1 zero
      have hbouter : b = S.val.outer := by
        apply (Arc.stackOffset_zero_iff S.val.outer b).1
        simpa [zero] using hb
      exact hbouter ▸ hbT
    · intro hout
      obtain ⟨S', hlt⟩ :=
        HelixSegmentContaining.extendOutward T a S hout
      have hle := hmax S' (Finset.mem_univ S')
      omega
    · intro hin
      obtain ⟨S', hlt⟩ :=
        HelixSegmentContaining.extendInward T a S hin
      have hle := hmax S' (Finset.mem_univ S')
      omega
  let H : MaximalHelix T := ⟨S.val, hrun⟩
  refine ⟨H, ?_⟩
  simp only [helixMembers, Finset.mem_filter]
  exact ⟨ha, S.property.2.2⟩

/-- Every target pair belongs to exactly one maximal helix. -/
theorem existsUnique_maximalHelix_containing (T : SecondaryStructure n)
    (a : Arc n) (ha : a ∈ T.arcs) :
    ∃! H : MaximalHelix T, a ∈ helixMembers T H := by
  obtain ⟨H, haH⟩ := exists_maximalHelix_containing T a ha
  refine ⟨H, haH, ?_⟩
  intro K haK
  exact MaximalHelix.eq_of_common_member haK haH

/-- The canonical maximal helix containing a target pair. -/
noncomputable def maximalHelixContaining (T : SecondaryStructure n) (a : Arc n)
    (ha : a ∈ T.arcs) : MaximalHelix T :=
  Classical.choose (existsUnique_maximalHelix_containing T a ha)

@[simp]
theorem mem_maximalHelixContaining (T : SecondaryStructure n) (a : Arc n)
    (ha : a ∈ T.arcs) :
    a ∈ helixMembers T (maximalHelixContaining T a ha) :=
  (Classical.choose_spec (existsUnique_maximalHelix_containing T a ha)).1

theorem maximalHelixContaining_eq (T : SecondaryStructure n) (a : Arc n)
    (ha : a ∈ T.arcs) (H : MaximalHelix T)
    (haH : a ∈ helixMembers T H) :
    maximalHelixContaining T a ha = H :=
  ((Classical.choose_spec
    (existsUnique_maximalHelix_containing T a ha)).2 H haH).symm

/-! ## Partition statements -/

theorem helixMembers_subset_arcs (T : SecondaryStructure n)
    (H : MaximalHelix T) : helixMembers T H ⊆ T.arcs := by
  intro a ha
  exact (Finset.mem_filter.1 ha).1

/-- The union of the members of all maximal helices is exactly the target's
arc set. -/
theorem biUnion_maximalHelices_members (T : SecondaryStructure n) :
    (maximalHelices T).biUnion (helixMembers T) = T.arcs := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨H, _hHall, haH⟩ := Finset.mem_biUnion.1 ha
    exact helixMembers_subset_arcs T H haH
  · intro a ha
    obtain ⟨H, haH⟩ := exists_maximalHelix_containing T a ha
    exact Finset.mem_biUnion.2 ⟨H, mem_maximalHelices T H, haH⟩

/-- A convenient distinctness form of pairwise disjointness. -/
theorem disjoint_helixMembers_of_ne {T : SecondaryStructure n}
    {H K : MaximalHelix T} (hne : H ≠ K) :
    Disjoint (helixMembers T H) (helixMembers T K) := by
  rcases MaximalHelix.eq_or_disjoint_members H K with hEq | hDisjoint
  · exact False.elim (hne hEq)
  · exact hDisjoint

/-! ## Exact stacks in the interval tree -/

/-- Exact adjacent stack partners are parent and paired child in the interval
tree. -/
theorem parent_eq_some_of_stacked (T : SecondaryStructure n)
    (outer inner : PairedNode T) (hstack : outer.val.Stacked inner.val) :
    parent T (Sum.inl inner) = some outer := by
  apply (parent_eq_iff_isParent T (Sum.inl inner) (some outer)).2
  simp only [IsParent]
  have hcontains : PairedNode.StrictlyContains T outer (Sum.inl inner) := by
    simp only [PairedNode.StrictlyContains]
    unfold Arc.Stacked Arc.StackOffset at hstack
    omega
  refine ⟨hcontains, ?_⟩
  intro q hq
  rcases enclosingPairs_nested T (Sum.inl inner) q outer hq hcontains with
    hqo | hqOuter | houterQ
  · exact Or.inl hqo
  · exact Or.inr hqOuter
  · simp only [PairedNode.StrictlyContains] at hq houterQ
    unfold Arc.Stacked Arc.StackOffset at hstack
    omega

theorem mem_pairedChildren_of_stacked (T : SecondaryStructure n)
    (outer inner : PairedNode T) (hstack : outer.val.Stacked inner.val) :
    inner ∈ pairedChildren T (some outer) := by
  simp only [pairedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
  exact parent_eq_some_of_stacked T outer inner hstack

/-- An exact stacked pair leaves no room for another paired child. -/
theorem pairedChildren_eq_singleton_of_stacked (T : SecondaryStructure n)
    (outer inner : PairedNode T) (hstack : outer.val.Stacked inner.val) :
    pairedChildren T (some outer) = {inner} := by
  ext c
  simp only [Finset.mem_singleton]
  constructor
  · intro hc
    have hcparent : parent T (Sum.inl c) = some outer := by
      simpa [pairedChildren] using hc
    have hccontains := parent_pair_contains T hcparent
    by_cases hleft : c.val.left = inner.val.left
    · exact PairedNode.left_injective T hleft
    by_cases hright : c.val.right = inner.val.right
    · apply Subtype.ext
      exact T.eq_of_mem_of_incident c.property inner.property
        c.val.incident_right (Or.inr hright)
    · have hinnerContains :
          PairedNode.StrictlyContains T inner (Sum.inl c) := by
        simp only [PairedNode.StrictlyContains]
        simp only [PairedNode.StrictlyContains] at hccontains
        unfold Arc.Stacked Arc.StackOffset at hstack
        omega
      have hle := enclosing_left_le_parent T hcparent inner hinnerContains
      unfold Arc.Stacked Arc.StackOffset at hstack
      omega
  · intro hcinner
    simpa [hcinner] using mem_pairedChildren_of_stacked T outer inner hstack

/-- An exact stacked pair also leaves no room for an unpaired child. -/
theorem unpairedChildren_eq_empty_of_stacked (T : SecondaryStructure n)
    (outer inner : PairedNode T) (hstack : outer.val.Stacked inner.val) :
    unpairedChildren T (some outer) = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨u, hu⟩
  have huparent : parent T (Sum.inr u) = some outer := by
    simpa [unpairedChildren] using hu
  have hucontains := parent_pair_contains T huparent
  have hleft : u.val ≠ inner.val.left := by
    intro heq
    apply u.property
    exact ⟨inner.val, inner.property, Or.inl heq⟩
  have hright : u.val ≠ inner.val.right := by
    intro heq
    apply u.property
    exact ⟨inner.val, inner.property, Or.inr heq⟩
  have hinnerContains : PairedNode.StrictlyContains T inner (Sum.inr u) := by
    simp only [PairedNode.StrictlyContains]
    simp only [PairedNode.StrictlyContains] at hucontains
    unfold Arc.Stacked Arc.StackOffset at hstack
    omega
  have hle := enclosing_left_le_parent T huparent inner hinnerContains
  unfold Arc.Stacked Arc.StackOffset at hstack
  omega

/-- The forward half of the manuscript's helix-chain characterization. -/
theorem stacked_implies_unique_pairedChild_no_unpaired
    (T : SecondaryStructure n) (outer inner : PairedNode T)
    (hstack : outer.val.Stacked inner.val) :
    pairedChildren T (some outer) = {inner} ∧
      unpairedChildren T (some outer) = ∅ :=
  ⟨pairedChildren_eq_singleton_of_stacked T outer inner hstack,
    unpairedChildren_eq_empty_of_stacked T outer inner hstack⟩

namespace NonRootNode

/-- Last occupied backbone position, dual to `start`. -/
def finish {T : SecondaryStructure n} : NonRootNode T → Fin n
  | Sum.inl p => p.val.right
  | Sum.inr u => u.val

end NonRootNode

private theorem parent_eq_some_of_contains_start_succ
    (T : SecondaryStructure n) (outer : PairedNode T) (c : NonRootNode T)
    (hcontains : PairedNode.StrictlyContains T outer c)
    (hstart : (NonRootNode.start T c).val = outer.val.left.val + 1) :
    parent T c = some outer := by
  apply (parent_eq_iff_isParent T c (some outer)).2
  simp only [IsParent]
  refine ⟨hcontains, ?_⟩
  intro q hq
  rcases enclosingPairs_nested T c q outer hq hcontains with
    hqo | hqOuter | houterQ
  · exact Or.inl hqo
  · exact Or.inr hqOuter
  · cases c with
    | inl c =>
        simp only [PairedNode.StrictlyContains, NonRootNode.start] at hq houterQ hstart
        omega
    | inr u =>
        simp only [PairedNode.StrictlyContains, NonRootNode.start] at hq houterQ hstart
        omega

private theorem parent_eq_some_of_contains_finish_pred
    (T : SecondaryStructure n) (outer : PairedNode T) (c : NonRootNode T)
    (hcontains : PairedNode.StrictlyContains T outer c)
    (hfinish : (NonRootNode.finish c).val + 1 = outer.val.right.val) :
    parent T c = some outer := by
  apply (parent_eq_iff_isParent T c (some outer)).2
  simp only [IsParent]
  refine ⟨hcontains, ?_⟩
  intro q hq
  rcases enclosingPairs_nested T c q outer hq hcontains with
    hqo | hqOuter | houterQ
  · exact Or.inl hqo
  · exact Or.inr hqOuter
  · cases c with
    | inl c =>
        simp only [PairedNode.StrictlyContains, NonRootNode.finish] at hq houterQ hfinish
        omega
    | inr u =>
        simp only [PairedNode.StrictlyContains, NonRootNode.finish] at hq houterQ hfinish
        omega

/-- If `outer` contains a paired node, some child begins immediately after
`outer`'s left endpoint. -/
theorem exists_child_start_eq_left_succ (T : SecondaryStructure n)
    (outer inner : PairedNode T)
    (hcontains : PairedNode.StrictlyContains T outer (Sum.inl inner)) :
    ∃ c : NonRootNode T,
      parent T c = some outer ∧
        (NonRootNode.start T c).val = outer.val.left.val + 1 := by
  have hbounds := hcontains
  simp only [PairedNode.StrictlyContains] at hbounds
  have hiord := inner.val.ordered
  let x : Fin n := ⟨outer.val.left.val + 1, by
    have := inner.val.left.isLt
    omega⟩
  have hxval : x.val = outer.val.left.val + 1 := rfl
  by_cases hx : T.positionPaired x
  · obtain ⟨a, haT, hxa⟩ := hx
    let q : PairedNode T := ⟨a, haT⟩
    have hqleft : q.val.left = x := by
      rcases hxa with hleft | hright
      · exact hleft.symm
      · have hrightVal : a.right.val = outer.val.left.val + 1 := by
          have he := congrArg Fin.val hright
          omega
        have hqrightVal : q.val.right.val = outer.val.left.val + 1 := by
          simpa [q] using hrightVal
        have hlam := pairedNode_laminar T outer q
        rcases hlam with heq | hd₁ | hd₂ | hn₁ | hn₂
        · have he := congrArg (fun p : PairedNode T => p.val.right.val) heq
          omega
        · have hqord := q.val.ordered
          omega
        · have hqord := q.val.ordered
          omega
        · have hqord := q.val.ordered
          omega
        · omega
    have hqleftVal : q.val.left.val = outer.val.left.val + 1 := by
      have he := congrArg Fin.val hqleft
      omega
    have houterQ : PairedNode.StrictlyContains T outer (Sum.inl q) := by
      have hlam := pairedNode_laminar T outer q
      rcases hlam with heq | hd₁ | hd₂ | hn₁ | hn₂
      · have he := congrArg (fun p : PairedNode T => p.val.left.val) heq
        omega
      · have hqord := q.val.ordered
        omega
      · have hqord := q.val.ordered
        omega
      · exact hn₁
      · omega
    refine ⟨Sum.inl q, ?_, ?_⟩
    · exact parent_eq_some_of_contains_start_succ T outer (Sum.inl q)
        houterQ (by simpa [NonRootNode.start] using hqleftVal)
    · simpa [NonRootNode.start] using hqleftVal
  · let u : UnpairedPosition T := ⟨x, hx⟩
    have houterU : PairedNode.StrictlyContains T outer (Sum.inr u) := by
      simp only [PairedNode.StrictlyContains]
      change outer.val.left.val < x.val ∧ x.val < outer.val.right.val
      omega
    refine ⟨Sum.inr u, ?_, ?_⟩
    · exact parent_eq_some_of_contains_start_succ T outer (Sum.inr u)
        houterU (by simpa [NonRootNode.start, u] using hxval)
    · simpa [NonRootNode.start, u] using hxval

/-- If `outer` contains a paired node, some child ends immediately before
`outer`'s right endpoint. -/
theorem exists_child_finish_add_one_eq_right (T : SecondaryStructure n)
    (outer inner : PairedNode T)
    (hcontains : PairedNode.StrictlyContains T outer (Sum.inl inner)) :
    ∃ c : NonRootNode T,
      parent T c = some outer ∧
        (NonRootNode.finish c).val + 1 = outer.val.right.val := by
  have hbounds := hcontains
  simp only [PairedNode.StrictlyContains] at hbounds
  have hiord := inner.val.ordered
  let y : Fin n := ⟨outer.val.right.val - 1, by
    have := outer.val.right.isLt
    omega⟩
  have hyval : y.val + 1 = outer.val.right.val := by
    dsimp [y]
    have := outer.val.ordered
    omega
  by_cases hy : T.positionPaired y
  · obtain ⟨a, haT, hya⟩ := hy
    let q : PairedNode T := ⟨a, haT⟩
    have hqright : q.val.right = y := by
      rcases hya with hleft | hright
      · have hleftVal : a.left.val + 1 = outer.val.right.val := by
          have he := congrArg Fin.val hleft
          omega
        have hqleftVal : q.val.left.val + 1 = outer.val.right.val := by
          simpa [q] using hleftVal
        have hlam := pairedNode_laminar T outer q
        rcases hlam with heq | hd₁ | hd₂ | hn₁ | hn₂
        · have he := congrArg (fun p : PairedNode T => p.val.left.val) heq
          omega
        · omega
        · have hqord := q.val.ordered
          omega
        · have hqord := q.val.ordered
          omega
        · have hqord := q.val.ordered
          omega
      · exact hright.symm
    have hqrightVal : q.val.right.val + 1 = outer.val.right.val := by
      have he := congrArg Fin.val hqright
      omega
    have houterQ : PairedNode.StrictlyContains T outer (Sum.inl q) := by
      have hlam := pairedNode_laminar T outer q
      rcases hlam with heq | hd₁ | hd₂ | hn₁ | hn₂
      · have he := congrArg (fun p : PairedNode T => p.val.right.val) heq
        omega
      · have hqord := q.val.ordered
        omega
      · omega
      · exact hn₁
      · omega
    refine ⟨Sum.inl q, ?_, ?_⟩
    · exact parent_eq_some_of_contains_finish_pred T outer (Sum.inl q)
        houterQ (by simpa [NonRootNode.finish] using hqrightVal)
    · simpa [NonRootNode.finish] using hqrightVal
  · let u : UnpairedPosition T := ⟨y, hy⟩
    have houterU : PairedNode.StrictlyContains T outer (Sum.inr u) := by
      simp only [PairedNode.StrictlyContains]
      change outer.val.left.val < y.val ∧ y.val < outer.val.right.val
      omega
    refine ⟨Sum.inr u, ?_, ?_⟩
    · exact parent_eq_some_of_contains_finish_pred T outer (Sum.inr u)
        houterU (by simpa [NonRootNode.finish, u] using hyval)
    · simpa [NonRootNode.finish, u] using hyval

/-- A paired node with exactly one paired child and no unpaired child is an
exact one-step stack.  Together with the forward theorem above this is Lemma 4
of the canonical manuscript. -/
theorem stacked_of_unique_pairedChild_no_unpaired
    (T : SecondaryStructure n) (outer inner : PairedNode T)
    (hpaired : pairedChildren T (some outer) = {inner})
    (hunpaired : unpairedChildren T (some outer) = ∅) :
    outer.val.Stacked inner.val := by
  have hinnerMem : inner ∈ pairedChildren T (some outer) := by
    rw [hpaired]
    simp
  have hinnerParent : parent T (Sum.inl inner) = some outer := by
    simpa [pairedChildren] using hinnerMem
  have hcontains := parent_pair_contains T hinnerParent
  have hleft : inner.val.left.val = outer.val.left.val + 1 := by
    obtain ⟨c, hcparent, hcstart⟩ :=
      exists_child_start_eq_left_succ T outer inner hcontains
    cases c with
    | inl q =>
        have hqmem : q ∈ pairedChildren T (some outer) := by
          simpa [pairedChildren] using hcparent
        have hqeq : q = inner := by
          rw [hpaired] at hqmem
          simpa using hqmem
        simpa [hqeq, NonRootNode.start] using hcstart
    | inr u =>
        have humem : u ∈ unpairedChildren T (some outer) := by
          simpa [unpairedChildren] using hcparent
        rw [hunpaired] at humem
        simp at humem
  have hright : inner.val.right.val + 1 = outer.val.right.val := by
    obtain ⟨c, hcparent, hcfinish⟩ :=
      exists_child_finish_add_one_eq_right T outer inner hcontains
    cases c with
    | inl q =>
        have hqmem : q ∈ pairedChildren T (some outer) := by
          simpa [pairedChildren] using hcparent
        have hqeq : q = inner := by
          rw [hpaired] at hqmem
          simpa using hqmem
        simpa [hqeq, NonRootNode.finish] using hcfinish
    | inr u =>
        have humem : u ∈ unpairedChildren T (some outer) := by
          simpa [unpairedChildren] using hcparent
        rw [hunpaired] at humem
        simp at humem
  exact ⟨hleft, hright⟩

theorem stacked_iff_unique_pairedChild_no_unpaired
    (T : SecondaryStructure n) (outer inner : PairedNode T) :
    outer.val.Stacked inner.val ↔
      pairedChildren T (some outer) = {inner} ∧
        unpairedChildren T (some outer) = ∅ := by
  constructor
  · exact stacked_implies_unique_pairedChild_no_unpaired T outer inner
  · rintro ⟨hpaired, hunpaired⟩
    exact stacked_of_unique_pairedChild_no_unpaired T outer inner
      hpaired hunpaired

namespace MaximalHelix

/-! ## Canonical ordering, head, and terminal pair -/

/-- The outermost pair of a maximal helix. -/
def head {T : SecondaryStructure n} (H : MaximalHelix T) : Arc n := H.outer

/-- The target paired node at offset `k`. -/
noncomputable def offsetNode {T : SecondaryStructure n} (H : MaximalHelix T)
    (k : Fin H.length) : PairedNode T :=
  ⟨H.offsetArc k, H.offsetArc_mem k⟩

/-- The outermost target paired node. -/
def headNode {T : SecondaryStructure n} (H : MaximalHelix T) : PairedNode T :=
  ⟨H.head, H.outer_mem⟩

/-- The innermost pair of a maximal helix. -/
noncomputable def terminalPair {T : SecondaryStructure n}
    (H : MaximalHelix T) : Arc n :=
  H.offsetArc ⟨H.length - 1, by have := H.positive; omega⟩

/-- The innermost target paired node. -/
noncomputable def terminalNode {T : SecondaryStructure n}
    (H : MaximalHelix T) : PairedNode T :=
  H.offsetNode ⟨H.length - 1, by have := H.positive; omega⟩

/-- Members in outside-to-inside order. -/
noncomputable def orderedMembers {T : SecondaryStructure n}
    (H : MaximalHelix T) : List (Arc n) :=
  List.ofFn H.offsetArc

@[simp]
theorem orderedMembers_length {T : SecondaryStructure n}
    (H : MaximalHelix T) : H.orderedMembers.length = H.length := by
  simp [orderedMembers]

@[simp]
theorem mem_orderedMembers_iff {T : SecondaryStructure n}
    (H : MaximalHelix T) (a : Arc n) :
    a ∈ H.orderedMembers ↔ ∃ k : Fin H.length, H.offsetArc k = a := by
  simp [orderedMembers]

@[simp]
theorem head_mem {T : SecondaryStructure n} (H : MaximalHelix T) :
    H.head ∈ T.arcs :=
  H.outer_mem

@[simp]
theorem terminalPair_mem {T : SecondaryStructure n} (H : MaximalHelix T) :
    H.terminalPair ∈ T.arcs := by
  exact H.offsetArc_mem _

theorem terminalPair_stackOffset {T : SecondaryStructure n}
    (H : MaximalHelix T) :
    H.head.StackOffset H.terminalPair (H.length - 1) := by
  exact H.offsetArc_stackOffset _

theorem head_eq_offsetArc_zero {T : SecondaryStructure n}
    (H : MaximalHelix T) :
    H.head = H.offsetArc ⟨0, H.positive⟩ := by
  symm
  apply (Arc.stackOffset_zero_iff H.head _).1
  exact H.offsetArc_stackOffset _

/-- Adjacent entries in the canonical member sequence are exact stacked
pairs. -/
theorem offsetArc_stacked_succ {T : SecondaryStructure n}
    (H : MaximalHelix T) (k : Nat) (hk : k + 1 < H.length) :
    (H.offsetArc ⟨k, by omega⟩).Stacked
      (H.offsetArc ⟨k + 1, hk⟩) := by
  have houter := H.offsetArc_stackOffset ⟨k, by omega⟩
  have hinner := H.offsetArc_stackOffset ⟨k + 1, hk⟩
  unfold Arc.Stacked Arc.StackOffset at houter hinner ⊢
  change
    (H.offsetArc ⟨k, by omega⟩).left.val = H.outer.left.val + k ∧
      (H.offsetArc ⟨k, by omega⟩).right.val + k = H.outer.right.val
    at houter
  change
    (H.offsetArc ⟨k + 1, hk⟩).left.val = H.outer.left.val + (k + 1) ∧
      (H.offsetArc ⟨k + 1, hk⟩).right.val + (k + 1) = H.outer.right.val
    at hinner
  omega

/-- The paired node at offset `k+1` has the node at offset `k` as its exact
interval-tree parent. -/
theorem parent_offsetNode_succ {T : SecondaryStructure n}
    (H : MaximalHelix T) (k : Nat) (hk : k + 1 < H.length) :
    parent T (Sum.inl (H.offsetNode ⟨k + 1, hk⟩)) =
      some (H.offsetNode ⟨k, by omega⟩) := by
  apply parent_eq_some_of_stacked
  exact H.offsetArc_stacked_succ k hk

theorem offsetNode_succ_mem_pairedChildren {T : SecondaryStructure n}
    (H : MaximalHelix T) (k : Nat) (hk : k + 1 < H.length) :
    H.offsetNode ⟨k + 1, hk⟩ ∈
      pairedChildren T (some (H.offsetNode ⟨k, by omega⟩)) := by
  simp only [pairedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
  exact H.parent_offsetNode_succ k hk

/-- No target pair continues a maximal helix inward past its terminal pair. -/
theorem terminalPair_no_inward_stacked {T : SecondaryStructure n}
    (H : MaximalHelix T) :
    ¬ ∃ a ∈ T.arcs, H.terminalPair.Stacked a := by
  rintro ⟨a, haT, hstack⟩
  apply H.no_inward
  refine ⟨a, haT, ?_⟩
  have hterminal := H.terminalPair_stackOffset
  have hcomp := Arc.stackOffset_trans hterminal hstack
  have hindex : H.length - 1 + 1 = H.length := by
    have := H.positive
    omega
  change H.head.StackOffset a H.length
  simpa [hindex, Arc.Stacked] using hcomp

/-- A terminal helix node cannot itself have the one-paired-child/no-unpaired
shape that would continue the same helix. -/
theorem terminalNode_not_unique_pairedChild_no_unpaired
    {T : SecondaryStructure n} (H : MaximalHelix T) :
    ¬ ∃ inner : PairedNode T,
      pairedChildren T (some H.terminalNode) = {inner} ∧
        unpairedChildren T (some H.terminalNode) = ∅ := by
  rintro ⟨inner, hpaired, hunpaired⟩
  have hstack := stacked_of_unique_pairedChild_no_unpaired
    T H.terminalNode inner hpaired hunpaired
  apply H.terminalPair_no_inward_stacked
  refine ⟨inner.val, inner.property, ?_⟩
  simpa [terminalNode, terminalPair, offsetNode] using hstack

/-- If a target pair has no target stack predecessor, then any maximal helix
containing it has that pair as its head. -/
theorem head_eq_of_member_of_no_outward_at {T : SecondaryStructure n}
    (H : MaximalHelix T) {a : Arc n} (haH : a ∈ helixMembers T H)
    (hno : ¬ ∃ b ∈ T.arcs, b.Stacked a) : H.head = a := by
  obtain ⟨_haT, k, hk⟩ := Finset.mem_filter.1 haH
  by_cases hkzero : k.val = 0
  · have : a = H.outer := by
      apply (Arc.stackOffset_zero_iff H.outer a).1
      simpa [hkzero] using hk
    simpa [head] using this.symm
  · have hkpos : 0 < k.val := by omega
    let predecessor : Fin H.length := ⟨k.val - 1, by omega⟩
    obtain ⟨b, hbT, hb⟩ := H.has_offset predecessor
    exfalso
    apply hno
    refine ⟨b, hbT, ?_⟩
    unfold Arc.StackOffset at hb hk
    unfold Arc.Stacked Arc.StackOffset
    dsimp [predecessor] at hb
    omega

/-- A paired child of a terminal loop has no outward stack predecessor. -/
theorem no_outward_at_child_of_terminal {T : SecondaryStructure n}
    (G : MaximalHelix T) (c : PairedNode T)
    (hc : c ∈ pairedChildren T (some G.terminalNode)) :
    ¬ ∃ b ∈ T.arcs, b.Stacked c.val := by
  have hcparent : parent T (Sum.inl c) = some G.terminalNode := by
    simpa [pairedChildren] using hc
  rintro ⟨b, hbT, hstack⟩
  let bNode : PairedNode T := ⟨b, hbT⟩
  have hbparent : parent T (Sum.inl c) = some bNode :=
    parent_eq_some_of_stacked T bNode c hstack
  have hbterminal : bNode = G.terminalNode := by
    exact Option.some.inj (hbparent.symm.trans hcparent)
  apply G.terminalPair_no_inward_stacked
  refine ⟨c.val, c.property, ?_⟩
  have : G.terminalNode.val.Stacked c.val := by
    rw [← hbterminal]
    exact hstack
  simpa [terminalNode, terminalPair, offsetNode] using this

/-- A paired child of a loop/terminal node is the head of exactly one outgoing
maximal helix. -/
theorem existsUnique_outgoing_of_terminal_child {T : SecondaryStructure n}
    (G : MaximalHelix T) (c : PairedNode T)
    (hc : c ∈ pairedChildren T (some G.terminalNode)) :
    ∃! H : MaximalHelix T, H.headNode = c := by
  obtain ⟨H, hcH⟩ := exists_maximalHelix_containing T c.val c.property
  have hhead : H.head = c.val :=
    H.head_eq_of_member_of_no_outward_at hcH
      (G.no_outward_at_child_of_terminal c hc)
  have hheadNode : H.headNode = c := by
    apply Subtype.ext
    exact hhead
  refine ⟨H, hheadNode, ?_⟩
  intro K hKhead
  apply MaximalHelix.ext_outer
  change K.head = H.head
  calc
    K.head = c.val := congrArg Subtype.val hKhead
    _ = H.head := hhead.symm

end MaximalHelix

/-! ## The distinguished short helix in class `K` -/

/-- The unique length-two maximal helix selected by class `K`. -/
noncomputable def shortHelix (T : SecondaryStructure n) (hK : InTargetClassK T) :
    MaximalHelix T :=
  Classical.choose (targetClass_has_unique_length_two hK)

@[simp]
theorem shortHelix_length (T : SecondaryStructure n) (hK : InTargetClassK T) :
    (shortHelix T hK).length = 2 :=
  (Classical.choose_spec (targetClass_has_unique_length_two hK)).1

theorem eq_shortHelix_of_length_two (T : SecondaryStructure n)
    (hK : InTargetClassK T) (H : MaximalHelix T) (hlen : H.length = 2) :
    H = shortHelix T hK :=
  (Classical.choose_spec
    (targetClass_has_unique_length_two hK)).2 H hlen

theorem length_ne_two_of_ne_shortHelix (T : SecondaryStructure n)
    (hK : InTargetClassK T) (H : MaximalHelix T)
    (hne : H ≠ shortHelix T hK) : H.length ≠ 2 := by
  intro hlen
  exact hne (eq_shortHelix_of_length_two T hK H hlen)

theorem length_at_least_three_of_ne_shortHelix (T : SecondaryStructure n)
    (hK : InTargetClassK T) (H : MaximalHelix T)
    (hne : H ≠ shortHelix T hK) : 3 ≤ H.length := by
  exact targetClass_other_length_at_least_three hK
    (shortHelix_length T hK) hne

theorem no_maximalHelix_length_one (T : SecondaryStructure n)
    (hK : InTargetClassK T) (H : MaximalHelix T) : H.length ≠ 1 :=
  targetClass_no_length_one hK H

end RNA
