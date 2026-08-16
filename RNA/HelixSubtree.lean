module

public import RNA.LocalAllocations

@[expose] public section

set_option autoImplicit false

/-!
# Maximal-helix subtrees

The paired subtree of a maximal helix consists of its head and every target
pair strictly nested in that head.  The corresponding unpaired subtree
consists of every target-unpaired position strictly nested in the head.

The interval definitions make the domains finite and decidable.  The results
below identify their exact decomposition into the current helix and the
subtrees of the actual outgoing helices.  In particular, they provide the
strict finite-cardinality decrease used by the Milestone 3 recursion.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

namespace PairedNode

/-- Reflexive interval containment between target paired nodes. -/
def WeaklyContains (outer inner : PairedNode T) : Prop :=
  outer = inner ∨ StrictlyContains T outer (Sum.inl inner)

instance instDecidableWeaklyContains (outer inner : PairedNode T) :
    Decidable (WeaklyContains outer inner) := by
  unfold WeaklyContains
  infer_instance

@[simp]
theorem weaklyContains_refl (p : PairedNode T) : p.WeaklyContains p :=
  Or.inl rfl

theorem WeaklyContains.strict_of_ne {outer inner : PairedNode T}
    (h : outer.WeaklyContains inner) (hne : outer ≠ inner) :
    StrictlyContains T outer (Sum.inl inner) := by
  rcases h with heq | hstrict
  · exact False.elim (hne heq)
  · exact hstrict

theorem WeaklyContains.trans {a b c : PairedNode T}
    (hab : a.WeaklyContains b) (hbc : b.WeaklyContains c) :
    a.WeaklyContains c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  · right
    simp only [StrictlyContains] at hab hbc ⊢
    omega

theorem WeaklyContains.trans_strict {a b c : PairedNode T}
    (hab : a.WeaklyContains b)
    (hbc : StrictlyContains T b (Sum.inl c)) :
    StrictlyContains T a (Sum.inl c) := by
  rcases hab with rfl | hab
  · exact hbc
  · simp only [StrictlyContains] at hab hbc ⊢
    omega

theorem StrictlyContains.trans_weaklyContains {a b c : PairedNode T}
    (hab : StrictlyContains T a (Sum.inl b))
    (hbc : b.WeaklyContains c) :
    StrictlyContains T a (Sum.inl c) := by
  rcases hbc with rfl | hbc
  · exact hab
  · simp only [StrictlyContains] at hab hbc ⊢
    omega

theorem StrictlyContains.trans_unpaired {a b : PairedNode T}
    {u : UnpairedPosition T}
    (hab : StrictlyContains T a (Sum.inl b))
    (hbu : StrictlyContains T b (Sum.inr u)) :
    StrictlyContains T a (Sum.inr u) := by
  simp only [StrictlyContains] at hab hbu ⊢
  omega

theorem WeaklyContains.trans_unpaired {a b : PairedNode T}
    {u : UnpairedPosition T} (hab : a.WeaklyContains b)
    (hbu : StrictlyContains T b (Sum.inr u)) :
    StrictlyContains T a (Sum.inr u) := by
  rcases hab with rfl | hab
  · exact hbu
  · exact hab.trans_unpaired hbu

theorem StrictlyContains.not_reverse_weaklyContains {a b : PairedNode T}
    (hab : StrictlyContains T a (Sum.inl b)) :
    ¬ b.WeaklyContains a := by
  intro hba
  rcases hba with hba | hba
  · subst b
    simp only [StrictlyContains] at hab
    omega
  · simp only [StrictlyContains] at hab hba
    omega

end PairedNode

/-- Target paired nodes in the subtree rooted at `H`. -/
def pairedHelixSubtree (T : SecondaryStructure n) (H : MaximalHelix T) :
    Finset (PairedNode T) :=
  Finset.univ.filter (fun p => H.headNode.WeaklyContains p)

/-- Target-unpaired positions in the subtree rooted at `H`. -/
def unpairedHelixSubtree (T : SecondaryStructure n) (H : MaximalHelix T) :
    Finset (UnpairedPosition T) :=
  Finset.univ.filter (fun u =>
    PairedNode.StrictlyContains T H.headNode (Sum.inr u))

/-- The paired-node form of the member set of a maximal helix. -/
def helixMemberNodes (T : SecondaryStructure n) (H : MaximalHelix T) :
    Finset (PairedNode T) :=
  Finset.univ.filter (fun p => p.val ∈ helixMembers T H)

@[simp]
theorem mem_pairedHelixSubtree_iff (H : MaximalHelix T) (p : PairedNode T) :
    p ∈ pairedHelixSubtree T H ↔ H.headNode.WeaklyContains p := by
  simp [pairedHelixSubtree]

@[simp]
theorem mem_unpairedHelixSubtree_iff (H : MaximalHelix T)
    (u : UnpairedPosition T) :
    u ∈ unpairedHelixSubtree T H ↔
      PairedNode.StrictlyContains T H.headNode (Sum.inr u) := by
  simp [unpairedHelixSubtree]

@[simp]
theorem mem_helixMemberNodes_iff (H : MaximalHelix T) (p : PairedNode T) :
    p ∈ helixMemberNodes T H ↔ p.val ∈ helixMembers T H := by
  simp [helixMemberNodes]

/-- Number of target pairs in a maximal helix's complete paired subtree. -/
def helixSubtreePairCount (T : SecondaryStructure n) (H : MaximalHelix T) : Nat :=
  (pairedHelixSubtree T H).card

/-- The actual outgoing maximal helix at a terminal-loop child slot. -/
noncomputable def outgoingHelix (T : SecondaryStructure n)
    (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) : MaximalHelix T :=
  outgoingHelixAtLoopSlot T H.terminalNode ⟨H, rfl⟩ i

@[simp]
theorem outgoingHelix_headNode (T : SecondaryStructure n)
    (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    (outgoingHelix T H i).headNode =
      orderedPairedChild T (some H.terminalNode) i := by
  exact outgoingHelixAtLoopSlot_head T H.terminalNode ⟨H, rfl⟩ i

private theorem headNode_weaklyContains_offsetNode (H : MaximalHelix T)
    (k : Fin H.length) :
    H.headNode.WeaklyContains (H.offsetNode k) := by
  by_cases hk : k.val = 0
  · left
    apply Subtype.ext
    change H.head = H.offsetArc k
    have hzero : k = ⟨0, H.positive⟩ := Fin.ext hk
    rw [hzero]
    exact H.head_eq_offsetArc_zero
  · right
    have hoff := H.offsetArc_stackOffset k
    simp only [PairedNode.StrictlyContains]
    change H.outer.left.val < (H.offsetArc k).left.val ∧
      (H.offsetArc k).right.val < H.outer.right.val
    unfold Arc.StackOffset at hoff
    omega

/-- Every target pair belonging to `H` belongs to the complete paired subtree
rooted at `H`. -/
theorem helixMemberNodes_subset_pairedHelixSubtree (H : MaximalHelix T) :
    helixMemberNodes T H ⊆ pairedHelixSubtree T H := by
  intro p hp
  have hpH : p.val ∈ helixMembers T H :=
    (mem_helixMemberNodes_iff H p).1 hp
  obtain ⟨_hpT, k, hk⟩ := Finset.mem_filter.1 hpH
  apply (mem_pairedHelixSubtree_iff H p).2
  have hcontain := headNode_weaklyContains_offsetNode H k
  have hnode : H.offsetNode k = p := by
    apply Subtype.ext
    exact Arc.stackOffset_arc_unique (H.offsetArc_stackOffset k) hk
  simpa [hnode] using hcontain

/-- The head of `H` is a member of both the helix and its paired subtree. -/
theorem headNode_mem_helixMemberNodes (H : MaximalHelix T) :
    H.headNode ∈ helixMemberNodes T H := by
  apply (mem_helixMemberNodes_iff H H.headNode).2
  simp only [helixMembers, Finset.mem_filter]
  refine ⟨H.outer_mem, ⟨⟨0, H.positive⟩, ?_⟩⟩
  change H.head.StackOffset H.head 0
  exact (Arc.stackOffset_zero_iff H.head H.head).2 rfl

theorem headNode_mem_pairedHelixSubtree (H : MaximalHelix T) :
    H.headNode ∈ pairedHelixSubtree T H :=
  helixMemberNodes_subset_pairedHelixSubtree H (headNode_mem_helixMemberNodes H)

private theorem headNode_weaklyContains_terminalNode (H : MaximalHelix T) :
    H.headNode.WeaklyContains H.terminalNode := by
  let last : Fin H.length :=
    ⟨H.length - 1, by have := H.positive; omega⟩
  simpa [MaximalHelix.terminalNode, last] using
    (headNode_weaklyContains_offsetNode H last)

private theorem terminalNode_strictlyContains_outgoing_head
    (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    PairedNode.StrictlyContains T H.terminalNode
      (Sum.inl (outgoingHelix T H i).headNode) := by
  have hi := orderedPairedChild_mem T (some H.terminalNode) i
  have hparent :
      parent T (Sum.inl (orderedPairedChild T (some H.terminalNode) i)) =
        some H.terminalNode := by
    simpa [pairedChildren] using hi
  have hcontains := parent_pair_contains T hparent
  simpa only [outgoingHelix_headNode] using hcontains

private theorem headNode_strictlyContains_outgoing_head
    (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    PairedNode.StrictlyContains T H.headNode
      (Sum.inl (outgoingHelix T H i).headNode) :=
  (headNode_weaklyContains_terminalNode H).trans_strict
    (terminalNode_strictlyContains_outgoing_head H i)

/-- Every paired node below an outgoing child helix is also below its parent
helix. -/
theorem pairedHelixSubtree_outgoing_subset (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    pairedHelixSubtree T (outgoingHelix T H i) ⊆ pairedHelixSubtree T H := by
  intro p hp
  have hchild := (mem_pairedHelixSubtree_iff (outgoingHelix T H i) p).1 hp
  apply (mem_pairedHelixSubtree_iff H p).2
  exact Or.inr <|
    (headNode_strictlyContains_outgoing_head H i).trans_weaklyContains hchild

/-- Every target-unpaired position below an outgoing child helix is also below
its parent helix. -/
theorem unpairedHelixSubtree_outgoing_subset (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    unpairedHelixSubtree T (outgoingHelix T H i) ⊆
      unpairedHelixSubtree T H := by
  intro u hu
  have hchild :=
    (mem_unpairedHelixSubtree_iff (outgoingHelix T H i) u).1 hu
  apply (mem_unpairedHelixSubtree_iff H u).2
  exact (headNode_strictlyContains_outgoing_head H i).trans_unpaired hchild

/-- An outgoing child helix has a strict paired-subtree inclusion in its
parent helix. -/
theorem pairedHelixSubtree_outgoing_ssubset (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    pairedHelixSubtree T (outgoingHelix T H i) ⊂ pairedHelixSubtree T H := by
  have hsubset := pairedHelixSubtree_outgoing_subset H i
  apply (Finset.ssubset_iff_of_subset hsubset).2
  refine ⟨H.headNode, headNode_mem_pairedHelixSubtree H, ?_⟩
  intro hhead
  have hreverse :=
    (mem_pairedHelixSubtree_iff (outgoingHelix T H i) H.headNode).1 hhead
  exact (headNode_strictlyContains_outgoing_head H i).not_reverse_weaklyContains
    hreverse

/-- The paired-subtree cardinality strictly decreases at every recursive
outgoing-child call. -/
theorem helixSubtreePairCount_outgoing_lt (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    helixSubtreePairCount T (outgoingHelix T H i) <
      helixSubtreePairCount T H := by
  exact Finset.card_lt_card (pairedHelixSubtree_outgoing_ssubset H i)

private theorem parent_outgoingHelix_headNode (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    parent T (Sum.inl (outgoingHelix T H i).headNode) =
      some H.terminalNode := by
  have hi := orderedPairedChild_mem T (some H.terminalNode) i
  have hparent :
      parent T (Sum.inl (orderedPairedChild T (some H.terminalNode) i)) =
        some H.terminalNode := by
    simpa [pairedChildren] using hi
  simpa only [outgoingHelix_headNode] using hparent

private theorem outgoing_heads_interval_disjoint (H : MaximalHelix T)
    {i j : Fin (pairedChildCount T (some H.terminalNode))} (hij : i ≠ j) :
    (outgoingHelix T H i).headNode.val.right <
        (outgoingHelix T H j).headNode.val.left ∨
      (outgoingHelix T H j).headNode.val.right <
        (outgoingHelix T H i).headNode.val.left := by
  let A := (outgoingHelix T H i).headNode
  let B := (outgoingHelix T H j).headNode
  have hAparent : parent T (Sum.inl A) = some H.terminalNode := by
    simpa [A] using parent_outgoingHelix_headNode H i
  have hBparent : parent T (Sum.inl B) = some H.terminalNode := by
    simpa [B] using parent_outgoingHelix_headNode H j
  have hterminalA :
      PairedNode.StrictlyContains T H.terminalNode (Sum.inl A) :=
    parent_pair_contains T hAparent
  have hterminalB :
      PairedNode.StrictlyContains T H.terminalNode (Sum.inl B) :=
    parent_pair_contains T hBparent
  rcases pairedNode_laminar T A B with hAB | hbefore | hafter | hAcontains | hBcontains
  · exfalso
    apply hij
    apply orderedPairedChild_injective T (some H.terminalNode)
    rw [← outgoingHelix_headNode T H i, ← outgoingHelix_headNode T H j]
    exact hAB
  · exact Or.inl hbefore
  · exact Or.inr hafter
  · exfalso
    have hle := enclosing_left_le_parent T hBparent A hAcontains
    simp only [PairedNode.StrictlyContains] at hterminalA
    omega
  · exfalso
    have hle := enclosing_left_le_parent T hAparent B hBcontains
    simp only [PairedNode.StrictlyContains] at hterminalB
    omega

private theorem weaklyContains_bounds {a b : PairedNode T}
    (h : a.WeaklyContains b) :
    a.val.left ≤ b.val.left ∧ b.val.right ≤ a.val.right := by
  rcases h with rfl | h
  · exact ⟨le_rfl, le_rfl⟩
  · simp only [PairedNode.StrictlyContains] at h
    exact ⟨h.1.le, h.2.le⟩

/-- Paired subtrees of distinct outgoing terminal-loop children are disjoint. -/
theorem pairedHelixSubtree_outgoing_disjoint (H : MaximalHelix T)
    {i j : Fin (pairedChildCount T (some H.terminalNode))} (hij : i ≠ j) :
    Disjoint (pairedHelixSubtree T (outgoingHelix T H i))
      (pairedHelixSubtree T (outgoingHelix T H j)) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hi := weaklyContains_bounds
    ((mem_pairedHelixSubtree_iff (outgoingHelix T H i) p).1 hpi)
  have hj := weaklyContains_bounds
    ((mem_pairedHelixSubtree_iff (outgoingHelix T H j) p).1 hpj)
  rcases outgoing_heads_interval_disjoint H hij with hbefore | hafter
  · have hpord := p.val.ordered
    omega
  · have hpord := p.val.ordered
    omega

/-- Unpaired subtrees of distinct outgoing terminal-loop children are
disjoint. -/
theorem unpairedHelixSubtree_outgoing_disjoint (H : MaximalHelix T)
    {i j : Fin (pairedChildCount T (some H.terminalNode))} (hij : i ≠ j) :
    Disjoint (unpairedHelixSubtree T (outgoingHelix T H i))
      (unpairedHelixSubtree T (outgoingHelix T H j)) := by
  rw [Finset.disjoint_left]
  intro u hui huj
  have hi :=
    (mem_unpairedHelixSubtree_iff (outgoingHelix T H i) u).1 hui
  have hj :=
    (mem_unpairedHelixSubtree_iff (outgoingHelix T H j) u).1 huj
  simp only [PairedNode.StrictlyContains] at hi hj
  rcases outgoing_heads_interval_disjoint H hij with hbefore | hafter <;> omega

private theorem memberNode_weaklyContains_terminalNode (H : MaximalHelix T)
    {p : PairedNode T} (hp : p ∈ helixMemberNodes T H) :
    p.WeaklyContains H.terminalNode := by
  have hpH := (mem_helixMemberNodes_iff H p).1 hp
  obtain ⟨_hpT, k, hk⟩ := Finset.mem_filter.1 hpH
  let last : Fin H.length :=
    ⟨H.length - 1, by have := H.positive; omega⟩
  have hlast := H.offsetArc_stackOffset last
  have hkval : k.val ≤ last.val := by
    dsimp [last]
    have hklt := k.isLt
    omega
  by_cases hklast : k.val = last.val
  · left
    apply Subtype.ext
    change p.val = H.offsetArc last
    exact Arc.stackOffset_arc_unique hk (by simpa [hklast] using hlast)
  · right
    simp only [PairedNode.StrictlyContains]
    change p.val.left.val < H.terminalPair.left.val ∧
      H.terminalPair.right.val < p.val.right.val
    unfold Arc.StackOffset at hk hlast
    simp only [MaximalHelix.terminalPair]
    dsimp [last] at hlast ⊢
    constructor <;> omega

/-- No pair belonging to the parent helix itself occurs in an outgoing child
subtree. -/
theorem helixMemberNodes_disjoint_outgoing (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    Disjoint (helixMemberNodes T H)
      (pairedHelixSubtree T (outgoingHelix T H i)) := by
  rw [Finset.disjoint_left]
  intro p hpH hpchild
  have hpTerminal := memberNode_weaklyContains_terminalNode H hpH
  have hpContainsChild :
      PairedNode.StrictlyContains T p
        (Sum.inl (outgoingHelix T H i).headNode) :=
    hpTerminal.trans_strict (terminalNode_strictlyContains_outgoing_head H i)
  have hchildContainsP :=
    (mem_pairedHelixSubtree_iff (outgoingHelix T H i) p).1 hpchild
  exact hpContainsChild.not_reverse_weaklyContains hchildContainsP

/-! ## Immediate-child coverage inside an interval -/

private theorem exists_pairedChild_weaklyContains
    (outer q : PairedNode T)
    (hq : PairedNode.StrictlyContains T outer (Sum.inl q)) :
    ∃ c ∈ pairedChildren T (some outer), c.WeaklyContains q := by
  let candidates : Finset (PairedNode T) :=
    Finset.univ.filter (fun c =>
      PairedNode.StrictlyContains T outer (Sum.inl c) ∧
        c.WeaklyContains q)
  have hcandidates : candidates.Nonempty := by
    refine ⟨q, ?_⟩
    simp [candidates, hq]
  let c : PairedNode T := candidates.min' hcandidates
  have hcMem : c ∈ candidates := Finset.min'_mem candidates hcandidates
  have hcData :
      PairedNode.StrictlyContains T outer (Sum.inl c) ∧
        c.WeaklyContains q := by
    simpa [candidates] using hcMem
  have hcParent : parent T (Sum.inl c) = some outer := by
    apply (parent_eq_iff_isParent T (Sum.inl c) (some outer)).2
    simp only [IsParent]
    refine ⟨hcData.1, ?_⟩
    intro r hr
    rcases pairedNode_laminar T outer r with hor | hbefore | hafter |
        houterR | hrOuter
    · exact Or.inl hor.symm
    · simp only [PairedNode.StrictlyContains] at hcData hr
      have hcord := c.val.ordered
      omega
    · simp only [PairedNode.StrictlyContains] at hcData hr
      have hcord := c.val.ordered
      omega
    · exfalso
      have hrq : r.WeaklyContains q :=
        Or.inr (hr.trans_weaklyContains hcData.2)
      have hrMem : r ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨houterR, hrq⟩
      have hmin : c ≤ r := Finset.min'_le candidates r hrMem
      have hrc : r.val.left < c.val.left := hr.1
      exact (not_lt_of_ge hmin) hrc
    · exact Or.inr hrOuter
  refine ⟨c, ?_, hcData.2⟩
  simpa [pairedChildren] using hcParent

private theorem exists_rootChild_weaklyContains (q : PairedNode T) :
    ∃ c ∈ pairedChildren T none, c.WeaklyContains q := by
  let candidates : Finset (PairedNode T) :=
    Finset.univ.filter (fun c => c.WeaklyContains q)
  have hcandidates : candidates.Nonempty := by
    refine ⟨q, ?_⟩
    simp [candidates]
  let c : PairedNode T := candidates.min' hcandidates
  have hcMem : c ∈ candidates := Finset.min'_mem candidates hcandidates
  have hcq : c.WeaklyContains q := by
    simpa [candidates] using hcMem
  have hcRoot : parent T (Sum.inl c) = none := by
    apply (parent_eq_root_iff T (Sum.inl c)).2
    intro r hr
    have hrq : r.WeaklyContains q :=
      Or.inr (hr.trans_weaklyContains hcq)
    have hrMem : r ∈ candidates := by
      simp [candidates, hrq]
    have hmin : c ≤ r := Finset.min'_le candidates r hrMem
    have hrc : r.val.left < c.val.left := hr.1
    exact (not_lt_of_ge hmin) hrc
  refine ⟨c, ?_, hcq⟩
  simpa [pairedChildren] using hcRoot

/-! ## Peeling the exact stack down to the terminal loop -/

private theorem stacked_funnel_paired (outer inner q : PairedNode T)
    (hstack : outer.val.Stacked inner.val)
    (hq : PairedNode.StrictlyContains T outer (Sum.inl q)) :
    q = inner ∨ PairedNode.StrictlyContains T inner (Sum.inl q) := by
  rcases pairedNode_laminar T inner q with heq | hright | hleft |
      hinner | hqinner
  · exact Or.inl heq.symm
  · exfalso
    simp only [PairedNode.StrictlyContains] at hq
    unfold Arc.Stacked Arc.StackOffset at hstack
    have hqord := q.val.ordered
    omega
  · exfalso
    simp only [PairedNode.StrictlyContains] at hq
    unfold Arc.Stacked Arc.StackOffset at hstack
    have hqord := q.val.ordered
    omega
  · exact Or.inr hinner
  · exfalso
    simp only [PairedNode.StrictlyContains] at hq hqinner
    unfold Arc.Stacked Arc.StackOffset at hstack
    omega

private theorem stacked_funnel_unpaired (outer inner : PairedNode T)
    (u : UnpairedPosition T) (hstack : outer.val.Stacked inner.val)
    (hu : PairedNode.StrictlyContains T outer (Sum.inr u)) :
    PairedNode.StrictlyContains T inner (Sum.inr u) := by
  have hneLeft : u.val ≠ inner.val.left := by
    intro heq
    apply u.property
    exact ⟨inner.val, inner.property, Or.inl heq⟩
  have hneRight : u.val ≠ inner.val.right := by
    intro heq
    apply u.property
    exact ⟨inner.val, inner.property, Or.inr heq⟩
  simp only [PairedNode.StrictlyContains] at hu ⊢
  unfold Arc.Stacked Arc.StackOffset at hstack
  constructor <;> omega

private theorem headNode_eq_offsetNode_zero (H : MaximalHelix T) :
    H.headNode = H.offsetNode ⟨0, H.positive⟩ := by
  apply Subtype.ext
  exact H.head_eq_offsetArc_zero

private theorem pairedSubtree_member_or_terminalContains (H : MaximalHelix T)
    {q : PairedNode T} (hq : q ∈ pairedHelixSubtree T H) :
    q ∈ helixMemberNodes T H ∨
      PairedNode.StrictlyContains T H.terminalNode (Sum.inl q) := by
  let last : Nat := H.length - 1
  have hlastLt : last < H.length := by
    dsimp [last]
    have := H.positive
    omega
  let P : Nat → Prop := fun k =>
    ∀ (hk : k < H.length) (q : PairedNode T),
      (H.offsetNode ⟨k, hk⟩).WeaklyContains q →
        q ∈ helixMemberNodes T H ∨
          PairedNode.StrictlyContains T H.terminalNode (Sum.inl q)
  have hbase : P last := by
    intro hk q hcontains
    have hnode : H.offsetNode ⟨last, hk⟩ = H.terminalNode := by
      apply Subtype.ext
      rfl
    rw [hnode] at hcontains
    rcases hcontains with heq | hstrict
    · left
      subst q
      apply (mem_helixMemberNodes_iff H H.terminalNode).2
      exact H.terminalPair_mem_helixMembers
    · exact Or.inr hstrict
  have hstep :
      ∀ k, k < last → 0 ≤ k → P (k + 1) → P k := by
    intro k hkLast _hkZero ih hk q hcontains
    rcases hcontains with heq | hstrict
    · left
      subst q
      apply (mem_helixMemberNodes_iff H (H.offsetNode ⟨k, hk⟩)).2
      simp only [helixMembers, Finset.mem_filter]
      exact ⟨H.offsetArc_mem _, ⟨⟨k, hk⟩, H.offsetArc_stackOffset _⟩⟩
    · have hkNext : k + 1 < H.length := by
        dsimp [last] at hkLast
        omega
      have hstack := H.offsetArc_stacked_succ k hkNext
      have hfunnel := stacked_funnel_paired
        (H.offsetNode ⟨k, hk⟩) (H.offsetNode ⟨k + 1, hkNext⟩) q
        (by simpa [MaximalHelix.offsetNode] using hstack) hstrict
      have hnextContains :
          (H.offsetNode ⟨k + 1, hkNext⟩).WeaklyContains q := by
        rcases hfunnel with hqNext | hnext
        · exact Or.inl hqNext.symm
        · exact Or.inr hnext
      exact ih hkNext q hnextContains
  have hPzero : P 0 :=
    Nat.decreasingInduction' hstep (Nat.zero_le last) hbase
  have hheadContains := (mem_pairedHelixSubtree_iff H q).1 hq
  have hzeroContains :
      (H.offsetNode ⟨0, H.positive⟩).WeaklyContains q := by
    rw [← headNode_eq_offsetNode_zero H]
    exact hheadContains
  exact hPzero H.positive q hzeroContains

private theorem unpairedSubtree_terminalContains (H : MaximalHelix T)
    {u : UnpairedPosition T} (hu : u ∈ unpairedHelixSubtree T H) :
    PairedNode.StrictlyContains T H.terminalNode (Sum.inr u) := by
  let last : Nat := H.length - 1
  have hlastLt : last < H.length := by
    dsimp [last]
    have := H.positive
    omega
  let P : Nat → Prop := fun k =>
    ∀ (hk : k < H.length),
      PairedNode.StrictlyContains T (H.offsetNode ⟨k, hk⟩) (Sum.inr u) →
        PairedNode.StrictlyContains T H.terminalNode (Sum.inr u)
  have hbase : P last := by
    intro hk hcontains
    have hnode : H.offsetNode ⟨last, hk⟩ = H.terminalNode := by
      apply Subtype.ext
      rfl
    simpa [hnode] using hcontains
  have hstep :
      ∀ k, k < last → 0 ≤ k → P (k + 1) → P k := by
    intro k hkLast _hkZero ih hk hcontains
    have hkNext : k + 1 < H.length := by
      dsimp [last] at hkLast
      omega
    have hstack := H.offsetArc_stacked_succ k hkNext
    have hnext := stacked_funnel_unpaired
      (H.offsetNode ⟨k, hk⟩) (H.offsetNode ⟨k + 1, hkNext⟩) u
      (by simpa [MaximalHelix.offsetNode] using hstack) hcontains
    exact ih hkNext hnext
  have hPzero : P 0 :=
    Nat.decreasingInduction' hstep (Nat.zero_le last) hbase
  have hhead := (mem_unpairedHelixSubtree_iff H u).1 hu
  have hzero :
      PairedNode.StrictlyContains T (H.offsetNode ⟨0, H.positive⟩)
        (Sum.inr u) := by
    rw [← headNode_eq_offsetNode_zero H]
    exact hhead
  exact hPzero H.positive hzero

/-! ## Exact outgoing-forest decomposition -/

/-- Union of the paired subtrees of all actual outgoing helices of `H`. -/
noncomputable def outgoingPairedHelixSubtreeUnion
    (T : SecondaryStructure n) (H : MaximalHelix T) : Finset (PairedNode T) :=
  Finset.univ.biUnion (fun i => pairedHelixSubtree T (outgoingHelix T H i))

/-- Union of the unpaired subtrees of all actual outgoing helices of `H`. -/
noncomputable def outgoingUnpairedHelixSubtreeUnion
    (T : SecondaryStructure n) (H : MaximalHelix T) :
    Finset (UnpairedPosition T) :=
  Finset.univ.biUnion (fun i => unpairedHelixSubtree T (outgoingHelix T H i))

@[simp]
theorem mem_outgoingPairedHelixSubtreeUnion_iff (H : MaximalHelix T)
    (q : PairedNode T) :
    q ∈ outgoingPairedHelixSubtreeUnion T H ↔
      ∃ i : Fin (pairedChildCount T (some H.terminalNode)),
        q ∈ pairedHelixSubtree T (outgoingHelix T H i) := by
  simp [outgoingPairedHelixSubtreeUnion]

@[simp]
theorem mem_outgoingUnpairedHelixSubtreeUnion_iff (H : MaximalHelix T)
    (u : UnpairedPosition T) :
    u ∈ outgoingUnpairedHelixSubtreeUnion T H ↔
      ∃ i : Fin (pairedChildCount T (some H.terminalNode)),
        u ∈ unpairedHelixSubtree T (outgoingHelix T H i) := by
  simp [outgoingUnpairedHelixSubtreeUnion]

/-- The complete paired subtree is exactly the pairs in `H` itself together
with the subtrees of its actual outgoing helices. -/
theorem pairedHelixSubtree_decomposition (H : MaximalHelix T) :
    pairedHelixSubtree T H =
      helixMemberNodes T H ∪ outgoingPairedHelixSubtreeUnion T H := by
  apply Finset.Subset.antisymm
  · intro q hq
    rcases pairedSubtree_member_or_terminalContains H hq with hmember | hterminal
    · exact Finset.mem_union_left _ hmember
    · obtain ⟨c, hcChild, hcq⟩ :=
        exists_pairedChild_weaklyContains H.terminalNode q hterminal
      let i := pairedChildIndex T (some H.terminalNode) c hcChild
      have hhead : (outgoingHelix T H i).headNode = c := by
        calc
          (outgoingHelix T H i).headNode =
              orderedPairedChild T (some H.terminalNode) i :=
            outgoingHelix_headNode T H i
          _ = c := orderedPairedChild_pairedChildIndex
            T (some H.terminalNode) c hcChild
      apply Finset.mem_union_right
      apply (mem_outgoingPairedHelixSubtreeUnion_iff H q).2
      refine ⟨i, ?_⟩
      apply (mem_pairedHelixSubtree_iff (outgoingHelix T H i) q).2
      simpa [hhead] using hcq
  · intro q hq
    rcases Finset.mem_union.1 hq with hmember | houtgoing
    · exact helixMemberNodes_subset_pairedHelixSubtree H hmember
    · obtain ⟨i, hi⟩ :=
        (mem_outgoingPairedHelixSubtreeUnion_iff H q).1 houtgoing
      exact pairedHelixSubtree_outgoing_subset H i hi

/-- The target-unpaired positions below `H` are exactly the direct unpaired
children of its terminal loop together with the unpaired subtrees of its
actual outgoing helices. -/
theorem unpairedHelixSubtree_decomposition (H : MaximalHelix T) :
    unpairedHelixSubtree T H =
      unpairedChildren T (some H.terminalNode) ∪
        outgoingUnpairedHelixSubtreeUnion T H := by
  apply Finset.Subset.antisymm
  · intro u hu
    have hterminal := unpairedSubtree_terminalContains H hu
    cases hparent : parent T (Sum.inr u) with
    | none =>
        have hroot := (parent_eq_root_iff T (Sum.inr u)).1 hparent
        exact False.elim (hroot H.terminalNode hterminal)
    | some p =>
        by_cases hp : p = H.terminalNode
        · apply Finset.mem_union_left
          simpa [unpairedChildren, hp] using hparent
        · apply Finset.mem_union_right
          have hpSmallest := parent_pair_smallest T hparent
          have hterminalP :
              PairedNode.StrictlyContains T H.terminalNode (Sum.inl p) := by
            rcases hpSmallest.2 H.terminalNode hterminal with heq | hcontains
            · exact False.elim (hp heq.symm)
            · exact hcontains
          obtain ⟨c, hcChild, hcp⟩ :=
            exists_pairedChild_weaklyContains H.terminalNode p hterminalP
          let i := pairedChildIndex T (some H.terminalNode) c hcChild
          have hhead : (outgoingHelix T H i).headNode = c := by
            calc
              (outgoingHelix T H i).headNode =
                  orderedPairedChild T (some H.terminalNode) i :=
                outgoingHelix_headNode T H i
              _ = c := orderedPairedChild_pairedChildIndex
                T (some H.terminalNode) c hcChild
          have hpu := parent_pair_contains T hparent
          apply (mem_outgoingUnpairedHelixSubtreeUnion_iff H u).2
          refine ⟨i, ?_⟩
          apply (mem_unpairedHelixSubtree_iff (outgoingHelix T H i) u).2
          rw [hhead]
          exact hcp.trans_unpaired hpu
  · intro u hu
    rcases Finset.mem_union.1 hu with hdirect | houtgoing
    · have hparent : parent T (Sum.inr u) = some H.terminalNode := by
        simpa [unpairedChildren] using hdirect
      have hterminal := parent_pair_contains T hparent
      apply (mem_unpairedHelixSubtree_iff H u).2
      exact (headNode_weaklyContains_terminalNode H).trans_unpaired hterminal
    · obtain ⟨i, hi⟩ :=
        (mem_outgoingUnpairedHelixSubtreeUnion_iff H u).1 houtgoing
      exact unpairedHelixSubtree_outgoing_subset H i hi

/-! ## The virtual-root forest -/

private theorem parent_rootOutgoingHelix_headNode
    (i : Fin (pairedChildCount T none)) :
    parent T (Sum.inl (outgoingHelixAtRootSlot T i).headNode) = none := by
  have hi := orderedPairedChild_mem T none i
  have hparent :
      parent T (Sum.inl (orderedPairedChild T none i)) = none := by
    simpa [pairedChildren] using hi
  simpa only [outgoingHelixAtRootSlot_head] using hparent

private theorem rootOutgoing_heads_interval_disjoint
    {i j : Fin (pairedChildCount T none)} (hij : i ≠ j) :
    (outgoingHelixAtRootSlot T i).headNode.val.right <
        (outgoingHelixAtRootSlot T j).headNode.val.left ∨
      (outgoingHelixAtRootSlot T j).headNode.val.right <
        (outgoingHelixAtRootSlot T i).headNode.val.left := by
  let A := (outgoingHelixAtRootSlot T i).headNode
  let B := (outgoingHelixAtRootSlot T j).headNode
  have hAroot : parent T (Sum.inl A) = none := by
    simpa [A] using parent_rootOutgoingHelix_headNode (T := T) i
  have hBroot : parent T (Sum.inl B) = none := by
    simpa [B] using parent_rootOutgoingHelix_headNode (T := T) j
  rcases pairedNode_laminar T A B with hAB | hbefore | hafter | hAcontains |
      hBcontains
  · exfalso
    apply hij
    apply orderedPairedChild_injective T none
    rw [← outgoingHelixAtRootSlot_head T i,
      ← outgoingHelixAtRootSlot_head T j]
    exact hAB
  · exact Or.inl hbefore
  · exact Or.inr hafter
  · exfalso
    exact (parent_eq_root_iff T (Sum.inl B)).1 hBroot A hAcontains
  · exfalso
    exact (parent_eq_root_iff T (Sum.inl A)).1 hAroot B hBcontains

/-- Paired subtrees of distinct root-child helices are disjoint. -/
theorem pairedHelixSubtree_root_disjoint
    {i j : Fin (pairedChildCount T none)} (hij : i ≠ j) :
    Disjoint (pairedHelixSubtree T (outgoingHelixAtRootSlot T i))
      (pairedHelixSubtree T (outgoingHelixAtRootSlot T j)) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hi := weaklyContains_bounds
    ((mem_pairedHelixSubtree_iff (outgoingHelixAtRootSlot T i) p).1 hpi)
  have hj := weaklyContains_bounds
    ((mem_pairedHelixSubtree_iff (outgoingHelixAtRootSlot T j) p).1 hpj)
  rcases rootOutgoing_heads_interval_disjoint (T := T) hij with hbefore | hafter
  · have hpord := p.val.ordered
    omega
  · have hpord := p.val.ordered
    omega

/-- Unpaired subtrees of distinct root-child helices are disjoint. -/
theorem unpairedHelixSubtree_root_disjoint
    {i j : Fin (pairedChildCount T none)} (hij : i ≠ j) :
    Disjoint (unpairedHelixSubtree T (outgoingHelixAtRootSlot T i))
      (unpairedHelixSubtree T (outgoingHelixAtRootSlot T j)) := by
  rw [Finset.disjoint_left]
  intro u hui huj
  have hi :=
    (mem_unpairedHelixSubtree_iff (outgoingHelixAtRootSlot T i) u).1 hui
  have hj :=
    (mem_unpairedHelixSubtree_iff (outgoingHelixAtRootSlot T j) u).1 huj
  simp only [PairedNode.StrictlyContains] at hi hj
  rcases rootOutgoing_heads_interval_disjoint (T := T) hij with hbefore | hafter <;>
    omega

/-- Union of all paired root-child helix subtrees. -/
noncomputable def rootPairedHelixSubtreeUnion (T : SecondaryStructure n) :
    Finset (PairedNode T) :=
  Finset.univ.biUnion
    (fun i => pairedHelixSubtree T (outgoingHelixAtRootSlot T i))

/-- Union of all unpaired root-child helix subtrees. -/
noncomputable def rootUnpairedHelixSubtreeUnion (T : SecondaryStructure n) :
    Finset (UnpairedPosition T) :=
  Finset.univ.biUnion
    (fun i => unpairedHelixSubtree T (outgoingHelixAtRootSlot T i))

@[simp]
theorem mem_rootPairedHelixSubtreeUnion_iff (q : PairedNode T) :
    q ∈ rootPairedHelixSubtreeUnion T ↔
      ∃ i : Fin (pairedChildCount T none),
        q ∈ pairedHelixSubtree T (outgoingHelixAtRootSlot T i) := by
  simp [rootPairedHelixSubtreeUnion]

@[simp]
theorem mem_rootUnpairedHelixSubtreeUnion_iff (u : UnpairedPosition T) :
    u ∈ rootUnpairedHelixSubtreeUnion T ↔
      ∃ i : Fin (pairedChildCount T none),
        u ∈ unpairedHelixSubtree T (outgoingHelixAtRootSlot T i) := by
  simp [rootUnpairedHelixSubtreeUnion]

/-- Every target paired node lies below exactly one actual root-child helix
(existence here; uniqueness follows from `pairedHelixSubtree_root_disjoint`). -/
theorem rootPairedHelixSubtreeUnion_eq_univ (T : SecondaryStructure n) :
    rootPairedHelixSubtreeUnion T = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro q
  obtain ⟨c, hcRoot, hcq⟩ := exists_rootChild_weaklyContains (T := T) q
  let i := pairedChildIndex T none c hcRoot
  have hhead : (outgoingHelixAtRootSlot T i).headNode = c := by
    calc
      (outgoingHelixAtRootSlot T i).headNode = orderedPairedChild T none i :=
        outgoingHelixAtRootSlot_head T i
      _ = c := orderedPairedChild_pairedChildIndex T none c hcRoot
  apply (mem_rootPairedHelixSubtreeUnion_iff q).2
  refine ⟨i, ?_⟩
  apply (mem_pairedHelixSubtree_iff (outgoingHelixAtRootSlot T i) q).2
  simpa [hhead] using hcq

/-- Expanded form of the root paired-subtree partition. -/
theorem biUnion_root_pairedHelixSubtree (T : SecondaryStructure n) :
    Finset.univ.biUnion
        (fun i => pairedHelixSubtree T (outgoingHelixAtRootSlot T i)) =
      (Finset.univ : Finset (PairedNode T)) := by
  exact rootPairedHelixSubtreeUnion_eq_univ T

/-- A target-unpaired position is a direct child of the virtual root exactly
when it lies in no root-child helix subtree. -/
theorem mem_root_unpairedChildren_iff_not_mem_rootSubtree
    (u : UnpairedPosition T) :
    u ∈ unpairedChildren T none ↔
      u ∉ rootUnpairedHelixSubtreeUnion T := by
  constructor
  · intro huRoot huUnion
    have hparent : parent T (Sum.inr u) = none := by
      simpa [unpairedChildren] using huRoot
    obtain ⟨i, hi⟩ :=
      (mem_rootUnpairedHelixSubtreeUnion_iff u).1 huUnion
    have hcontains :=
      (mem_unpairedHelixSubtree_iff (outgoingHelixAtRootSlot T i) u).1 hi
    exact (parent_eq_root_iff T (Sum.inr u)).1 hparent
      (outgoingHelixAtRootSlot T i).headNode hcontains
  · intro huOutside
    have hparent : parent T (Sum.inr u) = none := by
      cases h : parent T (Sum.inr u) with
      | none => rfl
      | some p =>
          exfalso
          have hpu := parent_pair_contains T h
          obtain ⟨c, hcRoot, hcp⟩ := exists_rootChild_weaklyContains (T := T) p
          let i := pairedChildIndex T none c hcRoot
          have hhead : (outgoingHelixAtRootSlot T i).headNode = c := by
            calc
              (outgoingHelixAtRootSlot T i).headNode =
                  orderedPairedChild T none i :=
                outgoingHelixAtRootSlot_head T i
              _ = c := orderedPairedChild_pairedChildIndex T none c hcRoot
          apply huOutside
          apply (mem_rootUnpairedHelixSubtreeUnion_iff u).2
          refine ⟨i, ?_⟩
          apply (mem_unpairedHelixSubtree_iff (outgoingHelixAtRootSlot T i) u).2
          rw [hhead]
          exact hcp.trans_unpaired hpu
    simpa [unpairedChildren] using hparent

/-- Finset equality form of the root-unpaired complement partition. -/
theorem root_unpairedChildren_eq_compl_rootSubtrees (T : SecondaryStructure n) :
    unpairedChildren T none = Finset.univ \ rootUnpairedHelixSubtreeUnion T := by
  ext u
  simp [mem_root_unpairedChildren_iff_not_mem_rootSubtree]

end RNA
