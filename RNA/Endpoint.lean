module

public import RNA.Coloring
public import RNA.HelixPartition

@[expose] public section

set_option autoImplicit false

/-!
# Helix endpoints and the L/M/E taxonomy

This module packages Sections 4--6 of the canonical manuscript.  Endpoint
classes are predicates on actual paired interval-tree nodes.  A loop node is
not a second presentation of a helix: it is a paired node together with the
presentation-independent fact that it is the terminal member of a maximal
helix.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-! ## The four motif bounds -/

/-- The four motif bounds, restated at the endpoint-theory interface. -/
theorem endpointMotifBounds (hfree : MotifFree T) :
    (∀ p : PairedNode T,
        HasUnpairedChild T (some p) → pairedChildCount T (some p) ≤ 1) ∧
    (∀ p : PairedNode T,
        ¬ HasUnpairedChild T (some p) → pairedChildCount T (some p) ≤ 3) ∧
    (HasUnpairedChild T none → pairedChildCount T none ≤ 2) ∧
    (¬ HasUnpairedChild T none → pairedChildCount T none ≤ 4) :=
  motifBounds T hfree

/-! ## Terminal nodes -/

/-- A paired interval-tree node is a loop node when it is the terminal
(innermost) member of some maximal helix. -/
noncomputable def IsLoopNode (p : PairedNode T) : Prop :=
  ∃ H : MaximalHelix T, H.terminalNode = p

noncomputable instance (p : PairedNode T) : Decidable (IsLoopNode p) := by
  unfold IsLoopNode
  classical
  infer_instance

/-- Loop nodes as a subtype, when a first-class endpoint is convenient. -/
abbrev LoopNode (T : SecondaryStructure n) :=
  {p : PairedNode T // IsLoopNode p}

/-- The terminal pair belongs to the member set of its maximal helix. -/
theorem MaximalHelix.terminalPair_mem_helixMembers (H : MaximalHelix T) :
    H.terminalPair ∈ helixMembers T H := by
  simp only [helixMembers, Finset.mem_filter]
  refine ⟨H.terminalPair_mem, ?_⟩
  let last : Fin H.length :=
    ⟨H.length - 1, by have := H.positive; omega⟩
  refine ⟨last, ?_⟩
  simpa [MaximalHelix.terminalPair, last] using H.offsetArc_stackOffset last

/-- A loop node determines its maximal helix uniquely.  This makes the
terminal-node definition independent of an arbitrary helix presentation. -/
theorem existsUnique_maximalHelix_of_loopNode (p : PairedNode T)
    (hp : IsLoopNode p) :
    ∃! H : MaximalHelix T, H.terminalNode = p := by
  obtain ⟨H, hHp⟩ := hp
  refine ⟨H, hHp, ?_⟩
  intro K hKp
  have hvalH : H.terminalPair = p.val := congrArg Subtype.val hHp
  have hvalK : K.terminalPair = p.val := congrArg Subtype.val hKp
  exact MaximalHelix.eq_of_common_member (H := K) (K := H) (a := p.val)
    (by simpa [← hvalK] using K.terminalPair_mem_helixMembers)
    (by simpa [← hvalH] using H.terminalPair_mem_helixMembers)

theorem terminalNode_eq_iff {H K : MaximalHelix T}
    (h : H.terminalNode = K.terminalNode) : H = K := by
  apply MaximalHelix.eq_of_common_member (a := H.terminalPair)
  · exact H.terminalPair_mem_helixMembers
  · have hval : H.terminalPair = K.terminalPair := congrArg Subtype.val h
    rw [hval]
    exact K.terminalPair_mem_helixMembers

/-! ## Exact endpoint classes -/

/-- Type `L`: an unpaired child is present and there are zero or one paired
children. -/
def IsLEndpoint (p : PairedNode T) : Prop :=
  HasUnpairedChild T (some p) ∧
    (pairedChildCount T (some p) = 0 ∨
      pairedChildCount T (some p) = 1)

/-- Type `M`: no unpaired child is present and there are two or three paired
children. -/
def IsMEndpoint (p : PairedNode T) : Prop :=
  ¬ HasUnpairedChild T (some p) ∧
    (pairedChildCount T (some p) = 2 ∨
      pairedChildCount T (some p) = 3)

/-- Type `E`: the paired node has no child at all. -/
def IsEEndpoint (p : PairedNode T) : Prop :=
  ¬ HasUnpairedChild T (some p) ∧
    pairedChildCount T (some p) = 0

instance (p : PairedNode T) : Decidable (IsLEndpoint p) := by
  unfold IsLEndpoint
  infer_instance

instance (p : PairedNode T) : Decidable (IsMEndpoint p) := by
  unfold IsMEndpoint
  infer_instance

instance (p : PairedNode T) : Decidable (IsEEndpoint p) := by
  unfold IsEEndpoint
  infer_instance

/-- The finite endpoint tag used by allocation case splits. -/
inductive EndpointType where
  | L
  | M
  | E
  deriving DecidableEq, Repr

instance : Fintype EndpointType where
  elems := {EndpointType.L, EndpointType.M, EndpointType.E}
  complete := by intro e; cases e <;> simp

/-- A node has the endpoint class named by the tag. -/
def HasEndpointType (p : PairedNode T) : EndpointType → Prop
  | .L => IsLEndpoint p
  | .M => IsMEndpoint p
  | .E => IsEEndpoint p

instance (p : PairedNode T) (e : EndpointType) :
    Decidable (HasEndpointType p e) := by
  cases e <;> simp only [HasEndpointType] <;> infer_instance

/-- The L, M, and E predicates are pairwise disjoint. -/
theorem endpointType_unique (p : PairedNode T) {e f : EndpointType}
    (he : HasEndpointType p e) (hf : HasEndpointType p f) : e = f := by
  cases e <;> cases f <;>
    simp_all [HasEndpointType, IsLEndpoint, IsMEndpoint, IsEEndpoint]

/-- A finite set of paired children has count zero exactly when it is empty. -/
theorem pairedChildCount_eq_zero_iff (p : PairedOrRootNode T) :
    pairedChildCount T p = 0 ↔ pairedChildren T p = ∅ := by
  simp [pairedChildCount]

/-- Absence of an unpaired child is equivalent to an empty unpaired-child
set. -/
theorem noUnpairedChild_iff (p : PairedOrRootNode T) :
    ¬ HasUnpairedChild T p ↔ unpairedChildren T p = ∅ := by
  simp [HasUnpairedChild]

/-! ## Helix chains and complete endpoint coverage -/

/-- The precise tree characterization of an exact consecutive stack. -/
theorem helixChain_iff (outer inner : PairedNode T) :
    outer.val.Stacked inner.val ↔
      pairedChildren T (some outer) = {inner} ∧
        unpairedChildren T (some outer) = ∅ :=
  stacked_iff_unique_pairedChild_no_unpaired T outer inner

/-- Consecutive members of the canonical maximal-helix ordering have exactly
the one-child/no-unpaired tree shape. -/
theorem maximalHelix_consecutive_tree_shape (H : MaximalHelix T)
    (k : Nat) (hk : k + 1 < H.length) :
    pairedChildren T (some (H.offsetNode ⟨k, by omega⟩)) =
        {H.offsetNode ⟨k + 1, hk⟩} ∧
      unpairedChildren T (some (H.offsetNode ⟨k, by omega⟩)) = ∅ := by
  apply (helixChain_iff _ _).1
  exact H.offsetArc_stacked_succ k hk

/-- Every target pair that does not have the continuation shape is the
terminal node of its canonical maximal helix. -/
theorem isLoopNode_of_not_unique_pairedChild_no_unpaired (p : PairedNode T)
    (hstop : ¬ ∃ inner : PairedNode T,
      pairedChildren T (some p) = {inner} ∧
        unpairedChildren T (some p) = ∅) :
    IsLoopNode p := by
  obtain ⟨H, hpH⟩ := exists_maximalHelix_containing T p.val p.property
  obtain ⟨_hpT, k, hk⟩ := Finset.mem_filter.1 hpH
  have hoffset : H.offsetArc k = p.val :=
    Arc.stackOffset_arc_unique (H.offsetArc_stackOffset k) hk
  have hlast : k.val = H.length - 1 := by
    by_contra hne
    have hsucc : k.val + 1 < H.length := by
      have := k.isLt
      omega
    let next : PairedNode T := H.offsetNode ⟨k.val + 1, hsucc⟩
    apply hstop
    refine ⟨next, ?_⟩
    apply (helixChain_iff p next).1
    have hs := H.offsetArc_stacked_succ k.val hsucc
    simpa [next, MaximalHelix.offsetNode, hoffset] using hs
  refine ⟨H, ?_⟩
  apply Subtype.ext
  have hterminal := H.terminalPair_stackOffset
  apply Arc.stackOffset_arc_unique hterminal
  simpa [hlast, MaximalHelix.head] using hk

/-- Each of the three endpoint predicates itself rules out continuation and
therefore identifies a genuine maximal-helix terminal node. -/
theorem isLoopNode_of_endpointType (p : PairedNode T) (e : EndpointType)
    (he : HasEndpointType p e) : IsLoopNode p := by
  apply isLoopNode_of_not_unique_pairedChild_no_unpaired p
  rintro ⟨inner, hpaired, hunpaired⟩
  have hcard : pairedChildCount T (some p) = 1 := by
    simp [pairedChildCount, hpaired]
  cases e with
  | L =>
      have hu := he.1
      rw [HasUnpairedChild, hunpaired] at hu
      exact Finset.not_nonempty_empty hu
  | M =>
      rcases he.2 with htwo | hthree <;> omega
  | E =>
      have hzero := he.2
      omega

/-- The terminal node of a maximal helix never has the absent one-paired-
child/no-unpaired endpoint shape. -/
theorem loopNode_not_absent_case (p : PairedNode T) (hp : IsLoopNode p) :
    ¬ (¬ HasUnpairedChild T (some p) ∧
      pairedChildCount T (some p) = 1) := by
  obtain ⟨H, hHp⟩ := hp
  rintro ⟨hno, hone⟩
  obtain ⟨inner, hinner⟩ := Finset.card_eq_one.mp (by
    simpa [pairedChildCount] using hone)
  apply H.terminalNode_not_unique_pairedChild_no_unpaired
  refine ⟨inner, ?_, ?_⟩
  · simpa [hHp] using hinner
  · have hempty := (noUnpairedChild_iff (T := T) (some p)).1 hno
    simpa [hHp] using hempty

/-- Every loop node in a motif-free target is covered by L, M, or E. -/
theorem loopNode_endpointType_exists (hfree : MotifFree T)
    (p : PairedNode T) (hp : IsLoopNode p) :
    ∃ e : EndpointType, HasEndpointType p e := by
  by_cases hu : HasUnpairedChild T (some p)
  · have hle := paired_pairedChildren_le_one_of_unpaired T hfree p hu
    refine ⟨.L, hu, ?_⟩
    omega
  · have hle := paired_pairedChildren_le_three_of_no_unpaired T hfree p hu
    have hnotOne := loopNode_not_absent_case p hp
    have hneOne : pairedChildCount T (some p) ≠ 1 := by
      intro hone
      exact hnotOne ⟨hu, hone⟩
    rcases Nat.eq_zero_or_pos (pairedChildCount T (some p)) with hzero | hpos
    · exact ⟨.E, hu, hzero⟩
    · refine ⟨.M, hu, ?_⟩
      omega

/-- Complete, exclusive L/M/E taxonomy for every nonroot loop node. -/
theorem existsUnique_endpointType_of_loopNode (hfree : MotifFree T)
    (p : PairedNode T) (hp : IsLoopNode p) :
    ∃! e : EndpointType, HasEndpointType p e := by
  obtain ⟨e, he⟩ := loopNode_endpointType_exists hfree p hp
  exact ⟨e, he, fun f hf => endpointType_unique p hf he⟩

/-- Class-K specialization of complete endpoint coverage. -/
theorem targetClass_loopNode_endpointType (hK : InTargetClassK T)
    (p : PairedNode T) (hp : IsLoopNode p) :
    ∃! e : EndpointType, HasEndpointType p e :=
  existsUnique_endpointType_of_loopNode (targetClass_motifFree hK) p hp

/-- The parent of a maximal-helix head, when nonroot, cannot have the absent
continuation shape: that would put the parent in the same maximal helix. -/
theorem parentOfHead_not_absent_case (H : MaximalHelix T) (p : PairedNode T)
    (hp : parent T (Sum.inl H.headNode) = some p) :
    ¬ (¬ HasUnpairedChild T (some p) ∧
      pairedChildCount T (some p) = 1) := by
  rintro ⟨hno, hone⟩
  obtain ⟨inner, hinner⟩ := Finset.card_eq_one.mp (by
    simpa [pairedChildCount] using hone)
  have hheadMem : H.headNode ∈ pairedChildren T (some p) := by
    simpa [pairedChildren] using hp
  have hheadEq : H.headNode = inner := by
    simpa [hinner] using hheadMem
  have hstack : p.val.Stacked H.headNode.val := by
    apply stacked_of_unique_pairedChild_no_unpaired T p H.headNode
    · simpa [hheadEq] using hinner
    · exact (noUnpairedChild_iff (T := T) (some p)).1 hno
  exact H.no_outward ⟨p.val, p.property, by
    simpa [MaximalHelix.headNode, MaximalHelix.head] using hstack⟩

/-- A nonroot parent of a maximal-helix head is a genuine loop node of type
L with exactly one paired child, or of type M; it is never E. -/
theorem nonroot_parentOfHead_classification (hfree : MotifFree T)
    (H : MaximalHelix T) (p : PairedNode T)
    (hp : parent T (Sum.inl H.headNode) = some p) :
    IsLoopNode p ∧
      ((IsLEndpoint p ∧ pairedChildCount T (some p) = 1) ∨
        IsMEndpoint p) := by
  have hheadMem : H.headNode ∈ pairedChildren T (some p) := by
    simpa [pairedChildren] using hp
  have hpos : 0 < pairedChildCount T (some p) := by
    rw [pairedChildCount]
    exact Finset.card_pos.mpr ⟨H.headNode, hheadMem⟩
  have hnot := parentOfHead_not_absent_case H p hp
  have hstop : ¬ ∃ inner : PairedNode T,
      pairedChildren T (some p) = {inner} ∧
        unpairedChildren T (some p) = ∅ := by
    rintro ⟨inner, hpaired, hunpaired⟩
    apply hnot
    refine ⟨(noUnpairedChild_iff (T := T) (some p)).2 hunpaired, ?_⟩
    simp [pairedChildCount, hpaired]
  refine ⟨isLoopNode_of_not_unique_pairedChild_no_unpaired p hstop, ?_⟩
  by_cases hu : HasUnpairedChild T (some p)
  · left
    have hle := paired_pairedChildren_le_one_of_unpaired T hfree p hu
    have hone : pairedChildCount T (some p) = 1 := by omega
    exact ⟨⟨hu, Or.inr hone⟩, hone⟩
  · right
    have hle := paired_pairedChildren_le_three_of_no_unpaired T hfree p hu
    have hneOne : pairedChildCount T (some p) ≠ 1 := by
      intro hone
      exact hnot ⟨hu, hone⟩
    exact ⟨hu, by omega⟩

/-- The root/nonroot interface split for every maximal-helix head. -/
theorem parentOfHead_root_or_classified (hfree : MotifFree T)
    (H : MaximalHelix T) :
    parent T (Sum.inl H.headNode) = none ∨
      ∃ p : PairedNode T,
        parent T (Sum.inl H.headNode) = some p ∧
          IsLoopNode p ∧
          ((IsLEndpoint p ∧ pairedChildCount T (some p) = 1) ∨
            IsMEndpoint p) := by
  cases hp : parent T (Sum.inl H.headNode) with
  | none => exact Or.inl rfl
  | some p =>
      right
      exact ⟨p, rfl, nonroot_parentOfHead_classification hfree H p hp⟩

/-- A paired child of the virtual root has no stacked predecessor. -/
theorem no_outward_at_root_child (c : PairedNode T)
    (hc : c ∈ pairedChildren T none) :
    ¬ ∃ b ∈ T.arcs, b.Stacked c.val := by
  have hcparent : parent T (Sum.inl c) = none := by
    simpa [pairedChildren] using hc
  rintro ⟨b, hbT, hstack⟩
  let bNode : PairedNode T := ⟨b, hbT⟩
  have hbparent : parent T (Sum.inl c) = some bNode :=
    parent_eq_some_of_stacked T bNode c hstack
  rw [hcparent] at hbparent
  simp at hbparent

/-- A paired child of the virtual root is the head of exactly one outgoing
maximal helix. -/
theorem existsUnique_outgoing_of_root_child (c : PairedNode T)
    (hc : c ∈ pairedChildren T none) :
    ∃! H : MaximalHelix T, H.headNode = c := by
  obtain ⟨H, hcH⟩ := exists_maximalHelix_containing T c.val c.property
  have hhead : H.head = c.val :=
    H.head_eq_of_member_of_no_outward_at hcH
      (no_outward_at_root_child c hc)
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

/-- A paired child of any loop node is the head of exactly one outgoing
maximal helix, independently of the presentation witnessing loophood. -/
theorem existsUnique_outgoing_of_loop_child (p : PairedNode T)
    (hp : IsLoopNode p) (c : PairedNode T)
    (hc : c ∈ pairedChildren T (some p)) :
    ∃! H : MaximalHelix T, H.headNode = c := by
  obtain ⟨G, hGp⟩ := hp
  apply G.existsUnique_outgoing_of_terminal_child c
  simpa [hGp] using hc

/-- Class K is nonempty, hence the root has at least one paired child. -/
theorem targetClass_root_pairedChildCount_pos (hK : InTargetClassK T) :
    0 < pairedChildCount T none := by
  let witness : PairedNode T := (shortHelix T hK).headNode
  let roots : Finset (PairedNode T) := Finset.univ
  have hroots : roots.Nonempty := ⟨witness, Finset.mem_univ _⟩
  let top : PairedNode T := roots.min' hroots
  have htopRoot : parent T (Sum.inl top) = none := by
    apply (parent_eq_root_iff T (Sum.inl top)).2
    intro q hq
    have hqLeft : q.val.left < top.val.left := hq.1
    have hqTop : q < top := hqLeft
    have hmin : top ≤ q := Finset.min'_le roots q (Finset.mem_univ q)
    exact (not_lt_of_ge hmin) hqTop
  rw [pairedChildCount, Finset.card_pos]
  exact ⟨top, by simpa [pairedChildren] using htopRoot⟩

/-! ## Strong two-separation with a named residue -/

/-- The witness-bearing form of global strong two-separation.  This is stated
using the global level functions from `RNA.Coloring`, not a local surrogate. -/
def StrongTwoSeparatedWith (χ : Coloring T) (xi : Parity) : Prop :=
  (∀ u : UnpairedPosition T, levelParity (unpairedLevel χ u) = xi) ∧
    (∀ g : PairedNode T, χ g = Color.grey →
      levelParity (pairedLevel χ g) = xi.opposite)

theorem strongTwoSeparated_iff_exists_with (χ : Coloring T) :
    StrongTwoSeparated χ ↔ ∃ xi, StrongTwoSeparatedWith χ xi := by
  rfl

/-- At an L endpoint, its inclusive level is the unpaired residue. -/
theorem lEndpoint_level_residue (χ : Coloring T) (xi : Parity)
    (hsep : StrongTwoSeparatedWith χ xi) (p : PairedNode T)
    (hL : IsLEndpoint p) :
    levelParity (pairedLevel χ p) = xi := by
  obtain ⟨u, hu⟩ := hL.1
  rw [← unpairedLevel_of_mem_pairedChildren χ hu]
  exact hsep.1 u

/-- An L endpoint cannot itself be grey. -/
theorem lEndpoint_color_nonGrey (χ : Coloring T) (xi : Parity)
    (hsep : StrongTwoSeparatedWith χ xi) (p : PairedNode T)
    (hL : IsLEndpoint p) :
    (χ p).NonGrey := by
  intro hpGrey
  have hpResidue := hsep.2 p hpGrey
  have hLResidue := lEndpoint_level_residue χ xi hsep p hL
  exact xi.ne_opposite (hLResidue.symm.trans hpResidue)

/-- Every paired child port of an L endpoint is non-grey. -/
theorem lEndpoint_child_color_nonGrey (χ : Coloring T) (xi : Parity)
    (hsep : StrongTwoSeparatedWith χ xi) (p u : PairedNode T)
    (hL : IsLEndpoint p) (hu : u ∈ pairedChildren T (some p)) :
    (χ u).NonGrey := by
  intro huGrey
  have hchildLevel : pairedLevel χ u = pairedLevel χ p := by
    rw [pairedLevel_eq_entry_add_delta,
      entryLevel_of_mem_pairedChildren χ hu, huGrey]
    simp
  have huResidue := hsep.2 u huGrey
  have hpResidue := lEndpoint_level_residue χ xi hsep p hL
  rw [hchildLevel] at huResidue
  exact xi.ne_opposite (hpResidue.symm.trans huResidue)

/-- A proper exposure of cardinality at least three contains grey. -/
theorem grey_mem_of_properExposure_of_card_ge_three
    (X : Multiset Color) (hproper : ProperExposure X) (hcard : 3 ≤ X.card) :
    Color.grey ∈ X := by
  by_contra hgrey
  have hle : X ≤ ({Color.black, Color.white} : Multiset Color) := by
    rw [Multiset.le_iff_count]
    intro c
    cases c with
    | black => simpa using hproper.1
    | white => simpa using hproper.2.1
    | grey =>
        have hz : X.count Color.grey = 0 :=
          Multiset.count_eq_zero.mpr hgrey
        simp [hz]
  have := Multiset.card_le_card hle
  simp at this
  omega

/-- The exposure at a paired node has one closing incidence plus one entry
for each paired child. -/
theorem exposedMultiset_card (χ : Coloring T) (p : PairedNode T) :
    (exposedMultiset χ (some p)).card =
      1 + pairedChildCount T (some p) := by
  simp [exposedMultiset, childColorMultiset, pairedChildCount, Nat.add_comm]

/-- At an M endpoint, some exposed incidence is grey. -/
theorem mEndpoint_grey_exposed (χ : Coloring T) (p : PairedNode T)
    (hproper : ProperColoring χ) (hM : IsMEndpoint p) :
    Color.grey ∈ exposedMultiset χ (some p) := by
  apply grey_mem_of_properExposure_of_card_ge_three
  · exact hproper (some p)
  · rw [exposedMultiset_card]
    rcases hM.2 with htwo | hthree <;> omega

/-- An M endpoint lies at the grey residue. -/
theorem mEndpoint_level_residue (χ : Coloring T) (xi : Parity)
    (hproper : ProperColoring χ) (hsep : StrongTwoSeparatedWith χ xi)
    (p : PairedNode T) (hM : IsMEndpoint p) :
    levelParity (pairedLevel χ p) = xi.opposite := by
  have hgrey := mEndpoint_grey_exposed χ p hproper hM
  simp only [exposedMultiset_paired, Multiset.mem_add,
    Multiset.mem_singleton, childColorMultiset, Multiset.mem_map] at hgrey
  rcases hgrey with hclosing | ⟨u, hu, huGrey⟩
  · have hpGrey : χ p = Color.grey := by
      exact (Color.inv_eq_grey_iff (χ p)).1 hclosing.symm
    exact hsep.2 p hpGrey
  · have hentry := entryLevel_of_mem_pairedChildren χ hu
    have hchildLevel : pairedLevel χ u = pairedLevel χ p := by
      rw [pairedLevel_eq_entry_add_delta, hentry, huGrey]
      simp
    rw [← hchildLevel]
    exact hsep.2 u huGrey

/-- The forced-residue package used by later allocation proofs. -/
theorem endpoint_forcedResidues (χ : Coloring T) (xi : Parity)
    (hproper : ProperColoring χ) (hsep : StrongTwoSeparatedWith χ xi)
    (p : PairedNode T) :
    (IsLEndpoint p →
      levelParity (pairedLevel χ p) = xi ∧
      (χ p).NonGrey ∧
      ∀ u ∈ pairedChildren T (some p), (χ u).NonGrey) ∧
    (IsMEndpoint p →
      levelParity (pairedLevel χ p) = xi.opposite) := by
  constructor
  · intro hL
    exact ⟨lEndpoint_level_residue χ xi hsep p hL,
      lEndpoint_color_nonGrey χ xi hsep p hL,
      fun u hu => lEndpoint_child_color_nonGrey χ xi hsep p u hL hu⟩
  · intro hM
    exact mEndpoint_level_residue χ xi hproper hsep p hM

/-- Direct wrapper from the global existential strong-two-separation
predicate: one witness residue simultaneously supplies all L/M forced-residue
facts. -/
theorem forcedResidues_of_proper_strongTwoSeparated (χ : Coloring T)
    (hproper : ProperColoring χ) (hstrong : StrongTwoSeparated χ) :
    ∃ xi : Parity,
      StrongTwoSeparatedWith χ xi ∧
      ∀ p : PairedNode T,
        (IsLEndpoint p →
          levelParity (pairedLevel χ p) = xi ∧
          (χ p).NonGrey ∧
          ∀ u ∈ pairedChildren T (some p), (χ u).NonGrey) ∧
        (IsMEndpoint p →
          levelParity (pairedLevel χ p) = xi.opposite) := by
  obtain ⟨xi, hsep⟩ := hstrong
  refine ⟨xi, hsep, ?_⟩
  intro p
  exact endpoint_forcedResidues χ xi hproper hsep p

end RNA
