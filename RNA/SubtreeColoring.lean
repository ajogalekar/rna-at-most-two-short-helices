module

public import RNA.HelixSubtree
public import RNA.HelixTransferBridge

@[expose] public section

set_option autoImplicit false

/-!
# Partial colourings on maximal-helix subtrees

This file contains the finite-domain assignment algebra used by the global
Milestone 3 construction.  A partial colouring is a function on the subtype
of its exact finite domain.  Consequently it has no value, and hence no
hidden dependency, outside that domain.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- A colour assignment whose domain is exactly `D`. -/
abbrev PartialColoring (D : Finset (PairedNode T)) :=
  {p : PairedNode T // p ∈ D} → Color

/-- A partial colouring on exactly the paired subtree rooted at `H`. -/
abbrev SubtreeColoring (H : MaximalHelix T) :=
  PartialColoring (pairedHelixSubtree T H)

/-- A total colouring agrees with a partial colouring on its exact domain. -/
def ExtendsPartial (chi : Coloring T) {D : Finset (PairedNode T)}
    (sigma : PartialColoring D) : Prop :=
  ∀ (p : PairedNode T) (hp : p ∈ D), chi p = sigma ⟨p, hp⟩

/-- Subtree-specialized extension relation. -/
def ExtendsSubtree (chi : Coloring T) {H : MaximalHelix T}
    (sigma : SubtreeColoring H) : Prop :=
  ExtendsPartial chi sigma

/-- Transport a partial colouring across an equality of exact domains. -/
def PartialColoring.cast {D E : Finset (PairedNode T)} (h : D = E)
    (sigma : PartialColoring D) : PartialColoring E := by
  subst E
  exact sigma

@[simp]
theorem PartialColoring.cast_apply {D E : Finset (PairedNode T)}
    (h : D = E) (sigma : PartialColoring D) (p : PairedNode T) (hp : p ∈ E) :
    sigma.cast h ⟨p, hp⟩ = sigma ⟨p, by simpa [h] using hp⟩ := by
  subst E
  rfl

theorem extendsPartial_cast_iff (chi : Coloring T)
    {D E : Finset (PairedNode T)} (h : D = E)
    (sigma : PartialColoring D) :
    ExtendsPartial chi (sigma.cast h) ↔ ExtendsPartial chi sigma := by
  subst E
  rfl

/-! ## Binary and indexed disjoint unions -/

/-- Combine assignments on disjoint domains.  The disjointness premise makes
both original assignments genuine restrictions of the result. -/
def PartialColoring.disjointUnion {D E : Finset (PairedNode T)}
    (sigma : PartialColoring D) (tau : PartialColoring E)
    (_hdisjoint : Disjoint D E) : PartialColoring (D ∪ E) :=
  fun p => if hp : p.1 ∈ D then sigma ⟨p.1, hp⟩ else
    tau ⟨p.1, by
      have hpUnion : p.1 ∈ D ∪ E := p.2
      exact (Finset.mem_union.mp hpUnion).resolve_left hp⟩

@[simp]
theorem PartialColoring.disjointUnion_apply_left
    {D E : Finset (PairedNode T)}
    (sigma : PartialColoring D) (tau : PartialColoring E)
    (hdisjoint : Disjoint D E) (p : PairedNode T) (hp : p ∈ D)
    (hpUnion : p ∈ D ∪ E) :
    sigma.disjointUnion tau hdisjoint ⟨p, hpUnion⟩ = sigma ⟨p, hp⟩ := by
  simp [PartialColoring.disjointUnion, hp]

@[simp]
theorem PartialColoring.disjointUnion_apply_right
    {D E : Finset (PairedNode T)}
    (sigma : PartialColoring D) (tau : PartialColoring E)
    (hdisjoint : Disjoint D E) (p : PairedNode T) (hp : p ∈ E)
    (hpUnion : p ∈ D ∪ E) :
    sigma.disjointUnion tau hdisjoint ⟨p, hpUnion⟩ = tau ⟨p, hp⟩ := by
  have hpNot : p ∉ D := by
    intro hpD
    exact (Finset.disjoint_left.mp hdisjoint) hpD hp
  simp [PartialColoring.disjointUnion, hpNot]

theorem extendsPartial_disjointUnion_iff (chi : Coloring T)
    {D E : Finset (PairedNode T)}
    (sigma : PartialColoring D) (tau : PartialColoring E)
    (hdisjoint : Disjoint D E) :
    ExtendsPartial chi (sigma.disjointUnion tau hdisjoint) ↔
      ExtendsPartial chi sigma ∧ ExtendsPartial chi tau := by
  constructor
  · intro hext
    constructor
    · intro p hp
      have hpUnion : p ∈ D ∪ E := Finset.mem_union_left E hp
      exact (hext p hpUnion).trans
        (sigma.disjointUnion_apply_left tau hdisjoint p hp hpUnion)
    · intro p hp
      have hpUnion : p ∈ D ∪ E := Finset.mem_union_right D hp
      exact (hext p hpUnion).trans
        (sigma.disjointUnion_apply_right tau hdisjoint p hp hpUnion)
  · rintro ⟨hextSigma, hextTau⟩ p hp
    by_cases hpD : p ∈ D
    · rw [sigma.disjointUnion_apply_left tau hdisjoint p hpD hp]
      exact hextSigma p hpD
    · have hpE : p ∈ E := (Finset.mem_union.mp hp).resolve_left hpD
      rw [sigma.disjointUnion_apply_right tau hdisjoint p hpE hp]
      exact hextTau p hpE

section IndexedUnion

variable {I : Type} [Fintype I]

/-- Union of a finite indexed family of partial-colouring domains. -/
def partialColoringFamilyDomain (D : I → Finset (PairedNode T)) :
    Finset (PairedNode T) :=
  Finset.univ.biUnion D

@[simp]
theorem mem_partialColoringFamilyDomain_iff
    (D : I → Finset (PairedNode T)) (p : PairedNode T) :
    p ∈ partialColoringFamilyDomain D ↔ ∃ i : I, p ∈ D i := by
  simp [partialColoringFamilyDomain]

/-- Choose the unique owner of a point in a pairwise-disjoint finite family.
Uniqueness is used below; the choice itself is made only from proved cover. -/
noncomputable def partialColoringFamilyOwner
    (D : I → Finset (PairedNode T)) (p : PairedNode T)
    (hp : p ∈ partialColoringFamilyDomain D) : I :=
  Classical.choose ((mem_partialColoringFamilyDomain_iff D p).1 hp)

theorem partialColoringFamilyOwner_mem
    (D : I → Finset (PairedNode T)) (p : PairedNode T)
    (hp : p ∈ partialColoringFamilyDomain D) :
    p ∈ D (partialColoringFamilyOwner D p hp) :=
  Classical.choose_spec ((mem_partialColoringFamilyDomain_iff D p).1 hp)

theorem partialColoringFamilyOwner_eq_of_mem
    (D : I → Finset (PairedNode T))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (p : PairedNode T) (hpUnion : p ∈ partialColoringFamilyDomain D)
    (i : I) (hp : p ∈ D i) :
    partialColoringFamilyOwner D p hpUnion = i := by
  by_contra hne
  exact (Finset.disjoint_left.mp
    (hdisjoint (partialColoringFamilyOwner D p hpUnion) i hne))
      (partialColoringFamilyOwner_mem D p hpUnion) hp

/-- Flatten a pairwise-disjoint indexed family without an overwrite
convention. -/
noncomputable def flattenPartialColoringFamily
    (D : I → Finset (PairedNode T))
    (sigma : ∀ i, PartialColoring (D i))
    (_hdisjoint : ∀ i j, i ≠ j → Disjoint (D i) (D j)) :
    PartialColoring (partialColoringFamilyDomain D) :=
  fun p =>
    let i := partialColoringFamilyOwner D p.1 p.2
    sigma i ⟨p.1, partialColoringFamilyOwner_mem D p.1 p.2⟩

@[simp]
theorem flattenPartialColoringFamily_apply
    (D : I → Finset (PairedNode T))
    (sigma : ∀ i, PartialColoring (D i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (i : I) (p : PairedNode T) (hp : p ∈ D i)
    (hpUnion : p ∈ partialColoringFamilyDomain D) :
    flattenPartialColoringFamily D sigma hdisjoint ⟨p, hpUnion⟩ =
      sigma i ⟨p, hp⟩ := by
  unfold flattenPartialColoringFamily
  have howner : partialColoringFamilyOwner D p hpUnion = i :=
    partialColoringFamilyOwner_eq_of_mem D hdisjoint p hpUnion i hp
  cases howner
  rfl

theorem extendsPartial_flattenFamily_iff (chi : Coloring T)
    (D : I → Finset (PairedNode T))
    (sigma : ∀ i, PartialColoring (D i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (D i) (D j)) :
    ExtendsPartial chi (flattenPartialColoringFamily D sigma hdisjoint) ↔
      ∀ i, ExtendsPartial chi (sigma i) := by
  constructor
  · intro hext i p hp
    have hpUnion : p ∈ partialColoringFamilyDomain D :=
      (mem_partialColoringFamilyDomain_iff D p).2 ⟨i, hp⟩
    exact (hext p hpUnion).trans
      (flattenPartialColoringFamily_apply D sigma hdisjoint i p hp hpUnion)
  · intro hext p hpUnion
    let i := partialColoringFamilyOwner D p hpUnion
    have hp : p ∈ D i := partialColoringFamilyOwner_mem D p hpUnion
    rw [flattenPartialColoringFamily_apply D sigma hdisjoint i p hp hpUnion]
    exact hext i p hp

end IndexedUnion

/-! ## Totalization from an exact finite cover -/

/-- A partial colouring whose proved domain is all target pairs gives a total
colouring without a default value. -/
def PartialColoring.toColoringOfDomainEqUniv
    {D : Finset (PairedNode T)} (sigma : PartialColoring D)
    (hcover : D = Finset.univ) : Coloring T :=
  fun p => sigma ⟨p, by rw [hcover]; exact Finset.mem_univ p⟩

theorem PartialColoring.extends_toColoringOfDomainEqUniv
    {D : Finset (PairedNode T)} (sigma : PartialColoring D)
    (hcover : D = Finset.univ) :
    ExtendsPartial (sigma.toColoringOfDomainEqUniv hcover) sigma := by
  intro p hp
  rfl

/-! ## Installing a local word on the members of one helix -/

/-- A member of a maximal helix has a unique offset in its canonical order. -/
theorem existsUnique_offsetNode_of_mem_helixMemberNodes
    (H : MaximalHelix T) (p : PairedNode T)
    (hp : p ∈ helixMemberNodes T H) :
    ∃! k : Fin H.length, H.offsetNode k = p := by
  have hpMembers : p.val ∈ helixMembers T H :=
    (mem_helixMemberNodes_iff H p).1 hp
  obtain ⟨_hpTarget, k, hk⟩ := Finset.mem_filter.mp hpMembers
  have hkNode : H.offsetNode k = p := by
    apply Subtype.ext
    exact Arc.stackOffset_arc_unique (H.offsetArc_stackOffset k) hk
  refine ⟨k, hkNode, ?_⟩
  intro j hjNode
  apply H.offsetArc_injective
  exact congrArg Subtype.val (hjNode.trans hkNode.symm)

/-- Canonical offset of a proved helix member. -/
noncomputable def helixMemberOffset (H : MaximalHelix T) (p : PairedNode T)
    (hp : p ∈ helixMemberNodes T H) : Fin H.length :=
  Classical.choose (existsUnique_offsetNode_of_mem_helixMemberNodes H p hp)

@[simp]
theorem offsetNode_helixMemberOffset (H : MaximalHelix T)
    (p : PairedNode T) (hp : p ∈ helixMemberNodes T H) :
    H.offsetNode (helixMemberOffset H p hp) = p :=
  (Classical.choose_spec
    (existsUnique_offsetNode_of_mem_helixMemberNodes H p hp)).1

theorem offsetNode_mem_helixMemberNodes (H : MaximalHelix T)
    (k : Fin H.length) : H.offsetNode k ∈ helixMemberNodes T H := by
  apply (mem_helixMemberNodes_iff H (H.offsetNode k)).2
  simp only [helixMembers, Finset.mem_filter]
  exact ⟨H.offsetArc_mem k, k, H.offsetArc_stackOffset k⟩

@[simp]
theorem helixMemberOffset_offsetNode (H : MaximalHelix T)
    (k : Fin H.length) :
    helixMemberOffset H (H.offsetNode k)
      (offsetNode_mem_helixMemberNodes H k) = k := by
  apply H.offsetArc_injective
  exact congrArg Subtype.val
    (offsetNode_helixMemberOffset H (H.offsetNode k)
      (offsetNode_mem_helixMemberNodes H k))

/-- The local word as a partial assignment on exactly the members of `H`. -/
noncomputable def helixWordPartialColoring (H : MaximalHelix T)
    (colors : List Color) (hlength : colors.length = H.length) :
    PartialColoring (helixMemberNodes T H) :=
  fun p => colors.get
    (Fin.cast hlength.symm (helixMemberOffset H p.1 p.2))

@[simp]
theorem helixWordPartialColoring_offsetNode (H : MaximalHelix T)
    (colors : List Color) (hlength : colors.length = H.length)
    (k : Fin H.length) :
    helixWordPartialColoring H colors hlength
        ⟨H.offsetNode k, offsetNode_mem_helixMemberNodes H k⟩ =
      colors.get (Fin.cast hlength.symm k) := by
  simp [helixWordPartialColoring]

/-- If a total colouring extends the local-word partial assignment, that word
is installed on the actual maximal helix. -/
theorem helixWordInstalled_of_extendsPartial
    (chi : Coloring T) (H : MaximalHelix T) (colors : List Color)
    (hlength : colors.length = H.length)
    (hextends : ExtendsPartial chi
      (helixWordPartialColoring H colors hlength)) :
    HelixWordInstalled chi H colors := by
  unfold HelixWordInstalled helixColorWord
  apply List.ext_get
  · simpa using hlength
  · intro m hmColors hmWord
    rw [List.get_ofFn]
    let k : Fin H.length := ⟨m, by simpa using hmWord⟩
    have hext := hextends (H.offsetNode k)
      (offsetNode_mem_helixMemberNodes H k)
    simpa [k, helixWordPartialColoring] using hext.symm

/-! ## The outgoing-child family of a helix -/

/-- Exact paired domains of all actual outgoing child helices. -/
noncomputable def outgoingSubtreeDomains (H : MaximalHelix T)
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    Finset (PairedNode T) :=
  pairedHelixSubtree T (outgoingHelix T H i)

/-- One exact-domain subtree assignment for every actual outgoing child. -/
abbrev OutgoingSubtreeColorings (H : MaximalHelix T) :=
  ∀ i : Fin (pairedChildCount T (some H.terminalNode)),
    SubtreeColoring (outgoingHelix T H i)

/-- Union of the exact paired domains of all outgoing child subtrees. -/
noncomputable def outgoingSubtreeFamilyDomain (H : MaximalHelix T) :
    Finset (PairedNode T) :=
  partialColoringFamilyDomain (outgoingSubtreeDomains H)

@[simp]
theorem mem_outgoingSubtreeFamilyDomain_iff (H : MaximalHelix T)
    (p : PairedNode T) :
    p ∈ outgoingSubtreeFamilyDomain H ↔
      ∃ i : Fin (pairedChildCount T (some H.terminalNode)),
        p ∈ pairedHelixSubtree T (outgoingHelix T H i) := by
  simp [outgoingSubtreeFamilyDomain, outgoingSubtreeDomains]

/-- Flatten the pairwise-disjoint actual outgoing child assignments. -/
noncomputable def flattenOutgoingSubtreeColorings (H : MaximalHelix T)
    (sigma : OutgoingSubtreeColorings H) :
    PartialColoring (outgoingSubtreeFamilyDomain H) :=
  flattenPartialColoringFamily (outgoingSubtreeDomains H) sigma
    (fun _ _ hij => pairedHelixSubtree_outgoing_disjoint H hij)

@[simp]
theorem flattenOutgoingSubtreeColorings_apply (H : MaximalHelix T)
    (sigma : OutgoingSubtreeColorings H)
    (i : Fin (pairedChildCount T (some H.terminalNode)))
    (p : PairedNode T)
    (hp : p ∈ pairedHelixSubtree T (outgoingHelix T H i))
    (hpUnion : p ∈ outgoingSubtreeFamilyDomain H) :
    flattenOutgoingSubtreeColorings H sigma ⟨p, hpUnion⟩ =
      sigma i ⟨p, hp⟩ := by
  exact flattenPartialColoringFamily_apply (outgoingSubtreeDomains H) sigma
    (fun _ _ hij => pairedHelixSubtree_outgoing_disjoint H hij)
    i p hp hpUnion

theorem extendsPartial_flattenOutgoing_iff (chi : Coloring T)
    (H : MaximalHelix T) (sigma : OutgoingSubtreeColorings H) :
    ExtendsPartial chi (flattenOutgoingSubtreeColorings H sigma) ↔
      ∀ i, ExtendsSubtree chi (sigma i) := by
  exact extendsPartial_flattenFamily_iff chi (outgoingSubtreeDomains H) sigma
    (fun _ _ hij => pairedHelixSubtree_outgoing_disjoint H hij)

/-- The current helix members are disjoint from the union of all outgoing
child-subtree domains. -/
theorem helixMemberNodes_disjoint_outgoingFamily (H : MaximalHelix T) :
    Disjoint (helixMemberNodes T H) (outgoingSubtreeFamilyDomain H) := by
  rw [Finset.disjoint_left]
  intro p hpMember hpOutgoing
  obtain ⟨i, hpChild⟩ :=
    (mem_outgoingSubtreeFamilyDomain_iff H p).1 hpOutgoing
  exact (Finset.disjoint_left.mp
    (helixMemberNodes_disjoint_outgoing H i)) hpMember hpChild

/-- Install the current local word and merge every outgoing subtree.  Its
domain is the disjoint union appearing in the helix-subtree decomposition. -/
noncomputable def mergeHelixWordAndOutgoing (H : MaximalHelix T)
    (colors : List Color) (hlength : colors.length = H.length)
    (children : OutgoingSubtreeColorings H) :
    PartialColoring
      (helixMemberNodes T H ∪ outgoingSubtreeFamilyDomain H) :=
  (helixWordPartialColoring H colors hlength).disjointUnion
    (flattenOutgoingSubtreeColorings H children)
    (helixMemberNodes_disjoint_outgoingFamily H)

@[simp]
theorem mergeHelixWordAndOutgoing_offsetNode (H : MaximalHelix T)
    (colors : List Color) (hlength : colors.length = H.length)
    (children : OutgoingSubtreeColorings H) (k : Fin H.length)
    (hpUnion : H.offsetNode k ∈
      helixMemberNodes T H ∪ outgoingSubtreeFamilyDomain H) :
    mergeHelixWordAndOutgoing H colors hlength children
        ⟨H.offsetNode k, hpUnion⟩ =
      colors.get (Fin.cast hlength.symm k) := by
  rw [mergeHelixWordAndOutgoing,
    PartialColoring.disjointUnion_apply_left
      (sigma := helixWordPartialColoring H colors hlength)
      (tau := flattenOutgoingSubtreeColorings H children)
      (hdisjoint := helixMemberNodes_disjoint_outgoingFamily H)
      (p := H.offsetNode k)
      (hp := offsetNode_mem_helixMemberNodes H k)
      (hpUnion := hpUnion)]
  exact helixWordPartialColoring_offsetNode H colors hlength k

@[simp]
theorem mergeHelixWordAndOutgoing_apply_child (H : MaximalHelix T)
    (colors : List Color) (hlength : colors.length = H.length)
    (children : OutgoingSubtreeColorings H)
    (i : Fin (pairedChildCount T (some H.terminalNode)))
    (p : PairedNode T)
    (hp : p ∈ pairedHelixSubtree T (outgoingHelix T H i))
    (hpUnion : p ∈ helixMemberNodes T H ∪ outgoingSubtreeFamilyDomain H) :
    mergeHelixWordAndOutgoing H colors hlength children ⟨p, hpUnion⟩ =
      children i ⟨p, hp⟩ := by
  have hpOutgoing : p ∈ outgoingSubtreeFamilyDomain H :=
    (mem_outgoingSubtreeFamilyDomain_iff H p).2 ⟨i, hp⟩
  rw [mergeHelixWordAndOutgoing,
    PartialColoring.disjointUnion_apply_right
      (sigma := helixWordPartialColoring H colors hlength)
      (tau := flattenOutgoingSubtreeColorings H children)
      (hdisjoint := helixMemberNodes_disjoint_outgoingFamily H)
      (p := p) (hp := hpOutgoing) (hpUnion := hpUnion)]
  exact flattenOutgoingSubtreeColorings_apply H children i p hp hpOutgoing

/-- Component-domain form of the exact paired-subtree decomposition. -/
theorem helixColoringComponentDomain_eq_subtree (H : MaximalHelix T) :
    helixMemberNodes T H ∪ outgoingSubtreeFamilyDomain H =
      pairedHelixSubtree T H := by
  rw [pairedHelixSubtree_decomposition H]
  rfl

/-- The local helix word and all child assignments, transported along the
proved exact decomposition to a `SubtreeColoring H`. -/
noncomputable def assembleSubtreeColoring (H : MaximalHelix T)
    (colors : List Color) (hlength : colors.length = H.length)
    (children : OutgoingSubtreeColorings H) : SubtreeColoring H :=
  (mergeHelixWordAndOutgoing H colors hlength children).cast
    (helixColoringComponentDomain_eq_subtree H)

@[simp]
theorem assembleSubtreeColoring_offsetNode (H : MaximalHelix T)
    (colors : List Color) (hlength : colors.length = H.length)
    (children : OutgoingSubtreeColorings H) (k : Fin H.length)
    (hpSubtree : H.offsetNode k ∈ pairedHelixSubtree T H) :
    assembleSubtreeColoring H colors hlength children
        ⟨H.offsetNode k, hpSubtree⟩ =
      colors.get (Fin.cast hlength.symm k) := by
  have hpComponents : H.offsetNode k ∈
      helixMemberNodes T H ∪ outgoingSubtreeFamilyDomain H :=
    Finset.mem_union_left _ (offsetNode_mem_helixMemberNodes H k)
  rw [assembleSubtreeColoring, PartialColoring.cast_apply]
  exact mergeHelixWordAndOutgoing_offsetNode H colors hlength children k
    hpComponents

@[simp]
theorem assembleSubtreeColoring_apply_child (H : MaximalHelix T)
    (colors : List Color) (hlength : colors.length = H.length)
    (children : OutgoingSubtreeColorings H)
    (i : Fin (pairedChildCount T (some H.terminalNode)))
    (p : PairedNode T)
    (hp : p ∈ pairedHelixSubtree T (outgoingHelix T H i))
    (hpSubtree : p ∈ pairedHelixSubtree T H) :
    assembleSubtreeColoring H colors hlength children ⟨p, hpSubtree⟩ =
      children i ⟨p, hp⟩ := by
  have hpOutgoing : p ∈ outgoingSubtreeFamilyDomain H :=
    (mem_outgoingSubtreeFamilyDomain_iff H p).2 ⟨i, hp⟩
  have hpComponents : p ∈
      helixMemberNodes T H ∪ outgoingSubtreeFamilyDomain H :=
    Finset.mem_union_right _ hpOutgoing
  rw [assembleSubtreeColoring, PartialColoring.cast_apply]
  exact mergeHelixWordAndOutgoing_apply_child H colors hlength children
    i p hp hpComponents

/-- Extending the assembled subtree is exactly extending its local word and
every child assignment. -/
theorem extendsSubtree_assemble_iff (chi : Coloring T)
    (H : MaximalHelix T) (colors : List Color)
    (hlength : colors.length = H.length)
    (children : OutgoingSubtreeColorings H) :
    ExtendsSubtree chi
        (assembleSubtreeColoring H colors hlength children) ↔
      ExtendsPartial chi (helixWordPartialColoring H colors hlength) ∧
        ∀ i, ExtendsSubtree chi (children i) := by
  rw [ExtendsSubtree, assembleSubtreeColoring,
    extendsPartial_cast_iff, mergeHelixWordAndOutgoing,
    extendsPartial_disjointUnion_iff, extendsPartial_flattenOutgoing_iff]

/-- An extension of the assembled subtree really installs the selected local
word on the actual maximal helix. -/
theorem helixWordInstalled_of_extendsSubtree_assemble
    (chi : Coloring T) (H : MaximalHelix T) (colors : List Color)
    (hlength : colors.length = H.length)
    (children : OutgoingSubtreeColorings H)
    (hextends : ExtendsSubtree chi
      (assembleSubtreeColoring H colors hlength children)) :
    HelixWordInstalled chi H colors := by
  apply helixWordInstalled_of_extendsPartial chi H colors hlength
  exact (extendsSubtree_assemble_iff chi H colors hlength children).1 hextends |>.1

/-- A total extension of the parent assembly restricts to every actual child
subtree assignment. -/
theorem extendsSubtree_child_of_extends_assemble
    (chi : Coloring T) (H : MaximalHelix T) (colors : List Color)
    (hlength : colors.length = H.length)
    (children : OutgoingSubtreeColorings H)
    (hextends : ExtendsSubtree chi
      (assembleSubtreeColoring H colors hlength children))
    (i : Fin (pairedChildCount T (some H.terminalNode))) :
    ExtendsSubtree chi (children i) :=
  ((extendsSubtree_assemble_iff chi H colors hlength children).1 hextends).2 i

/-! ## The virtual-root forest -/

/-- Exact paired domains of all actual root-child helices. -/
noncomputable def rootSubtreeDomains (T : SecondaryStructure n)
    (i : Fin (pairedChildCount T none)) : Finset (PairedNode T) :=
  pairedHelixSubtree T (outgoingHelixAtRootSlot T i)

/-- One exact-domain subtree assignment for every actual root child. -/
abbrev RootSubtreeColorings (T : SecondaryStructure n) :=
  ∀ i : Fin (pairedChildCount T none),
    SubtreeColoring (outgoingHelixAtRootSlot T i)

theorem rootSubtreeDomains_pairwiseDisjoint (T : SecondaryStructure n)
    (i j : Fin (pairedChildCount T none)) (hij : i ≠ j) :
    Disjoint (rootSubtreeDomains T i) (rootSubtreeDomains T j) := by
  exact pairedHelixSubtree_root_disjoint hij

/-- Flatten the pairwise-disjoint root-child subtree assignments. -/
noncomputable def flattenRootSubtreeColorings
    (sigma : RootSubtreeColorings T) :
    PartialColoring (rootPairedHelixSubtreeUnion T) := by
  exact flattenPartialColoringFamily (rootSubtreeDomains T) sigma
    (rootSubtreeDomains_pairwiseDisjoint T)

theorem extendsPartial_flattenRoot_iff (chi : Coloring T)
    (sigma : RootSubtreeColorings T) :
    ExtendsPartial chi (flattenRootSubtreeColorings sigma) ↔
      ∀ i, ExtendsSubtree chi (sigma i) := by
  exact extendsPartial_flattenFamily_iff chi (rootSubtreeDomains T) sigma
    (rootSubtreeDomains_pairwiseDisjoint T)

/-- The root partition totalizes a root forest without choosing any default
colour. -/
noncomputable def coloringOfRootSubtrees
    (sigma : RootSubtreeColorings T) : Coloring T :=
  (flattenRootSubtreeColorings sigma).toColoringOfDomainEqUniv
    (rootPairedHelixSubtreeUnion_eq_univ T)

/-- The total root-forest colouring agrees with every child subtree on its
complete exact domain. -/
theorem coloringOfRootSubtrees_extends (sigma : RootSubtreeColorings T)
    (i : Fin (pairedChildCount T none)) :
    ExtendsSubtree (coloringOfRootSubtrees sigma) (sigma i) := by
  apply (extendsPartial_flattenRoot_iff
    (coloringOfRootSubtrees sigma) sigma).1
  exact PartialColoring.extends_toColoringOfDomainEqUniv
    (flattenRootSubtreeColorings sigma)
    (rootPairedHelixSubtreeUnion_eq_univ T)

end RNA
