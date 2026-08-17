module

public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Fin.Basic
public import RNA.Structure

@[expose] public section

set_option autoImplicit false

/-!
# Order-preserving transport of secondary structures

All operations in this file preserve the backbone order.  In particular, an
arbitrary order embedding may leave gaps in the larger backbone; this is the
operation needed when adjacent positions or a common unpaired set are deleted.
-/

namespace RNA

variable {m n k : Nat}

namespace Arc

/-- Map both endpoints of an arc through an order embedding. -/
def mapOrderEmbedding (e : Fin m ↪o Fin n) (a : Arc m) : Arc n where
  left := e a.left
  right := e a.right
  ordered := e.lt_iff_lt.mpr a.ordered

@[simp]
theorem mapOrderEmbedding_left (e : Fin m ↪o Fin n) (a : Arc m) :
    (a.mapOrderEmbedding e).left = e a.left := rfl

@[simp]
theorem mapOrderEmbedding_right (e : Fin m ↪o Fin n) (a : Arc m) :
    (a.mapOrderEmbedding e).right = e a.right := rfl

theorem mapOrderEmbedding_injective (e : Fin m ↪o Fin n) :
    Function.Injective (mapOrderEmbedding e) := by
  intro a b h
  apply Arc.ext
  · apply e.injective
    exact congrArg Arc.left h
  · apply e.injective
    exact congrArg Arc.right h

/-- Arc transport as a `Function.Embedding`, for use with `Finset.map`. -/
def mapOrderEmbeddingEmbedding (e : Fin m ↪o Fin n) : Arc m ↪ Arc n :=
  ⟨mapOrderEmbedding e, mapOrderEmbedding_injective e⟩

@[simp]
theorem mapOrderEmbeddingEmbedding_apply (e : Fin m ↪o Fin n) (a : Arc m) :
    mapOrderEmbeddingEmbedding e a = a.mapOrderEmbedding e := rfl

/-- Incidence at an embedded position is preserved and reflected. -/
@[simp]
theorem mapOrderEmbedding_incident_iff (e : Fin m ↪o Fin n)
    (a : Arc m) (p : Fin m) :
    (a.mapOrderEmbedding e).Incident (e p) ↔ a.Incident p := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective h)
  · intro h
    rcases h with rfl | rfl
    · exact (a.mapOrderEmbedding e).incident_left
    · exact (a.mapOrderEmbedding e).incident_right

/-- Every endpoint incident to a mapped arc comes from a unique source
position. -/
theorem mapOrderEmbedding_incident_iff_exists (e : Fin m ↪o Fin n)
    (a : Arc m) (q : Fin n) :
    (a.mapOrderEmbedding e).Incident q ↔
      ∃ p : Fin m, a.Incident p ∧ q = e p := by
  constructor
  · intro h
    rcases h with h | h
    · exact ⟨a.left, a.incident_left, h⟩
    · exact ⟨a.right, a.incident_right, h⟩
  · rintro ⟨p, hp, rfl⟩
    exact (mapOrderEmbedding_incident_iff e a p).2 hp

/-- Sharing an endpoint is preserved and reflected by an order embedding. -/
@[simp]
theorem mapOrderEmbedding_shareEndpoint_iff (e : Fin m ↪o Fin n)
    (a b : Arc m) :
    (a.mapOrderEmbedding e).ShareEndpoint (b.mapOrderEmbedding e) ↔
      a.ShareEndpoint b := by
  constructor
  · rintro ⟨q, hqa, hqb⟩
    obtain ⟨pa, hpa, hqpa⟩ :=
      (mapOrderEmbedding_incident_iff_exists e a q).1 hqa
    obtain ⟨pb, hpb, hqpb⟩ :=
      (mapOrderEmbedding_incident_iff_exists e b q).1 hqb
    have hp : pa = pb := e.injective (hqpa.symm.trans hqpb)
    subst pb
    exact ⟨pa, hpa, hpb⟩
  · rintro ⟨p, hpa, hpb⟩
    exact ⟨e p,
      (mapOrderEmbedding_incident_iff e a p).2 hpa,
      (mapOrderEmbedding_incident_iff e b p).2 hpb⟩

/-- Strict interleaving is preserved and reflected by an order embedding. -/
@[simp]
theorem mapOrderEmbedding_crosses_iff (e : Fin m ↪o Fin n)
    (a b : Arc m) :
    (a.mapOrderEmbedding e).Crosses (b.mapOrderEmbedding e) ↔ a.Crosses b := by
  simp only [Arc.Crosses, mapOrderEmbedding_left, mapOrderEmbedding_right,
    e.lt_iff_lt]

@[simp]
theorem mapOrderEmbedding_trans (e : Fin m ↪o Fin n) (f : Fin n ↪o Fin k)
    (a : Arc m) :
    (a.mapOrderEmbedding e).mapOrderEmbedding f =
      a.mapOrderEmbedding (e.trans f) := rfl

end Arc

namespace SecondaryStructure

/-- Push a secondary structure through an order embedding, retaining every
arc and leaving all positions outside the image unpaired. -/
def mapOrderEmbedding (e : Fin m ↪o Fin n)
    (S : SecondaryStructure m) : SecondaryStructure n where
  arcs := S.arcs.map (Arc.mapOrderEmbeddingEmbedding e)
  isPartialMatching := by
    intro a ha b hb hshare
    rcases Finset.mem_map.1 ha with ⟨a₀, ha₀, rfl⟩
    rcases Finset.mem_map.1 hb with ⟨b₀, hb₀, rfl⟩
    have hab : a₀ = b₀ := S.isPartialMatching ha₀ hb₀
      ((Arc.mapOrderEmbedding_shareEndpoint_iff e a₀ b₀).1 hshare)
    subst b₀
    rfl
  isNoncrossing := by
    intro a ha b hb hcross
    rcases Finset.mem_map.1 ha with ⟨a₀, ha₀, rfl⟩
    rcases Finset.mem_map.1 hb with ⟨b₀, hb₀, rfl⟩
    exact S.isNoncrossing ha₀ hb₀
      ((Arc.mapOrderEmbedding_crosses_iff e a₀ b₀).1 hcross)

/-- Exact membership description for mapped structures. -/
theorem mem_mapOrderEmbedding_iff (e : Fin m ↪o Fin n)
    (S : SecondaryStructure m) (a : Arc n) :
    a ∈ (S.mapOrderEmbedding e).arcs ↔
      ∃ b ∈ S.arcs, b.mapOrderEmbedding e = a := by
  simp [mapOrderEmbedding]

/-- A mapped source arc belongs to the mapped structure exactly when the
source arc belongs to the source structure. -/
@[simp]
theorem mapOrderEmbedding_mem_iff (e : Fin m ↪o Fin n)
    (S : SecondaryStructure m) (a : Arc m) :
    a.mapOrderEmbedding e ∈ (S.mapOrderEmbedding e).arcs ↔ a ∈ S.arcs := by
  change Arc.mapOrderEmbeddingEmbedding e a ∈
      S.arcs.map (Arc.mapOrderEmbeddingEmbedding e) ↔ a ∈ S.arcs
  exact Finset.mem_map' (Arc.mapOrderEmbeddingEmbedding e)

/-- Mapping every arc through an embedding preserves the pair count. -/
@[simp]
theorem pairCount_mapOrderEmbedding (e : Fin m ↪o Fin n)
    (S : SecondaryStructure m) :
    pairCount (S.mapOrderEmbedding e) = pairCount S := by
  simp [pairCount, mapOrderEmbedding]

/-- Compatibility of a mapped structure is exactly compatibility of the
source structure with the sequence restricted along the embedding. -/
theorem structureCompatible_mapOrderEmbedding_iff
    (e : Fin m ↪o Fin n) (S : SecondaryStructure m) (w : Sequence n) :
    StructureCompatible w (S.mapOrderEmbedding e) ↔
      StructureCompatible (fun i => w (e i)) S := by
  constructor
  · intro h a ha
    simpa using h (a.mapOrderEmbedding e)
      ((mapOrderEmbedding_mem_iff e S a).2 ha)
  · intro h a ha
    obtain ⟨b, hb, rfl⟩ := (mem_mapOrderEmbedding_iff e S a).1 ha
    simpa using h b hb

/-- Pull back the part of a structure whose two endpoints lie in the image of
an order embedding. -/
def pullbackOrderEmbedding (e : Fin m ↪o Fin n)
    (S : SecondaryStructure n) : SecondaryStructure m where
  arcs := Finset.univ.filter (fun a : Arc m => a.mapOrderEmbedding e ∈ S.arcs)
  isPartialMatching := by
    intro a ha b hb hshare
    have ha' : a.mapOrderEmbedding e ∈ S.arcs := (Finset.mem_filter.1 ha).2
    have hb' : b.mapOrderEmbedding e ∈ S.arcs := (Finset.mem_filter.1 hb).2
    apply Arc.mapOrderEmbedding_injective e
    exact S.isPartialMatching ha' hb'
      ((Arc.mapOrderEmbedding_shareEndpoint_iff e a b).2 hshare)
  isNoncrossing := by
    intro a ha b hb hcross
    have ha' : a.mapOrderEmbedding e ∈ S.arcs := (Finset.mem_filter.1 ha).2
    have hb' : b.mapOrderEmbedding e ∈ S.arcs := (Finset.mem_filter.1 hb).2
    exact S.isNoncrossing ha' hb'
      ((Arc.mapOrderEmbedding_crosses_iff e a b).2 hcross)

/-- Exact arc membership for a pullback. -/
@[simp]
theorem mem_pullbackOrderEmbedding_iff (e : Fin m ↪o Fin n)
    (S : SecondaryStructure n) (a : Arc m) :
    a ∈ (S.pullbackOrderEmbedding e).arcs ↔
      a.mapOrderEmbedding e ∈ S.arcs := by
  simp [pullbackOrderEmbedding]

/-- Compatibility restricts to every order-embedded sub-backbone. -/
theorem structureCompatible_pullbackOrderEmbedding
    (e : Fin m ↪o Fin n) (S : SecondaryStructure n) (w : Sequence n)
    (hS : StructureCompatible w S) :
    StructureCompatible (fun i => w (e i)) (S.pullbackOrderEmbedding e) := by
  intro a ha
  simpa using hS (a.mapOrderEmbedding e)
    ((mem_pullbackOrderEmbedding_iff e S a).1 ha)

/-- Pulling a mapped structure back along the same embedding recovers it
exactly. -/
@[simp]
theorem pullbackOrderEmbedding_mapOrderEmbedding
    (e : Fin m ↪o Fin n) (S : SecondaryStructure m) :
    (S.mapOrderEmbedding e).pullbackOrderEmbedding e = S := by
  apply SecondaryStructure.ext
  apply Finset.ext
  intro a
  rw [mem_pullbackOrderEmbedding_iff, mapOrderEmbedding_mem_iff]

/-- Mapping structures through a fixed order embedding is injective. -/
theorem mapOrderEmbedding_injective (e : Fin m ↪o Fin n) :
    Function.Injective (mapOrderEmbedding e) := by
  intro S T h
  have h' := congrArg (pullbackOrderEmbedding e) h
  simpa using h'

/-- Mapping a pullback back into the large backbone introduces no arcs that
were absent from the original structure. -/
theorem mapOrderEmbedding_pullback_arcs_subset
    (e : Fin m ↪o Fin n) (S : SecondaryStructure n) :
    ((S.pullbackOrderEmbedding e).mapOrderEmbedding e).arcs ⊆ S.arcs := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ :=
    (mem_mapOrderEmbedding_iff e (S.pullbackOrderEmbedding e) a).1 ha
  exact (mem_pullbackOrderEmbedding_iff e S b).1 hb

/-- Every arc of `S` is represented over the small backbone through `e`. -/
def ArcsInOrderEmbeddingRange (e : Fin m ↪o Fin n)
    (S : SecondaryStructure n) : Prop :=
  ∀ a ∈ S.arcs, ∃ b : Arc m, b.mapOrderEmbedding e = a

/-- If every original arc lies in the embedded range, pullback followed by
mapping is faithful. -/
theorem mapOrderEmbedding_pullbackOrderEmbedding_of_arcsInRange
    (e : Fin m ↪o Fin n) (S : SecondaryStructure n)
    (hRange : ArcsInOrderEmbeddingRange e S) :
    (S.pullbackOrderEmbedding e).mapOrderEmbedding e = S := by
  apply SecondaryStructure.ext
  ext a
  constructor
  · exact fun ha => mapOrderEmbedding_pullback_arcs_subset e S ha
  · intro ha
    obtain ⟨b, rfl⟩ := hRange a ha
    exact (mapOrderEmbedding_mem_iff e (S.pullbackOrderEmbedding e) b).2
      ((mem_pullbackOrderEmbedding_iff e S b).2 ha)

/-- Pullback cannot have more pairs than the original structure. -/
theorem pairCount_pullbackOrderEmbedding_le
    (e : Fin m ↪o Fin n) (S : SecondaryStructure n) :
    pairCount (S.pullbackOrderEmbedding e) ≤ pairCount S := by
  rw [← pairCount_mapOrderEmbedding e (S.pullbackOrderEmbedding e)]
  exact Finset.card_le_card (mapOrderEmbedding_pullback_arcs_subset e S)

/-- Under the no-lost-arcs hypothesis, pullback preserves pair count. -/
theorem pairCount_pullbackOrderEmbedding_of_arcsInRange
    (e : Fin m ↪o Fin n) (S : SecondaryStructure n)
    (hRange : ArcsInOrderEmbeddingRange e S) :
    pairCount (S.pullbackOrderEmbedding e) = pairCount S := by
  rw [← pairCount_mapOrderEmbedding e (S.pullbackOrderEmbedding e),
    mapOrderEmbedding_pullbackOrderEmbedding_of_arcsInRange e S hRange]

/-- Reindex a structure along an order isomorphism. -/
def reindexOrderIso (e : Fin m ≃o Fin n)
    (S : SecondaryStructure m) : SecondaryStructure n :=
  S.mapOrderEmbedding e.toOrderEmbedding

@[simp]
theorem pairCount_reindexOrderIso (e : Fin m ≃o Fin n)
    (S : SecondaryStructure m) :
    pairCount (S.reindexOrderIso e) = pairCount S := by
  exact pairCount_mapOrderEmbedding e.toOrderEmbedding S

theorem structureCompatible_reindexOrderIso_iff
    (e : Fin m ≃o Fin n) (S : SecondaryStructure m) (w : Sequence n) :
    StructureCompatible w (S.reindexOrderIso e) ↔
      StructureCompatible (fun i => w (e i)) S :=
  structureCompatible_mapOrderEmbedding_iff e.toOrderEmbedding S w

end SecondaryStructure

namespace Fin

/-- The canonical order embedding which retains `left` positions, skips two
adjacent positions, and then retains `right` positions. -/
def skipTwoOrderEmbedding (left right : Nat) :
    Fin (left + right) ↪o Fin (left + 2 + right) :=
  OrderEmbedding.ofStrictMono
    (fun i : Fin (left + right) =>
      if h : i.val < left then
        ⟨i.val, by omega⟩
      else
        ⟨i.val + 2, by omega⟩)
    (by
      intro i j hij
      simp only at hij ⊢
      split <;> split <;> simp only [Fin.mk_lt_mk] <;> omega)

@[simp]
theorem skipTwoOrderEmbedding_apply_of_lt
    (left right : Nat) (i : Fin (left + right)) (hi : i.val < left) :
    (skipTwoOrderEmbedding left right i).val = i.val := by
  simp [skipTwoOrderEmbedding, hi]

@[simp]
theorem skipTwoOrderEmbedding_apply_of_le
    (left right : Nat) (i : Fin (left + right)) (hi : left ≤ i.val) :
    (skipTwoOrderEmbedding left right i).val = i.val + 2 := by
  simp [skipTwoOrderEmbedding, Nat.not_lt.mpr hi]

/-- On the retained left block, `skipTwoOrderEmbedding` does not change the
numeric position. -/
@[simp]
theorem skipTwoOrderEmbedding_castAdd_val
    (left right : Nat) (i : Fin left) :
    (skipTwoOrderEmbedding left right (Fin.castAdd right i)).val = i.val := by
  apply skipTwoOrderEmbedding_apply_of_lt
  exact i.isLt

/-- On the retained right block, `skipTwoOrderEmbedding` adds two to the
numeric position. -/
@[simp]
theorem skipTwoOrderEmbedding_natAdd_val
    (left right : Nat) (i : Fin right) :
    (skipTwoOrderEmbedding left right (Fin.natAdd left i)).val =
      left + i.val + 2 := by
  rw [skipTwoOrderEmbedding_apply_of_le]
  · rfl
  · simp

/-- Exact range of the adjacent skip-two embedding. -/
theorem mem_range_skipTwoOrderEmbedding_iff
    (left right : Nat) (j : Fin (left + 2 + right)) :
    j ∈ Set.range (skipTwoOrderEmbedding left right) ↔
      j.val < left ∨ left + 2 ≤ j.val := by
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i.val < left
    · exact Or.inl (by simp [skipTwoOrderEmbedding, hi])
    · exact Or.inr (by
        rw [skipTwoOrderEmbedding_apply_of_le left right i (Nat.le_of_not_gt hi)]
        omega)
  · intro hj
    rcases hj with hj | hj
    · let i : Fin (left + right) := ⟨j.val, by omega⟩
      refine ⟨i, Fin.ext ?_⟩
      simp [i, skipTwoOrderEmbedding, hj]
    · let i : Fin (left + right) := ⟨j.val - 2, by omega⟩
      have hi : left ≤ i.val := by simp [i]; omega
      refine ⟨i, Fin.ext ?_⟩
      rw [skipTwoOrderEmbedding_apply_of_le left right i hi]
      simp [i]
      omega

end Fin

end RNA
