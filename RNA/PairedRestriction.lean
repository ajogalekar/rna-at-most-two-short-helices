module

public import RNA.TiedCompetitor
public import RNA.Saturable

@[expose] public section

set_option autoImplicit false

/-!
# Order-preserving restriction to target-paired positions

The retained backbone is the finite ordered set of positions paired by a fixed
target.  `Finset.orderIsoOfFin` compresses it to a consecutive `Fin` backbone.
Structures whose paired positions are retained are transported without
discarding any arc.
-/

namespace RNA

variable {n : Nat}

/-- Positions retained when deleting all positions unpaired by `T`. -/
def targetPairedPositionSet (T : SecondaryStructure n) : Finset (Fin n) :=
  Finset.univ.filter T.positionPaired

@[simp]
theorem mem_targetPairedPositionSet {T : SecondaryStructure n} {i : Fin n} :
    i ∈ targetPairedPositionSet T ↔ T.positionPaired i := by
  simp [targetPairedPositionSet]

/-- A retained original position, with its target-pairedness proof. -/
abbrev RetainedPosition (T : SecondaryStructure n) :=
  ↑(targetPairedPositionSet T)

/-- The size of the target-paired skeleton. -/
def pairedSkeletonLength (T : SecondaryStructure n) : Nat :=
  (targetPairedPositionSet T).card

/-- Increasing expansion from compressed positions to original retained
positions. -/
noncomputable def pairedPositionExpansion (T : SecondaryStructure n) :
    Fin (pairedSkeletonLength T) ≃o RetainedPosition T :=
  (targetPairedPositionSet T).orderIsoOfFin rfl

/-- Increasing compression (rank among retained positions). -/
noncomputable def pairedPositionCompression (T : SecondaryStructure n) :
    RetainedPosition T ≃o Fin (pairedSkeletonLength T) :=
  (pairedPositionExpansion T).symm

@[simp]
theorem pairedPositionExpansion_compression
    (T : SecondaryStructure n) (i : RetainedPosition T) :
    pairedPositionExpansion T (pairedPositionCompression T i) = i :=
  (pairedPositionExpansion T).apply_symm_apply i

@[simp]
theorem pairedPositionCompression_expansion
    (T : SecondaryStructure n) (i : Fin (pairedSkeletonLength T)) :
    pairedPositionCompression T (pairedPositionExpansion T i) = i :=
  (pairedPositionExpansion T).symm_apply_apply i

/-- The complete sequence on the compressed paired skeleton. -/
noncomputable def pairedRestrictedSequence (T : SecondaryStructure n)
    (w : Sequence n) : Sequence (pairedSkeletonLength T) :=
  fun i ↦ w (pairedPositionExpansion T i).val

/-- Every paired position of `S` is retained by target `T`. -/
def PairedPositionsRetained (T S : SecondaryStructure n) : Prop :=
  ∀ i : Fin n, S.positionPaired i → T.positionPaired i

theorem pairedPositionsRetained_refl (T : SecondaryStructure n) :
    PairedPositionsRetained T T := by
  intro i hi
  exact hi

theorem pairedPositionsRetained_of_unpairedPositionSet_eq
    {T S : SecondaryStructure n}
    (hUnpaired : unpairedPositionSet S = unpairedPositionSet T) :
    PairedPositionsRetained T S := by
  intro i hiS
  by_contra hiT
  have hi : i ∈ unpairedPositionSet T := by
    simpa using hiT
  rw [← hUnpaired] at hi
  exact (mem_unpairedPositionSet.mp hi) hiS

theorem targetPaired_of_unpairedPositionSet_eq
    {T S : SecondaryStructure n}
    (hUnpaired : unpairedPositionSet S = unpairedPositionSet T) :
    ∀ i : Fin n, T.positionPaired i → S.positionPaired i := by
  intro i hiT
  by_contra hiS
  have hi : i ∈ unpairedPositionSet S := by
    simpa using hiS
  rw [hUnpaired] at hi
  exact (mem_unpairedPositionSet.mp hi) hiT

theorem pairedNode_left_positionPaired {S : SecondaryStructure n}
    (a : PairedNode S) : S.positionPaired a.val.left :=
  ⟨a.val, a.property, a.val.incident_left⟩

theorem pairedNode_right_positionPaired {S : SecondaryStructure n}
    (a : PairedNode S) : S.positionPaired a.val.right :=
  ⟨a.val, a.property, a.val.incident_right⟩

/-- Compress an original arc whose two endpoints are retained by `T`. -/
noncomputable def compressRetainedArc
    (T : SecondaryStructure n) (a : Arc n)
    (hleft : T.positionPaired a.left) (hright : T.positionPaired a.right) :
    Arc (pairedSkeletonLength T) where
  left := pairedPositionCompression T
    ⟨a.left, mem_targetPairedPositionSet.mpr hleft⟩
  right := pairedPositionCompression T
    ⟨a.right, mem_targetPairedPositionSet.mpr hright⟩
  ordered := (pairedPositionCompression T).lt_iff_lt.mpr a.ordered

/-- Compress an actual arc of `S` after proving that all its endpoints are
retained by `T`. -/
noncomputable def compressPairedArc
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (a : PairedNode S) : Arc (pairedSkeletonLength T) :=
  compressRetainedArc T a.val
    (hRetained a.val.left (pairedNode_left_positionPaired a))
    (hRetained a.val.right (pairedNode_right_positionPaired a))

/-- Lift a compressed arc back to the original retained positions. -/
noncomputable def liftPairedArc (T : SecondaryStructure n)
    (a : Arc (pairedSkeletonLength T)) : Arc n where
  left := (pairedPositionExpansion T a.left).val
  right := (pairedPositionExpansion T a.right).val
  ordered := (pairedPositionExpansion T).lt_iff_lt.mpr a.ordered

@[simp]
theorem liftPairedArc_compressPairedArc
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (a : PairedNode S) :
    liftPairedArc T (compressPairedArc T S hRetained a) = a.val := by
  apply Arc.ext
  · exact congrArg Subtype.val
      (pairedPositionExpansion_compression T _)
  · exact congrArg Subtype.val
      (pairedPositionExpansion_compression T _)

@[simp]
theorem compressRetainedArc_liftPairedArc
    (T : SecondaryStructure n) (a : Arc (pairedSkeletonLength T)) :
    compressRetainedArc T (liftPairedArc T a)
      (mem_targetPairedPositionSet.mp (pairedPositionExpansion T a.left).property)
      (mem_targetPairedPositionSet.mp (pairedPositionExpansion T a.right).property) = a := by
  apply Arc.ext
  · exact pairedPositionCompression_expansion T a.left
  · exact pairedPositionCompression_expansion T a.right

/-- Compression is injective on the actual arcs of a retained structure. -/
noncomputable def compressPairedArcEmbedding
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S) :
    PairedNode S ↪ Arc (pairedSkeletonLength T) where
  toFun := compressPairedArc T S hRetained
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply Arc.ext
    · have hleft := congrArg Arc.left hab
      change pairedPositionCompression T
          ⟨a.val.left, mem_targetPairedPositionSet.mpr
            (hRetained a.val.left (pairedNode_left_positionPaired a))⟩ =
        pairedPositionCompression T
          ⟨b.val.left, mem_targetPairedPositionSet.mpr
            (hRetained b.val.left (pairedNode_left_positionPaired b))⟩ at hleft
      have hretained := (pairedPositionCompression T).injective hleft
      exact congrArg Subtype.val hretained
    · have hright := congrArg Arc.right hab
      change pairedPositionCompression T
          ⟨a.val.right, mem_targetPairedPositionSet.mpr
            (hRetained a.val.right (pairedNode_right_positionPaired a))⟩ =
        pairedPositionCompression T
          ⟨b.val.right, mem_targetPairedPositionSet.mpr
            (hRetained b.val.right (pairedNode_right_positionPaired b))⟩ at hright
      have hretained := (pairedPositionCompression T).injective hright
      exact congrArg Subtype.val hretained

/-- Exact image of all arcs of `S` on the compressed backbone. -/
noncomputable def compressedArcSet
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S) :
    Finset (Arc (pairedSkeletonLength T)) :=
  Finset.univ.map (compressPairedArcEmbedding T S hRetained)

@[simp]
theorem compressPairedArc_mem_compressedArcSet
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (a : PairedNode S) :
    compressPairedArc T S hRetained a ∈
      compressedArcSet T S hRetained := by
  simp [compressedArcSet, compressPairedArcEmbedding]

theorem mem_compressedArcSet_iff_exists
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (b : Arc (pairedSkeletonLength T)) :
    b ∈ compressedArcSet T S hRetained ↔
      ∃ a : PairedNode S, compressPairedArc T S hRetained a = b := by
  simp [compressedArcSet, compressPairedArcEmbedding, eq_comm]

/-- Arc membership is exactly reflected by lifting through the order
equivalence. -/
theorem liftPairedArc_mem_iff_mem_compressedArcSet
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (b : Arc (pairedSkeletonLength T)) :
    liftPairedArc T b ∈ S.arcs ↔ b ∈ compressedArcSet T S hRetained := by
  constructor
  · intro hb
    let a : PairedNode S := ⟨liftPairedArc T b, hb⟩
    have hcompress : compressPairedArc T S hRetained a = b := by
      simpa [a, compressPairedArc] using
        compressRetainedArc_liftPairedArc T b
    rw [← hcompress]
    exact compressPairedArc_mem_compressedArcSet T S hRetained a
  · intro hb
    obtain ⟨a, rfl⟩ :=
      (mem_compressedArcSet_iff_exists T S hRetained b).mp hb
    simpa using a.property

theorem liftPairedArc_injective (T : SecondaryStructure n) :
    Function.Injective (liftPairedArc T) := by
  intro a b hab
  apply Arc.ext
  · have hleft := congrArg Arc.left hab
    change (pairedPositionExpansion T a.left).val =
      (pairedPositionExpansion T b.left).val at hleft
    apply (pairedPositionExpansion T).injective
    exact Subtype.ext hleft
  · have hright := congrArg Arc.right hab
    change (pairedPositionExpansion T a.right).val =
      (pairedPositionExpansion T b.right).val at hright
    apply (pairedPositionExpansion T).injective
    exact Subtype.ext hright

theorem liftPairedArc_shareEndpoint
    (T : SecondaryStructure n) {a b : Arc (pairedSkeletonLength T)}
    (hshare : a.ShareEndpoint b) :
    (liftPairedArc T a).ShareEndpoint (liftPairedArc T b) := by
  obtain ⟨p, hap, hbp⟩ := hshare
  refine ⟨(pairedPositionExpansion T p).val, ?_, ?_⟩
  · rcases hap with hp | hp
    · left
      exact congrArg (fun q : Fin (pairedSkeletonLength T) ↦
        (pairedPositionExpansion T q).val) hp
    · right
      exact congrArg (fun q : Fin (pairedSkeletonLength T) ↦
        (pairedPositionExpansion T q).val) hp
  · rcases hbp with hp | hp
    · left
      exact congrArg (fun q : Fin (pairedSkeletonLength T) ↦
        (pairedPositionExpansion T q).val) hp
    · right
      exact congrArg (fun q : Fin (pairedSkeletonLength T) ↦
        (pairedPositionExpansion T q).val) hp

theorem liftPairedArc_crosses_iff
    (T : SecondaryStructure n) (a b : Arc (pairedSkeletonLength T)) :
    (liftPairedArc T a).Crosses (liftPairedArc T b) ↔ a.Crosses b := by
  simp only [Arc.Crosses]
  change
    (((pairedPositionExpansion T a.left) <
          pairedPositionExpansion T b.left ∧
        pairedPositionExpansion T b.left <
          pairedPositionExpansion T a.right ∧
        pairedPositionExpansion T a.right <
          pairedPositionExpansion T b.right) ∨
      ((pairedPositionExpansion T b.left) <
          pairedPositionExpansion T a.left ∧
        pairedPositionExpansion T a.left <
          pairedPositionExpansion T b.right ∧
        pairedPositionExpansion T b.right <
          pairedPositionExpansion T a.right)) ↔ _
  simp only [(pairedPositionExpansion T).lt_iff_lt]

theorem compressedArcSet_isPartialMatching
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S) :
    IsPartialMatching (compressedArcSet T S hRetained) := by
  intro a ha b hb hshare
  apply liftPairedArc_injective T
  apply S.eq_of_mem_of_shareEndpoint
  · exact (liftPairedArc_mem_iff_mem_compressedArcSet
      T S hRetained a).mpr ha
  · exact (liftPairedArc_mem_iff_mem_compressedArcSet
      T S hRetained b).mpr hb
  · exact liftPairedArc_shareEndpoint T hshare

theorem compressedArcSet_isNoncrossing
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S) :
    IsNoncrossing (compressedArcSet T S hRetained) := by
  intro a ha b hb hcross
  apply S.not_crossing
    ((liftPairedArc_mem_iff_mem_compressedArcSet
      T S hRetained a).mpr ha)
    ((liftPairedArc_mem_iff_mem_compressedArcSet
      T S hRetained b).mpr hb)
  exact (liftPairedArc_crosses_iff T a b).mpr hcross

/-- A structure transported to the target-paired compressed backbone.  The
retention hypothesis ensures that no arc is filtered out. -/
noncomputable def pairedRestriction
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S) :
    SecondaryStructure (pairedSkeletonLength T) where
  arcs := compressedArcSet T S hRetained
  isPartialMatching := compressedArcSet_isPartialMatching T S hRetained
  isNoncrossing := compressedArcSet_isNoncrossing T S hRetained

@[simp]
theorem pairedRestriction_arcs
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S) :
    (pairedRestriction T S hRetained).arcs =
      compressedArcSet T S hRetained := rfl

theorem mem_pairedRestriction_iff_liftPairedArc_mem
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (b : Arc (pairedSkeletonLength T)) :
    b ∈ (pairedRestriction T S hRetained).arcs ↔
      liftPairedArc T b ∈ S.arcs := by
  exact (liftPairedArc_mem_iff_mem_compressedArcSet
    T S hRetained b).symm

@[simp]
theorem pairedRestrictedSequence_liftPairedArc_left
    (T : SecondaryStructure n) (w : Sequence n)
    (a : Arc (pairedSkeletonLength T)) :
    pairedRestrictedSequence T w a.left = w (liftPairedArc T a).left := rfl

@[simp]
theorem pairedRestrictedSequence_liftPairedArc_right
    (T : SecondaryStructure n) (w : Sequence n)
    (a : Arc (pairedSkeletonLength T)) :
    pairedRestrictedSequence T w a.right = w (liftPairedArc T a).right := rfl

@[simp]
theorem pairedRestrictedSequence_compressPairedArc_left
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (w : Sequence n) (a : PairedNode S) :
    pairedRestrictedSequence T w
        (compressPairedArc T S hRetained a).left = w a.val.left := by
  change w (pairedPositionExpansion T
    (pairedPositionCompression T
      ⟨a.val.left, mem_targetPairedPositionSet.mpr
        (hRetained a.val.left (pairedNode_left_positionPaired a))⟩)).val = _
  rw [pairedPositionExpansion_compression]

@[simp]
theorem pairedRestrictedSequence_compressPairedArc_right
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (w : Sequence n) (a : PairedNode S) :
    pairedRestrictedSequence T w
        (compressPairedArc T S hRetained a).right = w a.val.right := by
  change w (pairedPositionExpansion T
    (pairedPositionCompression T
      ⟨a.val.right, mem_targetPairedPositionSet.mpr
        (hRetained a.val.right (pairedNode_right_positionPaired a))⟩)).val = _
  rw [pairedPositionExpansion_compression]

/-- Compatibility is preserved by paired-skeleton compression. -/
theorem structureCompatible_pairedRestriction
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (w : Sequence n) (hCompatible : StructureCompatible w S) :
    StructureCompatible (pairedRestrictedSequence T w)
      (pairedRestriction T S hRetained) := by
  intro a ha
  have hLift : liftPairedArc T a ∈ S.arcs :=
    (mem_pairedRestriction_iff_liftPairedArc_mem
      T S hRetained a).mp ha
  simpa using hCompatible (liftPairedArc T a) hLift

/-- No arc is lost under compression, so pair count is preserved exactly. -/
theorem pairCount_pairedRestriction
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S) :
    pairCount (pairedRestriction T S hRetained) = pairCount S := by
  simp [pairCount, pairedRestriction, compressedArcSet,
    compressPairedArcEmbedding, PairedNode]

/-- A compressed position is paired exactly when its expanded original
position is paired by `S`. -/
theorem pairedRestriction_positionPaired_iff
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (i : Fin (pairedSkeletonLength T)) :
    (pairedRestriction T S hRetained).positionPaired i ↔
      S.positionPaired (pairedPositionExpansion T i).val := by
  constructor
  · rintro ⟨a, ha, hi⟩
    refine ⟨liftPairedArc T a,
      (mem_pairedRestriction_iff_liftPairedArc_mem
        T S hRetained a).mp ha, ?_⟩
    rcases hi with hi | hi
    · left
      exact congrArg (fun q : Fin (pairedSkeletonLength T) ↦
        (pairedPositionExpansion T q).val) hi
    · right
      exact congrArg (fun q : Fin (pairedSkeletonLength T) ↦
        (pairedPositionExpansion T q).val) hi
  · rintro ⟨a, ha, hi⟩
    let q : PairedNode S := ⟨a, ha⟩
    refine ⟨compressPairedArc T S hRetained q,
      compressPairedArc_mem_compressedArcSet T S hRetained q, ?_⟩
    rcases hi with hi | hi
    · left
      have hretained : pairedPositionExpansion T i =
          (⟨a.left, mem_targetPairedPositionSet.mpr
            (hRetained a.left (pairedNode_left_positionPaired q))⟩ :
              RetainedPosition T) := Subtype.ext hi
      have hcompressed := congrArg (pairedPositionCompression T) hretained
      simpa [q, compressPairedArc, compressRetainedArc] using hcompressed
    · right
      have hretained : pairedPositionExpansion T i =
          (⟨a.right, mem_targetPairedPositionSet.mpr
            (hRetained a.right (pairedNode_right_positionPaired q))⟩ :
              RetainedPosition T) := Subtype.ext hi
      have hcompressed := congrArg (pairedPositionCompression T) hretained
      simpa [q, compressPairedArc, compressRetainedArc] using hcompressed

/-- If every target-retained position is paired by `S`, its compressed
restriction is saturated. -/
theorem saturatedStructure_pairedRestriction
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (hCovers : ∀ i : Fin n, T.positionPaired i → S.positionPaired i) :
    SaturatedStructure (pairedRestriction T S hRetained) := by
  intro i
  apply (pairedRestriction_positionPaired_iff T S hRetained i).mpr
  apply hCovers (pairedPositionExpansion T i).val
  exact mem_targetPairedPositionSet.mp (pairedPositionExpansion T i).property

/-- The target itself restricted to its paired skeleton. -/
noncomputable def targetPairedRestriction (T : SecondaryStructure n) :
    SecondaryStructure (pairedSkeletonLength T) :=
  pairedRestriction T T (pairedPositionsRetained_refl T)

/-- A competitor restricted along a proved common unpaired-position set. -/
noncomputable def competitorPairedRestriction
    (T S : SecondaryStructure n)
    (hUnpaired : unpairedPositionSet S = unpairedPositionSet T) :
    SecondaryStructure (pairedSkeletonLength T) :=
  pairedRestriction T S
    (pairedPositionsRetained_of_unpairedPositionSet_eq hUnpaired)

/-- The compressed target pairs every retained position. -/
theorem saturatedStructure_targetPairedRestriction
    (T : SecondaryStructure n) :
    SaturatedStructure (targetPairedRestriction T) := by
  exact saturatedStructure_pairedRestriction T T
    (pairedPositionsRetained_refl T) (fun _ hi ↦ hi)

/-- A competitor with the same unpaired set as the target is saturated after
the common unpaired positions are deleted. -/
theorem saturatedStructure_competitorPairedRestriction
    (T S : SecondaryStructure n)
    (hUnpaired : unpairedPositionSet S = unpairedPositionSet T) :
    SaturatedStructure (competitorPairedRestriction T S hUnpaired) := by
  exact saturatedStructure_pairedRestriction T S
    (pairedPositionsRetained_of_unpairedPositionSet_eq hUnpaired)
    (targetPaired_of_unpairedPositionSet_eq hUnpaired)

theorem mem_targetPairedRestriction_iff_liftPairedArc_mem
    (T : SecondaryStructure n) (a : Arc (pairedSkeletonLength T)) :
    a ∈ (targetPairedRestriction T).arcs ↔ liftPairedArc T a ∈ T.arcs := by
  exact mem_pairedRestriction_iff_liftPairedArc_mem T T
    (pairedPositionsRetained_refl T) a

theorem mem_competitorPairedRestriction_iff_liftPairedArc_mem
    (T S : SecondaryStructure n)
    (hUnpaired : unpairedPositionSet S = unpairedPositionSet T)
    (a : Arc (pairedSkeletonLength T)) :
    a ∈ (competitorPairedRestriction T S hUnpaired).arcs ↔
      liftPairedArc T a ∈ S.arcs := by
  exact mem_pairedRestriction_iff_liftPairedArc_mem T S
    (pairedPositionsRetained_of_unpairedPositionSet_eq hUnpaired) a

theorem structureCompatible_targetPairedRestriction
    (T : SecondaryStructure n) (w : Sequence n)
    (hCompatible : StructureCompatible w T) :
    StructureCompatible (pairedRestrictedSequence T w)
      (targetPairedRestriction T) := by
  exact structureCompatible_pairedRestriction T T
    (pairedPositionsRetained_refl T) w hCompatible

theorem structureCompatible_competitorPairedRestriction
    (T S : SecondaryStructure n)
    (hUnpaired : unpairedPositionSet S = unpairedPositionSet T)
    (w : Sequence n) (hCompatible : StructureCompatible w S) :
    StructureCompatible (pairedRestrictedSequence T w)
      (competitorPairedRestriction T S hUnpaired) := by
  exact structureCompatible_pairedRestriction T S
    (pairedPositionsRetained_of_unpairedPositionSet_eq hUnpaired)
    w hCompatible

@[simp]
theorem pairCount_targetPairedRestriction (T : SecondaryStructure n) :
    pairCount (targetPairedRestriction T) = pairCount T := by
  exact pairCount_pairedRestriction T T (pairedPositionsRetained_refl T)

@[simp]
theorem pairCount_competitorPairedRestriction
    (T S : SecondaryStructure n)
    (hUnpaired : unpairedPositionSet S = unpairedPositionSet T) :
    pairCount (competitorPairedRestriction T S hUnpaired) = pairCount S := by
  exact pairCount_pairedRestriction T S
    (pairedPositionsRetained_of_unpairedPositionSet_eq hUnpaired)

/-- Original and compressed arcs are in exact bijection. -/
noncomputable def pairedNodeRestrictionEquiv
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S) :
    PairedNode S ≃ PairedNode (pairedRestriction T S hRetained) where
  toFun a :=
    ⟨compressPairedArc T S hRetained a,
      compressPairedArc_mem_compressedArcSet T S hRetained a⟩
  invFun b :=
    ⟨liftPairedArc T b.val,
      (mem_pairedRestriction_iff_liftPairedArc_mem
        T S hRetained b.val).mp b.property⟩
  left_inv a := by
    apply Subtype.ext
    exact liftPairedArc_compressPairedArc T S hRetained a
  right_inv b := by
    apply Subtype.ext
    simpa [compressPairedArc] using
      compressRetainedArc_liftPairedArc T b.val

@[simp]
theorem pairedNodeRestrictionEquiv_apply_val
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (a : PairedNode S) :
    (pairedNodeRestrictionEquiv T S hRetained a).val =
      compressPairedArc T S hRetained a := rfl

@[simp]
theorem pairedNodeRestrictionEquiv_symm_apply_val
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (a : PairedNode (pairedRestriction T S hRetained)) :
    ((pairedNodeRestrictionEquiv T S hRetained).symm a).val =
      liftPairedArc T a.val := rfl

/-- Compression preserves and reflects the backbone order of paired left
endpoints. -/
theorem compressPairedArc_left_lt_left_iff
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (a b : PairedNode S) :
    (compressPairedArc T S hRetained a).left <
        (compressPairedArc T S hRetained b).left ↔
      a.val.left < b.val.left := by
  change pairedPositionCompression T
      ⟨a.val.left, mem_targetPairedPositionSet.mpr
        (hRetained a.val.left (pairedNode_left_positionPaired a))⟩ <
    pairedPositionCompression T
      ⟨b.val.left, mem_targetPairedPositionSet.mpr
        (hRetained b.val.left (pairedNode_left_positionPaired b))⟩ ↔ _
  exact (pairedPositionCompression T).lt_iff_lt

/-- Compression preserves and reflects the backbone order of paired right
endpoints. -/
theorem compressPairedArc_right_lt_right_iff
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (a b : PairedNode S) :
    (compressPairedArc T S hRetained a).right <
        (compressPairedArc T S hRetained b).right ↔
      a.val.right < b.val.right := by
  change pairedPositionCompression T
      ⟨a.val.right, mem_targetPairedPositionSet.mpr
        (hRetained a.val.right (pairedNode_right_positionPaired a))⟩ <
    pairedPositionCompression T
      ⟨b.val.right, mem_targetPairedPositionSet.mpr
        (hRetained b.val.right (pairedNode_right_positionPaired b))⟩ ↔ _
  exact (pairedPositionCompression T).lt_iff_lt

/-- Paired strict ancestry is unchanged by paired-skeleton compression. -/
theorem strictlyContains_pairedRestriction_iff
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (a b : PairedNode S) :
    PairedNode.StrictlyContains (pairedRestriction T S hRetained)
        (pairedNodeRestrictionEquiv T S hRetained a)
        (Sum.inl (pairedNodeRestrictionEquiv T S hRetained b)) ↔
      PairedNode.StrictlyContains S a (Sum.inl b) := by
  simp only [PairedNode.StrictlyContains]
  exact and_congr
    (compressPairedArc_left_lt_left_iff T S hRetained a b)
    (compressPairedArc_right_lt_right_iff T S hRetained b a)

/-- In particular, sibling order by first backbone position is preserved and
reflected. -/
theorem pairedChildBackboneOrder_pairedRestriction_iff
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (a b : PairedNode S) :
    (pairedNodeRestrictionEquiv T S hRetained a).val.left <
        (pairedNodeRestrictionEquiv T S hRetained b).val.left ↔
      a.val.left < b.val.left :=
  compressPairedArc_left_lt_left_iff T S hRetained a b

/-- Transport a paired interface, leaving the virtual root fixed. -/
noncomputable def pairedOrRootRestrictionMap
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S) :
    PairedOrRootNode S →
      PairedOrRootNode (pairedRestriction T S hRetained) :=
  Option.map (pairedNodeRestrictionEquiv T S hRetained)

/-- The independent smallest-enclosing-pair parent specification is preserved
and reflected. -/
theorem isParent_pairedRestriction_iff
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (p : PairedOrRootNode S) (c : PairedNode S) :
    IsParent (pairedRestriction T S hRetained)
        (pairedOrRootRestrictionMap T S hRetained p)
        (Sum.inl (pairedNodeRestrictionEquiv T S hRetained c)) ↔
      IsParent S p (Sum.inl c) := by
  let e := pairedNodeRestrictionEquiv T S hRetained
  cases p with
  | none =>
      change
        (∀ q : PairedNode (pairedRestriction T S hRetained),
          ¬ PairedNode.StrictlyContains (pairedRestriction T S hRetained)
            q (Sum.inl (e c))) ↔
        (∀ q : PairedNode S,
          ¬ PairedNode.StrictlyContains S q (Sum.inl c))
      constructor
      · intro h q hq
        exact h (e q)
          ((strictlyContains_pairedRestriction_iff
            T S hRetained q c).mpr hq)
      · intro h q hq
        obtain ⟨q, rfl⟩ := e.surjective q
        exact h q
          ((strictlyContains_pairedRestriction_iff
            T S hRetained q c).mp hq)
  | some a =>
      change
        (PairedNode.StrictlyContains (pairedRestriction T S hRetained)
            (e a) (Sum.inl (e c)) ∧
          ∀ q : PairedNode (pairedRestriction T S hRetained),
            PairedNode.StrictlyContains (pairedRestriction T S hRetained)
                q (Sum.inl (e c)) →
              q = e a ∨
                PairedNode.StrictlyContains
                  (pairedRestriction T S hRetained) q (Sum.inl (e a))) ↔
        (PairedNode.StrictlyContains S a (Sum.inl c) ∧
          ∀ q : PairedNode S,
            PairedNode.StrictlyContains S q (Sum.inl c) →
              q = a ∨ PairedNode.StrictlyContains S q (Sum.inl a))
      constructor
      · rintro ⟨hac, hall⟩
        refine ⟨(strictlyContains_pairedRestriction_iff
          T S hRetained a c).mp hac, ?_⟩
        intro q hqc
        rcases hall (e q)
            ((strictlyContains_pairedRestriction_iff
              T S hRetained q c).mpr hqc) with hqa | hqa
        · exact Or.inl (e.injective hqa)
        · exact Or.inr ((strictlyContains_pairedRestriction_iff
            T S hRetained q a).mp hqa)
      · rintro ⟨hac, hall⟩
        refine ⟨(strictlyContains_pairedRestriction_iff
          T S hRetained a c).mpr hac, ?_⟩
        intro q hqc
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases hall q ((strictlyContains_pairedRestriction_iff
          T S hRetained q c).mp hqc) with hqa | hqa
        · exact Or.inl (congrArg e hqa)
        · exact Or.inr ((strictlyContains_pairedRestriction_iff
            T S hRetained q a).mpr hqa)

/-- The executable paired-parent map commutes with compression. -/
theorem parent_pairedRestriction
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (c : PairedNode S) :
    parent (pairedRestriction T S hRetained)
        (Sum.inl (pairedNodeRestrictionEquiv T S hRetained c)) =
      pairedOrRootRestrictionMap T S hRetained
        (parent S (Sum.inl c)) := by
  apply (parent_eq_iff_isParent
    (pairedRestriction T S hRetained)
    (Sum.inl (pairedNodeRestrictionEquiv T S hRetained c))
    (pairedOrRootRestrictionMap T S hRetained
      (parent S (Sum.inl c)))).mpr
  exact (isParent_pairedRestriction_iff T S hRetained
    (parent S (Sum.inl c)) c).mpr (parent_isParent S (Sum.inl c))

/-- Paired-child membership at every root or paired interface is preserved and
reflected. -/
theorem mem_pairedChildren_pairedRestriction_iff
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (p : PairedOrRootNode S) (c : PairedNode S) :
    pairedNodeRestrictionEquiv T S hRetained c ∈
        pairedChildren (pairedRestriction T S hRetained)
          (pairedOrRootRestrictionMap T S hRetained p) ↔
      c ∈ pairedChildren S p := by
  simp only [pairedChildren, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [parent_pairedRestriction]
  let e := pairedNodeRestrictionEquiv T S hRetained
  exact (Function.Embedding.optionMap e.toEmbedding).injective.eq_iff

/-- Root-child membership is unchanged by compression. -/
theorem mem_root_pairedChildren_pairedRestriction_iff
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (c : PairedNode S) :
    pairedNodeRestrictionEquiv T S hRetained c ∈
        pairedChildren (pairedRestriction T S hRetained) none ↔
      c ∈ pairedChildren S none := by
  simpa [pairedOrRootRestrictionMap] using
    mem_pairedChildren_pairedRestriction_iff T S hRetained none c

/-- Nonroot paired-child membership is unchanged by compression. -/
theorem mem_nonroot_pairedChildren_pairedRestriction_iff
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (p c : PairedNode S) :
    pairedNodeRestrictionEquiv T S hRetained c ∈
        pairedChildren (pairedRestriction T S hRetained)
          (some (pairedNodeRestrictionEquiv T S hRetained p)) ↔
      c ∈ pairedChildren S (some p) := by
  simpa [pairedOrRootRestrictionMap] using
    mem_pairedChildren_pairedRestriction_iff T S hRetained (some p) c

/-- Local child-letter distinctness transfers to the compressed paired
skeleton. -/
theorem locallyDistinct_pairedRestriction
    (T S : SecondaryStructure n) (hRetained : PairedPositionsRetained T S)
    (w : Sequence n) (hLocal : LocallyDistinct S w) :
    LocallyDistinct (pairedRestriction T S hRetained)
      (pairedRestrictedSequence T w) := by
  let e := pairedNodeRestrictionEquiv T S hRetained
  constructor
  · intro v q hv hq hletters
    obtain ⟨v, rfl⟩ := e.surjective v
    obtain ⟨q, rfl⟩ := e.surjective q
    have hv' : v ∈ pairedChildren S none :=
      (mem_root_pairedChildren_pairedRestriction_iff
        T S hRetained v).mp hv
    have hq' : q ∈ pairedChildren S none :=
      (mem_root_pairedChildren_pairedRestriction_iff
        T S hRetained q).mp hq
    have hletters' : w v.val.left = w q.val.left := by
      simpa [e] using hletters
    exact congrArg e (hLocal.1 hv' hq' hletters')
  · intro p
    obtain ⟨p, rfl⟩ := e.surjective p
    constructor
    · intro v q hv hq hletters
      obtain ⟨v, rfl⟩ := e.surjective v
      obtain ⟨q, rfl⟩ := e.surjective q
      have hv' : v ∈ pairedChildren S (some p) :=
        (mem_nonroot_pairedChildren_pairedRestriction_iff
          T S hRetained p v).mp hv
      have hq' : q ∈ pairedChildren S (some p) :=
        (mem_nonroot_pairedChildren_pairedRestriction_iff
          T S hRetained p q).mp hq
      have hletters' : w v.val.left = w q.val.left := by
        simpa [e] using hletters
      exact congrArg e (hLocal.2 p |>.1 hv' hq' hletters')
    · intro v hv
      obtain ⟨v, rfl⟩ := e.surjective v
      have hv' : v ∈ pairedChildren S (some p) :=
        (mem_nonroot_pairedChildren_pairedRestriction_iff
          T S hRetained p v).mp hv
      simpa [e] using hLocal.2 p |>.2 v hv'

/-- Milestone-4 local distinctness transfers to the saturated target
restriction used by the no-tie proof. -/
theorem locallyDistinct_targetPairedRestriction
    (T : SecondaryStructure n) (w : Sequence n)
    (hLocal : LocallyDistinct T w) :
    LocallyDistinct (targetPairedRestriction T)
      (pairedRestrictedSequence T w) := by
  exact locallyDistinct_pairedRestriction T T
    (pairedPositionsRetained_refl T) w hLocal

/-- Compression is faithful on every structure whose paired positions are
retained: equality after compression implies equality of the original arc
sets and hence of the original structures. -/
theorem eq_of_pairedRestriction_eq
    (T S₁ S₂ : SecondaryStructure n)
    (h₁ : PairedPositionsRetained T S₁)
    (h₂ : PairedPositionsRetained T S₂)
    (hRestriction :
      pairedRestriction T S₁ h₁ = pairedRestriction T S₂ h₂) :
    S₁ = S₂ := by
  apply SecondaryStructure.ext
  ext a
  constructor
  · intro ha
    let q : PairedNode S₁ := ⟨a, ha⟩
    have hCompressed : compressPairedArc T S₁ h₁ q ∈
        (pairedRestriction T S₁ h₁).arcs :=
      compressPairedArc_mem_compressedArcSet T S₁ h₁ q
    rw [hRestriction] at hCompressed
    have hLifted :
        liftPairedArc T (compressPairedArc T S₁ h₁ q) ∈ S₂.arcs :=
      (mem_pairedRestriction_iff_liftPairedArc_mem
        T S₂ h₂ (compressPairedArc T S₁ h₁ q)).mp hCompressed
    simpa [q] using hLifted
  · intro ha
    let q : PairedNode S₂ := ⟨a, ha⟩
    have hCompressed : compressPairedArc T S₂ h₂ q ∈
        (pairedRestriction T S₂ h₂).arcs :=
      compressPairedArc_mem_compressedArcSet T S₂ h₂ q
    rw [← hRestriction] at hCompressed
    have hLifted :
        liftPairedArc T (compressPairedArc T S₂ h₂ q) ∈ S₁.arcs :=
      (mem_pairedRestriction_iff_liftPairedArc_mem
        T S₁ h₁ (compressPairedArc T S₂ h₂ q)).mp hCompressed
    simpa [q] using hLifted

/-- Faithful lifting in the exact tied-competitor packaging used by the final
no-tie theorem. -/
theorem eq_target_of_competitorPairedRestriction_eq
    (T S : SecondaryStructure n)
    (hUnpaired : unpairedPositionSet S = unpairedPositionSet T)
    (hRestriction :
      competitorPairedRestriction T S hUnpaired = targetPairedRestriction T) :
    S = T := by
  apply eq_of_pairedRestriction_eq T S T
    (pairedPositionsRetained_of_unpairedPositionSet_eq hUnpaired)
    (pairedPositionsRetained_refl T)
  simpa [competitorPairedRestriction, targetPairedRestriction] using hRestriction

end RNA
