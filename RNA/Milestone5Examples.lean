module

public import RNA.OneShortHelixDesignability
public import RNA.Milestone4Examples

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# Kernel-checked Milestone 5 examples and negative controls

The controls below exercise the final theorem, the general no-tie theorem,
saturated local-distinctness uniqueness, and the common-unpaired-position
compression used in the final proof.
-/

namespace RNA.Milestone5Examples

open Nucleotide

/-! ## 1. The final theorem on `(())` uses the retained `GGCC` witness -/

theorem nestedTarget_globalSequence_eq_ggcc :
    (globalSequenceCertificate Examples.nestedTarget_in_classK).sequence =
      Examples.ggcc := by
  change Milestone4Examples.smallestCanonicalSequence = Examples.ggcc
  exact Milestone4Examples.smallestCanonicalSequence_eq_ggcc

theorem nestedTarget_final_uniqueDesigns :
    UniqueDesigns
      (globalSequenceCertificate Examples.nestedTarget_in_classK).sequence
      Examples.nestedTarget :=
  oneShortHelix_uniqueDesigns Examples.nestedTarget_in_classK

theorem nestedTarget_final_witness :
    ∃ w : Sequence 4,
      w = Examples.ggcc ∧ UniqueDesigns w Examples.nestedTarget := by
  refine ⟨(globalSequenceCertificate
    Examples.nestedTarget_in_classK).sequence, ?_, ?_⟩
  · exact nestedTarget_globalSequence_eq_ggcc
  · exact nestedTarget_final_uniqueDesigns

/-! ## 2. `AUAU` is still rejected because `()()` ties `(())` -/

theorem auau_tie_control :
    StructureCompatible Examples.auau Examples.nestedTarget ∧
      StructureCompatible Examples.auau Examples.disjointTarget ∧
      Examples.disjointTarget ≠ Examples.nestedTarget ∧
      pairCount Examples.disjointTarget =
        pairCount Examples.nestedTarget :=
  Examples.auau_disjoint_tie

theorem auau_not_unique_design_control :
    ¬ UniqueDesigns Examples.auau Examples.nestedTarget :=
  Examples.auau_not_unique_design

/-! ## 3. General no-tie theorem with a target-unpaired position -/

theorem rootUnpaired_has_targetUnpaired_position :
    ¬ Milestone3Examples.rootUnpairedTarget.positionPaired (0 : Fin 5) := by
  decide

theorem rootUnpairedCertificate_separated :
    Separated Milestone3Examples.rootUnpairedCertificate.coloring :=
  strongTwoSeparated_implies_separated
    Milestone3Examples.rootUnpairedCertificate.coloring
    Milestone3Examples.rootUnpairedCertificate_strong

theorem rootUnpaired_general_noTie
    (S : SecondaryStructure 5)
    (hS : StructureCompatible
      (sequenceOfProperColoring
        Milestone3Examples.rootUnpairedCertificate.coloring
        Milestone3Examples.rootUnpairedCertificate.proper) S)
    (hEq : pairCount S =
      pairCount Milestone3Examples.rootUnpairedTarget) :
    S = Milestone3Examples.rootUnpairedTarget := by
  exact noTie_sequenceOfProperSeparatedColoring
    Milestone3Examples.rootUnpairedCertificate.coloring
    Milestone3Examples.rootUnpairedCertificate.proper
    rootUnpairedCertificate_separated S hS hEq

/-! ## 4. A positive saturated local-distinctness example -/

theorem nestedTarget_saturated :
    SaturatedStructure Examples.nestedTarget := by
  intro i
  fin_cases i <;> decide

theorem ggcc_nestedTarget_compatible :
    StructureCompatible Examples.ggcc Examples.nestedTarget := by
  decide

theorem ggcc_nestedTarget_locallyDistinct :
    LocallyDistinct Examples.nestedTarget Examples.ggcc := by
  have hLocal := locallyDistinct_sequenceOfProperColoring
    Milestone4Examples.nestedAllBlackColoring
    Milestone4Examples.nestedAllBlackColoring_proper
  change LocallyDistinct Examples.nestedTarget
    Milestone4Examples.nestedAllBlackSequence at hLocal
  rw [Milestone4Examples.nestedAllBlackSequence_eq_ggcc] at hLocal
  exact hLocal

theorem ggcc_unique_saturated_matching
    (P : SecondaryStructure 4) (hPSat : SaturatedStructure P)
    (hPComp : StructureCompatible Examples.ggcc P) :
    P = Examples.nestedTarget := by
  exact saturated_unique_of_localDistinctness
    Examples.nestedTarget Examples.ggcc nestedTarget_saturated
    ggcc_nestedTarget_compatible ggcc_nestedTarget_locallyDistinct
    P hPSat hPComp

/-! ## 5. Failure without local distinctness -/

theorem auau_nestedTarget_not_locallyDistinct :
    ¬ LocallyDistinct Examples.nestedTarget Examples.auau := by
  intro hLocal
  have hne := hLocal.2 Milestone4Examples.nestedOuterNode |>.2
    Milestone4Examples.nestedInnerNode (by decide)
  apply hne
  decide

theorem auau_disjoint_is_second_perfect_matching :
    SaturatedStructure Examples.disjointTarget ∧
      StructureCompatible Examples.auau Examples.disjointTarget ∧
      Examples.disjointTarget ≠ Examples.nestedTarget := by
  constructor
  · intro i
    fin_cases i <;> decide
  · exact ⟨Examples.auau_disjoint_tie.2.1,
      Examples.auau_disjoint_tie.2.2.1⟩

/-! ## 6. Concrete deletion and compression of one common unpaired position

The five-position target is `(()) .`, the competitor is `()() .`, and both
leave position `4` unpaired.  Compression therefore gives the existing
four-position nested/disjoint structures and restricts `AUAUC` to `AUAU`.
-/

def compressionOuterArc : Arc 5 := ⟨0, 3, by decide⟩
def compressionInnerArc : Arc 5 := ⟨1, 2, by decide⟩

def compressionTarget : SecondaryStructure 5 where
  arcs := {compressionOuterArc, compressionInnerArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

def compressionLeftArc : Arc 5 := ⟨0, 1, by decide⟩
def compressionRightArc : Arc 5 := ⟨2, 3, by decide⟩

def compressionCompetitor : SecondaryStructure 5 where
  arcs := {compressionLeftArc, compressionRightArc}
  isPartialMatching := by decide
  isNoncrossing := by decide

def compressionSequence : Sequence 5 := ![A, U, A, U, C]

theorem compression_setup :
    StructureCompatible compressionSequence compressionTarget ∧
      StructureCompatible compressionSequence compressionCompetitor ∧
      compressionCompetitor ≠ compressionTarget ∧
      pairCount compressionCompetitor = pairCount compressionTarget := by
  decide

theorem compression_common_unpaired :
    unpairedPositionSet compressionCompetitor =
      unpairedPositionSet compressionTarget := by
  decide

theorem compression_retained_positions :
    targetPairedPositionSet compressionTarget =
      ({(4 : Fin 5)}ᶜ : Finset (Fin 5)) := by
  decide

theorem compression_skeleton_length :
    pairedSkeletonLength compressionTarget = 4 := by
  unfold pairedSkeletonLength
  rw [compression_retained_positions]
  decide

theorem compressionExpansion_apply (i : Fin 4) :
    (pairedPositionExpansion compressionTarget
      (Fin.cast compression_skeleton_length.symm i)).val = Fin.castSucc i := by
  let f : Fin (pairedSkeletonLength compressionTarget) ↪o Fin 5 :=
    (Fin.castOrderIso compression_skeleton_length).toOrderEmbedding.trans
      Fin.castSuccOrderEmb
  have hf : ∀ j, f j ∈ targetPairedPositionSet compressionTarget := by
    intro j
    rw [compression_retained_positions]
    simp only [Finset.mem_compl, Finset.mem_singleton]
    intro heq
    have heqVal := congrArg Fin.val heq
    have hj := (Fin.cast compression_skeleton_length j).isLt
    change (Fin.cast compression_skeleton_length j).val = 4 at heqVal
    omega
  have heq :
      (targetPairedPositionSet compressionTarget).orderEmbOfFin rfl = f :=
    (Finset.orderEmbOfFin_unique' rfl hf).symm
  change
    (targetPairedPositionSet compressionTarget).orderEmbOfFin rfl
        (Fin.cast compression_skeleton_length.symm i) = Fin.castSucc i
  rw [heq]
  apply Fin.ext
  rfl

noncomputable def compressionRestrictedSequence : Sequence 4 :=
  fun i => pairedRestrictedSequence compressionTarget compressionSequence
    (Fin.cast compression_skeleton_length.symm i)

noncomputable def compressionTargetRestriction : SecondaryStructure 4 :=
  (targetPairedRestriction compressionTarget).reindexOrderIso
    (Fin.castOrderIso compression_skeleton_length)

noncomputable def compressionCompetitorRestriction : SecondaryStructure 4 :=
  (competitorPairedRestriction compressionTarget compressionCompetitor
      compression_common_unpaired).reindexOrderIso
    (Fin.castOrderIso compression_skeleton_length)

theorem compressionRestrictedSequence_eq_auau :
    compressionRestrictedSequence = Examples.auau := by
  funext i
  simp only [compressionRestrictedSequence, pairedRestrictedSequence,
    compressionExpansion_apply]
  fin_cases i <;> rfl

theorem compression_lift_cast_eq_castSucc (a : Arc 4) :
    liftPairedArc compressionTarget
        (a.mapOrderEmbedding
          (Fin.castOrderIso compression_skeleton_length).symm.toOrderEmbedding) =
      a.mapOrderEmbedding Fin.castSuccOrderEmb := by
  apply Arc.ext
  · change
      (pairedPositionExpansion compressionTarget
        (Fin.cast compression_skeleton_length.symm a.left)).val =
          Fin.castSucc a.left
    exact compressionExpansion_apply a.left
  · change
      (pairedPositionExpansion compressionTarget
        (Fin.cast compression_skeleton_length.symm a.right)).val =
          Fin.castSucc a.right
    exact compressionExpansion_apply a.right

theorem mem_compressionTargetRestriction_iff (a : Arc 4) :
    a ∈ compressionTargetRestriction.arcs ↔
      a.mapOrderEmbedding Fin.castSuccOrderEmb ∈ compressionTarget.arcs := by
  let e := Fin.castOrderIso compression_skeleton_length
  let c := a.mapOrderEmbedding e.symm.toOrderEmbedding
  have hca : c.mapOrderEmbedding e.toOrderEmbedding = a := by
    apply Arc.ext <;> apply Fin.ext <;> rfl
  calc
    a ∈ compressionTargetRestriction.arcs ↔
        c.mapOrderEmbedding e.toOrderEmbedding ∈
          compressionTargetRestriction.arcs := by rw [hca]
    _ ↔ c ∈ (targetPairedRestriction compressionTarget).arcs := by
      exact SecondaryStructure.mapOrderEmbedding_mem_iff
        e.toOrderEmbedding _ c
    _ ↔ liftPairedArc compressionTarget c ∈ compressionTarget.arcs :=
      mem_targetPairedRestriction_iff_liftPairedArc_mem compressionTarget c
    _ ↔ a.mapOrderEmbedding Fin.castSuccOrderEmb ∈
          compressionTarget.arcs := by
      rw [show liftPairedArc compressionTarget c =
          a.mapOrderEmbedding Fin.castSuccOrderEmb by
        exact compression_lift_cast_eq_castSucc a]

theorem mem_compressionCompetitorRestriction_iff (a : Arc 4) :
    a ∈ compressionCompetitorRestriction.arcs ↔
      a.mapOrderEmbedding Fin.castSuccOrderEmb ∈
        compressionCompetitor.arcs := by
  let e := Fin.castOrderIso compression_skeleton_length
  let c := a.mapOrderEmbedding e.symm.toOrderEmbedding
  have hca : c.mapOrderEmbedding e.toOrderEmbedding = a := by
    apply Arc.ext <;> apply Fin.ext <;> rfl
  calc
    a ∈ compressionCompetitorRestriction.arcs ↔
        c.mapOrderEmbedding e.toOrderEmbedding ∈
          compressionCompetitorRestriction.arcs := by rw [hca]
    _ ↔ c ∈
        (competitorPairedRestriction compressionTarget compressionCompetitor
          compression_common_unpaired).arcs := by
      exact SecondaryStructure.mapOrderEmbedding_mem_iff
        e.toOrderEmbedding _ c
    _ ↔ liftPairedArc compressionTarget c ∈
          compressionCompetitor.arcs :=
      mem_competitorPairedRestriction_iff_liftPairedArc_mem
        compressionTarget compressionCompetitor compression_common_unpaired c
    _ ↔ a.mapOrderEmbedding Fin.castSuccOrderEmb ∈
          compressionCompetitor.arcs := by
      rw [show liftPairedArc compressionTarget c =
          a.mapOrderEmbedding Fin.castSuccOrderEmb by
        exact compression_lift_cast_eq_castSucc a]

theorem compressionTargetRestriction_eq_nestedTarget :
    compressionTargetRestriction = Examples.nestedTarget := by
  apply SecondaryStructure.ext
  ext a
  rw [mem_compressionTargetRestriction_iff]
  rcases a with ⟨left, right, ordered⟩
  fin_cases left <;> fin_cases right <;>
    simp_all [compressionTarget, compressionOuterArc, compressionInnerArc,
      Examples.nestedTarget, Examples.outerArc, Examples.innerArc,
      Arc.mapOrderEmbedding]

theorem compressionCompetitorRestriction_eq_disjointTarget :
    compressionCompetitorRestriction = Examples.disjointTarget := by
  apply SecondaryStructure.ext
  ext a
  rw [mem_compressionCompetitorRestriction_iff]
  rcases a with ⟨left, right, ordered⟩
  fin_cases left <;> fin_cases right <;>
    simp_all [compressionCompetitor, compressionLeftArc,
      compressionRightArc, Examples.disjointTarget,
      Examples.leftAdjacentArc, Examples.rightAdjacentArc,
      Arc.mapOrderEmbedding]

theorem compressionRestrictions_distinct :
    compressionCompetitorRestriction ≠ compressionTargetRestriction := by
  rw [compressionCompetitorRestriction_eq_disjointTarget,
    compressionTargetRestriction_eq_nestedTarget]
  exact Examples.auau_disjoint_tie.2.2.1

/-- Equality of the two concrete compressed restrictions would faithfully
lift to equality of the original target and candidate. -/
theorem compression_faithful_lifting
    (hRestriction :
      compressionCompetitorRestriction = compressionTargetRestriction) :
    compressionCompetitor = compressionTarget := by
  have hRaw :
      competitorPairedRestriction compressionTarget compressionCompetitor
          compression_common_unpaired =
        targetPairedRestriction compressionTarget := by
    apply SecondaryStructure.mapOrderEmbedding_injective
      (Fin.castOrderIso compression_skeleton_length).toOrderEmbedding
    exact hRestriction
  exact eq_target_of_competitorPairedRestriction_eq
    compressionTarget compressionCompetitor compression_common_unpaired hRaw

/-! ## 7. The deliberate Milestone-4 inventory tie remains a tie -/

theorem inventoryTie_still_ties :
    StructureCompatible Milestone4Examples.inventorySequence
        Milestone4Examples.inventoryTie ∧
      Milestone4Examples.inventoryTie ≠
        Milestone4Examples.inventoryTarget ∧
      pairCount Milestone4Examples.inventoryTie =
        pairCount Milestone4Examples.inventoryTarget :=
  ⟨Milestone4Examples.inventoryTie_compatible,
    Milestone4Examples.inventoryTie_distinct,
    Milestone4Examples.inventoryTie_pairCount_eq⟩

/-- The no-tie theorem does not apply to the inventory control: its proper
coloring is not separated.  Otherwise the retained tie would equal the
target, contradicting the checked distinctness above. -/
theorem inventoryColoring_not_separated :
    ¬ Separated Milestone4Examples.inventoryColoring := by
  intro hSeparated
  apply Milestone4Examples.inventoryTie_distinct
  exact noTie_sequenceOfProperSeparatedColoring
    Milestone4Examples.inventoryColoring
    Milestone4Examples.inventoryColoring_proper hSeparated
    Milestone4Examples.inventoryTie
    Milestone4Examples.inventoryTie_compatible
    Milestone4Examples.inventoryTie_pairCount_eq

end RNA.Milestone5Examples
