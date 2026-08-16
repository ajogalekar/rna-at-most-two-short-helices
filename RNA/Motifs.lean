module

public import RNA.IntervalTree

@[expose] public section

set_option autoImplicit false

/-!
# Forbidden interval-tree motifs

Only the virtual root and paired target nodes have paired degree.  Unpaired
children are detected separately and never contribute to that degree.
-/

namespace RNA

variable {n : Nat} (T : SecondaryStructure n)

/-- A root/paired node has at least one unpaired singleton child. -/
def HasUnpairedChild (p : PairedOrRootNode T) : Prop :=
  (unpairedChildren T p).Nonempty

instance instDecidableHasUnpairedChild (p : PairedOrRootNode T) :
    Decidable (HasUnpairedChild T p) := by
  unfold HasUnpairedChild
  infer_instance

/-- Motif `m5`: some root/paired node has paired degree greater than four. -/
def HasM5 : Prop :=
  ∃ p : PairedOrRootNode T, 4 < pairedDegree T p

/-- Motif `m3dot`: some root/paired node has an unpaired child and paired
degree greater than two. -/
def HasM3Dot : Prop :=
  ∃ p : PairedOrRootNode T,
    HasUnpairedChild T p ∧ 2 < pairedDegree T p

/-- Simultaneous avoidance of the two forbidden motifs. -/
def MotifFree : Prop :=
  ¬ HasM5 T ∧ ¬ HasM3Dot T

instance instDecidableHasM5 : Decidable (HasM5 T) := by
  unfold HasM5
  infer_instance

instance instDecidableHasM3Dot : Decidable (HasM3Dot T) := by
  unfold HasM3Dot
  infer_instance

instance instDecidableMotifFree : Decidable (MotifFree T) := by
  unfold MotifFree
  infer_instance

theorem pairedDegree_le_four (hfree : MotifFree T) (p : PairedOrRootNode T) :
    pairedDegree T p ≤ 4 := by
  apply Nat.le_of_not_gt
  intro hgt
  exact hfree.1 ⟨p, hgt⟩

theorem pairedDegree_le_two_of_unpaired (hfree : MotifFree T)
    (p : PairedOrRootNode T) (hu : HasUnpairedChild T p) :
    pairedDegree T p ≤ 2 := by
  apply Nat.le_of_not_gt
  intro hgt
  exact hfree.2 ⟨p, hu, hgt⟩

theorem root_pairedChildren_le_two_of_unpaired (hfree : MotifFree T)
    (hu : HasUnpairedChild T none) :
    pairedChildCount T none ≤ 2 := by
  exact pairedDegree_le_two_of_unpaired T hfree none hu

theorem root_pairedChildren_le_four_of_no_unpaired (hfree : MotifFree T)
    (_hu : ¬ HasUnpairedChild T none) :
    pairedChildCount T none ≤ 4 := by
  exact pairedDegree_le_four T hfree none

theorem paired_pairedChildren_le_one_of_unpaired (hfree : MotifFree T)
    (p : PairedNode T) (hu : HasUnpairedChild T (some p)) :
    pairedChildCount T (some p) ≤ 1 := by
  have hdeg := pairedDegree_le_two_of_unpaired T hfree (some p) hu
  simp only [pairedDegree] at hdeg
  omega

theorem paired_pairedChildren_le_three_of_no_unpaired (hfree : MotifFree T)
    (p : PairedNode T) (_hu : ¬ HasUnpairedChild T (some p)) :
    pairedChildCount T (some p) ≤ 3 := by
  have hdeg := pairedDegree_le_four T hfree (some p)
  simp only [pairedDegree] at hdeg
  omega

/-- Lemma 1 of the canonical manuscript, bundled in the table's order:
nonroot-with-unpaired, nonroot-without-unpaired, root-with-unpaired,
root-without-unpaired. -/
theorem motifBounds (hfree : MotifFree T) :
    (∀ p : PairedNode T,
        HasUnpairedChild T (some p) → pairedChildCount T (some p) ≤ 1) ∧
    (∀ p : PairedNode T,
        ¬ HasUnpairedChild T (some p) → pairedChildCount T (some p) ≤ 3) ∧
    (HasUnpairedChild T none → pairedChildCount T none ≤ 2) ∧
    (¬ HasUnpairedChild T none → pairedChildCount T none ≤ 4) := by
  exact ⟨paired_pairedChildren_le_one_of_unpaired T hfree,
    paired_pairedChildren_le_three_of_no_unpaired T hfree,
    root_pairedChildren_le_two_of_unpaired T hfree,
    root_pairedChildren_le_four_of_no_unpaired T hfree⟩

end RNA
