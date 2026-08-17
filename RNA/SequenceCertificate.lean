module

public import RNA.SequenceAssignment
public import RNA.GlobalColoring

@[expose] public section

set_option autoImplicit false

/-!
# Compatibility and local distinctness of the assigned sequence
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- The left letters of the actual paired children of one interface are
pairwise distinct. -/
def ChildLeftLettersDistinct (T : SecondaryStructure n) (w : Sequence n)
    (p : PairedOrRootNode T) : Prop :=
  ∀ ⦃v q : PairedNode T⦄,
    v ∈ pairedChildren T p → q ∈ pairedChildren T p →
      w v.val.left = w q.val.left → v = q

/-- Manuscript Lemma 13: root child-left letters are pairwise distinct; at a
nonroot pair they are also all different from the parent's right letter. -/
def LocallyDistinct (T : SecondaryStructure n) (w : Sequence n) : Prop :=
  ChildLeftLettersDistinct T w none ∧
    ∀ p : PairedNode T,
      ChildLeftLettersDistinct T w (some p) ∧
        ∀ v ∈ pairedChildren T (some p),
          w v.val.left ≠ w p.val.right

private theorem eq_of_childrenOfColor_card_le_one
    (χ : Coloring T) (p : PairedOrRootNode T) (c : Color)
    {v q : PairedNode T}
    (hcard : (childrenOfColor χ p c).card ≤ 1)
    (hv : v ∈ pairedChildren T p) (hvc : χ v = c)
    (hq : q ∈ pairedChildren T p) (hqc : χ q = c) : v = q := by
  apply (Finset.card_le_one_iff.mp hcard)
  · simp [childrenOfColor, hv, hvc]
  · simp [childrenOfColor, hq, hqc]

private theorem no_child_of_childrenOfColor_card_eq_zero
    (χ : Coloring T) (p : PairedOrRootNode T) (c : Color)
    {v : PairedNode T}
    (hzero : (childrenOfColor χ p c).card = 0)
    (hv : v ∈ pairedChildren T p) (hvc : χ v = c) : False := by
  have hvMem : v ∈ childrenOfColor χ p c := by
    simp [childrenOfColor, hv, hvc]
  have hempty : childrenOfColor χ p c = ∅ := Finset.card_eq_zero.mp hzero
  rw [hempty] at hvMem
  simpa using hvMem

/-- Pairwise distinct child-left letters at every root/paired interface. -/
theorem childLeftLettersDistinct_sequenceOfProperColoring
    (χ : Coloring T) (hProper : ProperColoring χ)
    (p : PairedOrRootNode T) :
    ChildLeftLettersDistinct T (sequenceOfProperColoring χ hProper) p := by
  intro v q hv hq hletters
  cases hvc : χ v with
  | black =>
      cases hqc : χ q with
      | black =>
          exact eq_of_childrenOfColor_card_le_one χ p Color.black
            (black_children_card_le_one χ hProper p) hv hvc hq hqc
      | white =>
          have hvLetter := sequenceOfProperColoring_black_left χ hProper v hvc
          have hqLetter := sequenceOfProperColoring_white_left χ hProper q hqc
          simp_all
      | grey =>
          have hvLetter := sequenceOfProperColoring_black_left χ hProper v hvc
          rcases sequenceOfProperColoring_grey_left χ hProper q hqc with
            hqA | hqU <;> simp_all
  | white =>
      cases hqc : χ q with
      | black =>
          have hvLetter := sequenceOfProperColoring_white_left χ hProper v hvc
          have hqLetter := sequenceOfProperColoring_black_left χ hProper q hqc
          simp_all
      | white =>
          exact eq_of_childrenOfColor_card_le_one χ p Color.white
            (white_children_card_le_one χ hProper p) hv hvc hq hqc
      | grey =>
          have hvLetter := sequenceOfProperColoring_white_left χ hProper v hvc
          rcases sequenceOfProperColoring_grey_left χ hProper q hqc with
            hqA | hqU <;> simp_all
  | grey =>
      cases hqc : χ q with
      | black =>
          rcases sequenceOfProperColoring_grey_left χ hProper v hvc with
            hvA | hvU
          · have hqLetter := sequenceOfProperColoring_black_left χ hProper q hqc
            simp_all
          · have hqLetter := sequenceOfProperColoring_black_left χ hProper q hqc
            simp_all
      | white =>
          rcases sequenceOfProperColoring_grey_left χ hProper v hvc with
            hvA | hvU
          · have hqLetter := sequenceOfProperColoring_white_left χ hProper q hqc
            simp_all
          · have hqLetter := sequenceOfProperColoring_white_left χ hProper q hqc
            simp_all
      | grey =>
          by_cases hvq : v = q
          · exact hvq
          · cases p with
            | none =>
                have hne := leftLetter_ne_of_distinct_grey_anchor_children
                  χ hProper none hv hvc hq hqc
                  (by intro r h; cases h) hvq
                exact False.elim (hne (by simpa using hletters))
            | some r =>
                cases hrc : χ r with
                | black =>
                    have hne := leftLetter_ne_of_distinct_grey_anchor_children
                      χ hProper (some r) hv hvc hq hqc
                      (by
                        intro s hrs
                        have hrs' : r = s := Option.some.inj hrs
                        simpa [← hrs', hrc]) hvq
                    exact False.elim (hne (by simpa using hletters))
                | white =>
                    have hne := leftLetter_ne_of_distinct_grey_anchor_children
                      χ hProper (some r) hv hvc hq hqc
                      (by
                        intro s hrs
                        have hrs' : r = s := Option.some.inj hrs
                        simpa [← hrs', hrc]) hvq
                    exact False.elim (hne (by simpa using hletters))
                | grey =>
                    exact eq_of_childrenOfColor_card_le_one χ (some r) Color.grey
                      (grey_children_card_le_one_of_parent_grey χ hProper r hrc)
                      hv hvc hq hqc

private theorem child_left_ne_parent_right_black
    (χ : Coloring T) (hProper : ProperColoring χ)
    (p v : PairedNode T) (hpBlack : χ p = Color.black)
    (hv : v ∈ pairedChildren T (some p)) :
    sequenceOfProperColoring χ hProper v.val.left ≠
      sequenceOfProperColoring χ hProper p.val.right := by
  cases hvc : χ v with
  | black => simp [hpBlack, hvc]
  | white =>
      exact False.elim (no_child_of_childrenOfColor_card_eq_zero
        χ (some p) Color.white
        (white_children_card_eq_zero_of_parent_black χ hProper p hpBlack)
        hv hvc)
  | grey =>
      rcases sequenceOfProperColoring_grey_left χ hProper v hvc with
        hvA | hvU <;> simp_all

private theorem child_left_ne_parent_right_white
    (χ : Coloring T) (hProper : ProperColoring χ)
    (p v : PairedNode T) (hpWhite : χ p = Color.white)
    (hv : v ∈ pairedChildren T (some p)) :
    sequenceOfProperColoring χ hProper v.val.left ≠
      sequenceOfProperColoring χ hProper p.val.right := by
  cases hvc : χ v with
  | black =>
      exact False.elim (no_child_of_childrenOfColor_card_eq_zero
        χ (some p) Color.black
        (black_children_card_eq_zero_of_parent_white χ hProper p hpWhite)
        hv hvc)
  | white => simp [hpWhite, hvc]
  | grey =>
      rcases sequenceOfProperColoring_grey_left χ hProper v hvc with
        hvA | hvU <;> simp_all

private theorem child_left_ne_parent_right_grey
    (χ : Coloring T) (hProper : ProperColoring χ)
    (p v : PairedNode T) (hpGrey : χ p = Color.grey)
    (hv : v ∈ pairedChildren T (some p)) :
    sequenceOfProperColoring χ hProper v.val.left ≠
      sequenceOfProperColoring χ hProper p.val.right := by
  have hvParent : parent T (Sum.inl v) = some p := by
    simpa [pairedChildren] using hv
  cases hvc : χ v with
  | black =>
      rcases sequenceOfProperColoring_grey_left χ hProper p hpGrey with
        hpA | hpU <;> simp_all
  | white =>
      rcases sequenceOfProperColoring_grey_left χ hProper p hpGrey with
        hpA | hpU <;> simp_all
  | grey =>
      rw [sequenceOfProperColoring_left,
        leftLetter_grey_child_of_grey_parent χ hProper p v hvc hvParent hpGrey,
        sequenceOfProperColoring_right]
      exact Nucleotide.self_ne_comp _

/-- Nonroot child-left letters also avoid their parent's right letter. -/
theorem childLeft_ne_parentRight_sequenceOfProperColoring
    (χ : Coloring T) (hProper : ProperColoring χ)
    (p v : PairedNode T) (hv : v ∈ pairedChildren T (some p)) :
    sequenceOfProperColoring χ hProper v.val.left ≠
      sequenceOfProperColoring χ hProper p.val.right := by
  cases hpc : χ p with
  | black => exact child_left_ne_parent_right_black χ hProper p v hpc hv
  | white => exact child_left_ne_parent_right_white χ hProper p v hpc hv
  | grey => exact child_left_ne_parent_right_grey χ hProper p v hpc hv

/-- Every target arc joins the exact Watson--Crick complements assigned to its
actual endpoints. -/
theorem structureCompatible_sequenceOfProperColoring
    (χ : Coloring T) (hProper : ProperColoring χ) :
    StructureCompatible (sequenceOfProperColoring χ hProper) T := by
  intro a ha
  let v : PairedNode T := ⟨a, ha⟩
  change Compatible
    (sequenceOfProperColoring χ hProper v.val.left)
    (sequenceOfProperColoring χ hProper v.val.right)
  rw [sequenceOfProperColoring_right_eq_comp_left]
  exact compatible_comp _

/-- The sequence from every proper coloring satisfies manuscript Lemma 13. -/
theorem locallyDistinct_sequenceOfProperColoring
    (χ : Coloring T) (hProper : ProperColoring χ) :
    LocallyDistinct T (sequenceOfProperColoring χ hProper) := by
  refine ⟨childLeftLettersDistinct_sequenceOfProperColoring χ hProper none, ?_⟩
  intro p
  exact ⟨childLeftLettersDistinct_sequenceOfProperColoring χ hProper (some p),
    childLeft_ne_parentRight_sequenceOfProperColoring χ hProper p⟩

/-- Proof-bearing local sequence-assignment object. -/
structure SequenceAssignmentCertificate
    (T : SecondaryStructure n) (χ : Coloring T) where
  proper : ProperColoring χ
  leftLetter : PairedNode T → Nucleotide
  leftLetter_eq : leftLetter = leftLetterOfProperColoring χ proper
  sequence : Sequence n
  sequence_eq : sequence = sequenceOfProperColoring χ proper
  targetCompatible : StructureCompatible sequence T
  localDistinctness : LocallyDistinct T sequence

/-- Canonical certificate for one specified proper coloring. -/
noncomputable def sequenceAssignmentCertificate
    (χ : Coloring T) (hProper : ProperColoring χ) :
    SequenceAssignmentCertificate T χ where
  proper := hProper
  leftLetter := leftLetterOfProperColoring χ hProper
  leftLetter_eq := rfl
  sequence := sequenceOfProperColoring χ hProper
  sequence_eq := rfl
  targetCompatible := structureCompatible_sequenceOfProperColoring χ hProper
  localDistinctness := locallyDistinct_sequenceOfProperColoring χ hProper

/-- Milestone-3 coloring plus its one retained complete sequence assignment. -/
structure GlobalSequenceAssignmentCertificate
    (T : SecondaryStructure n) (hK : InTargetClassK T) where
  coloringCertificate : GlobalColoringCertificate T hK
  assignment : SequenceAssignmentCertificate T coloringCertificate.coloring

/-- Canonical class-K sequence assignment, based on the canonical global
coloring certificate and no separately chosen witness. -/
noncomputable def globalSequenceAssignmentCertificate
    (hK : InTargetClassK T) :
    GlobalSequenceAssignmentCertificate T hK := by
  let C := globalColoringCertificate hK
  exact {
    coloringCertificate := C
    assignment := sequenceAssignmentCertificate C.coloring C.proper }

end RNA
