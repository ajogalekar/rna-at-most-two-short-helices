module

public import RNA.AtMostTwoShort.Examples

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000

/-!
# Publication semantic examples

This module contains the concrete targets and literal sequences printed in the
paper.  It is intentionally downstream of the final theorem module and is not
imported by `RNA.AtMostTwoShort.Designability` or by `RNA.lean`.

Every finite computation below is checked by the ordinary Lean kernel.  The
two positive sequence claims are obtained by exhibiting proper separated
colorings whose deterministic sequence assignments are exactly the printed
words, and then applying the generic no-tie theorem.
-/

namespace RNA.PublicationExamples

open Nucleotide

/-! ## Publication target T1: `(())(())((()))` -/

/-- The first publication target, in dot-bracket notation
`(())(())((()))`. -/
abbrev t1Target : SecondaryStructure 14 := degreeThreeTwoShortTarget

theorem t1Target_inTargetClassKLeTwo :
    InTargetClassKLeTwo t1Target :=
  degreeThreeTwoShortTarget_inTargetClassK2.1

theorem t1Target_pairCount : pairCount t1Target = 7 := by
  decide

/-- The literal first publication sequence `AGCUUGCAGGGCCC`. -/
def w1 : Sequence 14 :=
  ![A, G, C, U, U, G, C, A, G, G, G, C, C, C]

/-- The coloring encoded by `w1`: the two short outer pairs are grey and all
other pairs are black. -/
def t1Coloring : Coloring t1Target := fun v =>
  if v.val.left.val = 0 || v.val.left.val = 4 then Color.grey
  else Color.black

theorem t1Coloring_proper : ProperColoring t1Coloring := by
  decide

theorem t1Coloring_strongTwoSeparated :
    StrongTwoSeparated t1Coloring := by
  decide

theorem t1Coloring_separated : Separated t1Coloring :=
  strongTwoSeparated_implies_separated t1Coloring
    t1Coloring_strongTwoSeparated

def t1Node03 : PairedNode t1Target :=
  ⟨⟨0, 3, by decide⟩, by decide⟩

def t1Node12 : PairedNode t1Target :=
  ⟨⟨1, 2, by decide⟩, by decide⟩

def t1Node47 : PairedNode t1Target :=
  ⟨⟨4, 7, by decide⟩, by decide⟩

def t1Node56 : PairedNode t1Target :=
  ⟨⟨5, 6, by decide⟩, by decide⟩

def t1Node813 : PairedNode t1Target :=
  ⟨⟨8, 13, by decide⟩, by decide⟩

def t1Node912 : PairedNode t1Target :=
  ⟨⟨9, 12, by decide⟩, by decide⟩

def t1Node1011 : PairedNode t1Target :=
  ⟨⟨10, 11, by decide⟩, by decide⟩

theorem t1Node03_leftLetter :
    leftLetterOfProperColoring t1Coloring t1Coloring_proper t1Node03 = A := by
  rw [leftLetter_grey_at_anchor t1Coloring t1Coloring_proper t1Node03
    (by decide) none (by decide) (by decide)]
  let L := orderedGreyChildren t1Coloring none
  have hleftMem : t1Node03 ∈ L :=
    (mem_orderedGreyChildren_iff t1Coloring none t1Node03).2
      ⟨by decide, by decide⟩
  have hrightMem : t1Node47 ∈ L :=
    (mem_orderedGreyChildren_iff t1Coloring none t1Node47).2
      ⟨by decide, by decide⟩
  have hleftRankLt := List.idxOf_lt_length_of_mem hleftMem
  have hrightRankLt := List.idxOf_lt_length_of_mem hrightMem
  have hsorted : L.SortedLT := by
    exact Finset.sortedLT_sort (childrenOfColor t1Coloring none Color.grey)
  have hnodeOrder : t1Node03 < t1Node47 := by
    decide
  have hrankOrder :
      greySiblingRank t1Coloring none t1Node03 <
        greySiblingRank t1Coloring none t1Node47 := by
    change L.idxOf t1Node03 < L.idxOf t1Node47
    rw [← hsorted.getElem_lt_getElem_iff
      (hi := hleftRankLt) (hj := hrightRankLt)]
    simpa using hnodeOrder
  have hleftLtTwo := greySiblingRank_lt_two t1Coloring
    t1Coloring_proper none t1Node03 (by decide) (by decide)
  have hrightLtTwo := greySiblingRank_lt_two t1Coloring
    t1Coloring_proper none t1Node47 (by decide) (by decide)
  have hleftZero : greySiblingRank t1Coloring none t1Node03 = 0 := by
    omega
  simp [greyRankLetter, hleftZero]

theorem t1Node47_leftLetter :
    leftLetterOfProperColoring t1Coloring t1Coloring_proper t1Node47 = U := by
  rw [leftLetter_grey_at_anchor t1Coloring t1Coloring_proper t1Node47
    (by decide) none (by decide) (by decide)]
  let L := orderedGreyChildren t1Coloring none
  have hleftMem : t1Node03 ∈ L :=
    (mem_orderedGreyChildren_iff t1Coloring none t1Node03).2
      ⟨by decide, by decide⟩
  have hrightMem : t1Node47 ∈ L :=
    (mem_orderedGreyChildren_iff t1Coloring none t1Node47).2
      ⟨by decide, by decide⟩
  have hleftRankLt := List.idxOf_lt_length_of_mem hleftMem
  have hrightRankLt := List.idxOf_lt_length_of_mem hrightMem
  have hsorted : L.SortedLT := by
    exact Finset.sortedLT_sort (childrenOfColor t1Coloring none Color.grey)
  have hnodeOrder : t1Node03 < t1Node47 := by
    decide
  have hrankOrder :
      greySiblingRank t1Coloring none t1Node03 <
        greySiblingRank t1Coloring none t1Node47 := by
    change L.idxOf t1Node03 < L.idxOf t1Node47
    rw [← hsorted.getElem_lt_getElem_iff
      (hi := hleftRankLt) (hj := hrightRankLt)]
    simpa using hnodeOrder
  have hrightLtTwo := greySiblingRank_lt_two t1Coloring
    t1Coloring_proper none t1Node47 (by decide) (by decide)
  have hrightOne : greySiblingRank t1Coloring none t1Node47 = 1 := by
    omega
  simp [greyRankLetter, hrightOne]

noncomputable def t1AssignedSequence : Sequence 14 :=
  sequenceOfProperColoring t1Coloring t1Coloring_proper

theorem t1AssignedSequence_eq_w1 : t1AssignedSequence = w1 := by
  funext i
  fin_cases i
  · change t1AssignedSequence t1Node03.val.left = A
    simpa [t1AssignedSequence] using t1Node03_leftLetter
  · change t1AssignedSequence t1Node12.val.left = G
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_left t1Coloring t1Coloring_proper
        t1Node12 (by decide))
  · change t1AssignedSequence t1Node12.val.right = C
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_right t1Coloring t1Coloring_proper
        t1Node12 (by decide))
  · change t1AssignedSequence t1Node03.val.right = U
    simp [t1AssignedSequence, t1Node03_leftLetter]
  · change t1AssignedSequence t1Node47.val.left = U
    simpa [t1AssignedSequence] using t1Node47_leftLetter
  · change t1AssignedSequence t1Node56.val.left = G
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_left t1Coloring t1Coloring_proper
        t1Node56 (by decide))
  · change t1AssignedSequence t1Node56.val.right = C
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_right t1Coloring t1Coloring_proper
        t1Node56 (by decide))
  · change t1AssignedSequence t1Node47.val.right = A
    simp [t1AssignedSequence, t1Node47_leftLetter]
  · change t1AssignedSequence t1Node813.val.left = G
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_left t1Coloring t1Coloring_proper
        t1Node813 (by decide))
  · change t1AssignedSequence t1Node912.val.left = G
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_left t1Coloring t1Coloring_proper
        t1Node912 (by decide))
  · change t1AssignedSequence t1Node1011.val.left = G
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_left t1Coloring t1Coloring_proper
        t1Node1011 (by decide))
  · change t1AssignedSequence t1Node1011.val.right = C
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_right t1Coloring t1Coloring_proper
        t1Node1011 (by decide))
  · change t1AssignedSequence t1Node912.val.right = C
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_right t1Coloring t1Coloring_proper
        t1Node912 (by decide))
  · change t1AssignedSequence t1Node813.val.right = C
    simpa [t1AssignedSequence] using
      (sequenceOfProperColoring_black_right t1Coloring t1Coloring_proper
        t1Node813 (by decide))

theorem w1_uniqueDesigns_t1Target : UniqueDesigns w1 t1Target := by
  rw [← t1AssignedSequence_eq_w1]
  exact uniqueDesigns_sequenceOfProperSeparatedColoring
    t1Coloring t1Coloring_proper t1Coloring_separated

/-! ## Publication target T2: `(((((((())(()))))((())))))` -/

/-- The corrected second publication target, in dot-bracket notation
`(((((((())(()))))((())))))`. -/
abbrev t2Target : SecondaryStructure 26 := internalTwoDemandTarget

theorem t2Target_inTargetClassKLeTwo :
    InTargetClassKLeTwo t2Target :=
  internalTwoDemandTarget_inTargetClassK2.1

theorem t2Target_pairCount : pairCount t2Target = 13 := by
  decide

/-- The corrected literal second publication sequence
`GGGAGGAGCUUGCACCUGGGCCCCCC`. -/
def w2 : Sequence 26 :=
  ![G, G, G, A, G, G, A, G, C, U, U, G, C,
    A, C, C, U, G, G, G, C, C, C, C, C, C]

/-- The proper strongly separated coloring encoded by the corrected `w2`.
The pairs beginning at 3, 6, and 10 are grey and every other pair is black.
Along maximal helices this is the deterministic F/Q pattern `BBB`, `GBB`,
`GB`, `GB`, `BBB` with unpaired residue `xi = 0`. -/
def t2Coloring : Coloring t2Target := fun v =>
  if v.val.left.val = 3 || v.val.left.val = 6 ||
      v.val.left.val = 10 then Color.grey
  else Color.black

theorem t2Coloring_proper : ProperColoring t2Coloring := by
  decide

set_option maxHeartbeats 800000 in
-- Reducing all exact levels of the explicit 26-position target needs headroom.
theorem t2Coloring_strongTwoSeparated :
    StrongTwoSeparated t2Coloring := by
  decide

theorem t2Coloring_strongTwoSeparatedWith_zero :
    StrongTwoSeparatedWith t2Coloring 0 := by
  let g : PairedNode t2Target :=
    ⟨⟨3, 16, by decide⟩, by decide⟩
  obtain ⟨xi, hxi⟩ :=
    (strongTwoSeparated_iff_exists_with t2Coloring).1
      t2Coloring_strongTwoSeparated
  rcases Parity.eq_or_eq_opposite 0 xi with hzero | hone
  · simpa [hzero] using hxi
  · have hxiOne : xi = 1 := by
      simpa [Parity.opposite] using hone
    have hgrey := hxi.2 g (by decide)
    have hlevel :
        levelParity (pairedLevel t2Coloring g) = 1 := by
      decide
    rw [hlevel, hxiOne] at hgrey
    simp [Parity.opposite] at hgrey

theorem t2Coloring_separated : Separated t2Coloring :=
  strongTwoSeparated_implies_separated t2Coloring
    ((strongTwoSeparated_iff_exists_with t2Coloring).2
      ⟨0, t2Coloring_strongTwoSeparatedWith_zero⟩)

def t2Node025 : PairedNode t2Target :=
  ⟨⟨0, 25, by decide⟩, by decide⟩

def t2Node124 : PairedNode t2Target :=
  ⟨⟨1, 24, by decide⟩, by decide⟩

def t2Node223 : PairedNode t2Target :=
  ⟨⟨2, 23, by decide⟩, by decide⟩

def t2Node316 : PairedNode t2Target :=
  ⟨⟨3, 16, by decide⟩, by decide⟩

def t2Node415 : PairedNode t2Target :=
  ⟨⟨4, 15, by decide⟩, by decide⟩

def t2Node514 : PairedNode t2Target :=
  ⟨⟨5, 14, by decide⟩, by decide⟩

def t2Node69 : PairedNode t2Target :=
  ⟨⟨6, 9, by decide⟩, by decide⟩

def t2Node78 : PairedNode t2Target :=
  ⟨⟨7, 8, by decide⟩, by decide⟩

def t2Node1013 : PairedNode t2Target :=
  ⟨⟨10, 13, by decide⟩, by decide⟩

def t2Node1112 : PairedNode t2Target :=
  ⟨⟨11, 12, by decide⟩, by decide⟩

def t2Node1722 : PairedNode t2Target :=
  ⟨⟨17, 22, by decide⟩, by decide⟩

def t2Node1821 : PairedNode t2Target :=
  ⟨⟨18, 21, by decide⟩, by decide⟩

def t2Node1920 : PairedNode t2Target :=
  ⟨⟨19, 20, by decide⟩, by decide⟩

theorem t2Node316_leftLetter :
    leftLetterOfProperColoring t2Coloring t2Coloring_proper t2Node316 = A := by
  rw [leftLetter_grey_at_anchor t2Coloring t2Coloring_proper t2Node316
    (by decide) (some t2Node223) (by decide) (by decide)]
  have hmem : t2Node316 ∈
      orderedGreyChildren t2Coloring (some t2Node223) :=
    (mem_orderedGreyChildren_iff t2Coloring (some t2Node223) t2Node316).2
      ⟨by decide, by decide⟩
  have hcardEq :
      (childrenOfColor t2Coloring (some t2Node223) Color.grey).card = 1 := by
    decide
  have hrankLt := List.idxOf_lt_length_of_mem hmem
  rw [orderedGreyChildren_length, hcardEq] at hrankLt
  have hrank :
      greySiblingRank t2Coloring (some t2Node223) t2Node316 = 0 := by
    change (orderedGreyChildren t2Coloring (some t2Node223)).idxOf
      t2Node316 = 0
    omega
  simp [greyRankLetter, hrank]

theorem t2Node69_leftLetter :
    leftLetterOfProperColoring t2Coloring t2Coloring_proper t2Node69 = A := by
  rw [leftLetter_grey_at_anchor t2Coloring t2Coloring_proper t2Node69
    (by decide) (some t2Node514) (by decide) (by decide)]
  let L := orderedGreyChildren t2Coloring (some t2Node514)
  have hleftMem : t2Node69 ∈ L :=
    (mem_orderedGreyChildren_iff t2Coloring (some t2Node514) t2Node69).2
      ⟨by decide, by decide⟩
  have hrightMem : t2Node1013 ∈ L :=
    (mem_orderedGreyChildren_iff t2Coloring (some t2Node514) t2Node1013).2
      ⟨by decide, by decide⟩
  have hleftRankLt := List.idxOf_lt_length_of_mem hleftMem
  have hrightRankLt := List.idxOf_lt_length_of_mem hrightMem
  have hsorted : L.SortedLT := by
    exact Finset.sortedLT_sort
      (childrenOfColor t2Coloring (some t2Node514) Color.grey)
  have hnodeOrder : t2Node69 < t2Node1013 := by
    decide
  have hrankOrder :
      greySiblingRank t2Coloring (some t2Node514) t2Node69 <
        greySiblingRank t2Coloring (some t2Node514) t2Node1013 := by
    change L.idxOf t2Node69 < L.idxOf t2Node1013
    rw [← hsorted.getElem_lt_getElem_iff
      (hi := hleftRankLt) (hj := hrightRankLt)]
    simpa using hnodeOrder
  have hleftLtTwo := greySiblingRank_lt_two t2Coloring
    t2Coloring_proper (some t2Node514) t2Node69 (by decide) (by decide)
  have hrightLtTwo := greySiblingRank_lt_two t2Coloring
    t2Coloring_proper (some t2Node514) t2Node1013 (by decide) (by decide)
  have hleftZero :
      greySiblingRank t2Coloring (some t2Node514) t2Node69 = 0 := by
    omega
  simp [greyRankLetter, hleftZero]

theorem t2Node1013_leftLetter :
    leftLetterOfProperColoring t2Coloring t2Coloring_proper t2Node1013 = U := by
  rw [leftLetter_grey_at_anchor t2Coloring t2Coloring_proper t2Node1013
    (by decide) (some t2Node514) (by decide) (by decide)]
  let L := orderedGreyChildren t2Coloring (some t2Node514)
  have hleftMem : t2Node69 ∈ L :=
    (mem_orderedGreyChildren_iff t2Coloring (some t2Node514) t2Node69).2
      ⟨by decide, by decide⟩
  have hrightMem : t2Node1013 ∈ L :=
    (mem_orderedGreyChildren_iff t2Coloring (some t2Node514) t2Node1013).2
      ⟨by decide, by decide⟩
  have hleftRankLt := List.idxOf_lt_length_of_mem hleftMem
  have hrightRankLt := List.idxOf_lt_length_of_mem hrightMem
  have hsorted : L.SortedLT := by
    exact Finset.sortedLT_sort
      (childrenOfColor t2Coloring (some t2Node514) Color.grey)
  have hnodeOrder : t2Node69 < t2Node1013 := by
    decide
  have hrankOrder :
      greySiblingRank t2Coloring (some t2Node514) t2Node69 <
        greySiblingRank t2Coloring (some t2Node514) t2Node1013 := by
    change L.idxOf t2Node69 < L.idxOf t2Node1013
    rw [← hsorted.getElem_lt_getElem_iff
      (hi := hleftRankLt) (hj := hrightRankLt)]
    simpa using hnodeOrder
  have hrightLtTwo := greySiblingRank_lt_two t2Coloring
    t2Coloring_proper (some t2Node514) t2Node1013 (by decide) (by decide)
  have hrightOne :
      greySiblingRank t2Coloring (some t2Node514) t2Node1013 = 1 := by
    omega
  simp [greyRankLetter, hrightOne]

noncomputable def t2AssignedSequence : Sequence 26 :=
  sequenceOfProperColoring t2Coloring t2Coloring_proper

theorem t2AssignedSequence_eq_w2 : t2AssignedSequence = w2 := by
  funext i
  fin_cases i
  · change t2AssignedSequence t2Node025.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node025 (by decide))
  · change t2AssignedSequence t2Node124.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node124 (by decide))
  · change t2AssignedSequence t2Node223.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node223 (by decide))
  · change t2AssignedSequence t2Node316.val.left = A
    simpa [t2AssignedSequence] using t2Node316_leftLetter
  · change t2AssignedSequence t2Node415.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node415 (by decide))
  · change t2AssignedSequence t2Node514.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node514 (by decide))
  · change t2AssignedSequence t2Node69.val.left = A
    simpa [t2AssignedSequence] using t2Node69_leftLetter
  · change t2AssignedSequence t2Node78.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node78 (by decide))
  · change t2AssignedSequence t2Node78.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node78 (by decide))
  · change t2AssignedSequence t2Node69.val.right = U
    simp [t2AssignedSequence, t2Node69_leftLetter]
  · change t2AssignedSequence t2Node1013.val.left = U
    simpa [t2AssignedSequence] using t2Node1013_leftLetter
  · change t2AssignedSequence t2Node1112.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node1112 (by decide))
  · change t2AssignedSequence t2Node1112.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node1112 (by decide))
  · change t2AssignedSequence t2Node1013.val.right = A
    simp [t2AssignedSequence, t2Node1013_leftLetter]
  · change t2AssignedSequence t2Node514.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node514 (by decide))
  · change t2AssignedSequence t2Node415.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node415 (by decide))
  · change t2AssignedSequence t2Node316.val.right = U
    simp [t2AssignedSequence, t2Node316_leftLetter]
  · change t2AssignedSequence t2Node1722.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node1722 (by decide))
  · change t2AssignedSequence t2Node1821.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node1821 (by decide))
  · change t2AssignedSequence t2Node1920.val.left = G
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_left t2Coloring t2Coloring_proper
        t2Node1920 (by decide))
  · change t2AssignedSequence t2Node1920.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node1920 (by decide))
  · change t2AssignedSequence t2Node1821.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node1821 (by decide))
  · change t2AssignedSequence t2Node1722.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node1722 (by decide))
  · change t2AssignedSequence t2Node223.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node223 (by decide))
  · change t2AssignedSequence t2Node124.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node124 (by decide))
  · change t2AssignedSequence t2Node025.val.right = C
    simpa [t2AssignedSequence] using
      (sequenceOfProperColoring_black_right t2Coloring t2Coloring_proper
        t2Node025 (by decide))

theorem w2_uniqueDesigns_t2Target : UniqueDesigns w2 t2Target := by
  rw [← t2AssignedSequence_eq_w2]
  exact uniqueDesigns_sequenceOfProperSeparatedColoring
    t2Coloring t2Coloring_proper t2Coloring_separated

/-! ## Negative class controls -/

/-- The three-short target `((.))((.))((.))`. -/
abbrev threeShortTarget : SecondaryStructure 15 := threeShortControl

theorem threeShortTarget_shortHelixCount :
    shortHelixCount threeShortTarget = 3 :=
  threeShortControl_shortHelixCount

theorem threeShortTarget_not_inTargetClassKLeTwo :
    ¬ InTargetClassKLeTwo threeShortTarget :=
  threeShortControl_not_inTargetClassKLeTwo

set_option maxHeartbeats 2000000 in
-- Exhaustively reduce the 729 colorings of the six-node target.
/-- The finite coloring domain has six paired nodes, hence only `3^6 = 729`
colorings.  Ordinary kernel reduction checks that none is both proper and
modulo-2 separated. -/
theorem threeShortTarget_no_proper_modTwoSeparated :
    ¬ ∃ χ : Coloring threeShortTarget,
      ProperColoring χ ∧ StrongTwoSeparated χ := by
  decide

/-- A target consisting of one maximal helix of length one. -/
abbrev lengthOneHelixTarget : SecondaryStructure 2 := lengthOneControl

theorem lengthOneHelixTarget_not_inTargetClassKLeTwo :
    ¬ InTargetClassKLeTwo lengthOneHelixTarget :=
  lengthOneControl_not_inTargetClassKLeTwo

/-! ## Four-position tie control -/

/-- The literal sequence `AUAU`. -/
abbrev auau : Sequence 4 := Examples.auau

/-- `AUAU` does not uniquely design the nested target `(())`; the disjoint
target `()()` is a tied compatible competitor. -/
theorem auau_not_uniqueDesigns_nested :
    ¬ UniqueDesigns auau Examples.nestedTarget :=
  Examples.auau_not_unique_design

end RNA.PublicationExamples
