module

public import RNA.Saturable
public import RNA.StructureOperations

@[expose] public section

set_option autoImplicit false

/-!
# Atomic saturable words and atomic designs

Atomicity is a property of a variable-length word.  Design uniqueness remains
quantified over every saturated `SecondaryStructure` on the word's complete
public sequence.
-/

namespace RNA

/-- A nonempty saturable word with no nonempty proper saturable prefix. -/
def Atomic (z : Word) : Prop :=
  z ≠ [] ∧ Saturable z ∧
    ∀ k : Nat, 1 ≤ k → k < z.length → ¬ Saturable (z.take k)

/-- A structure contains the positional pair joining the first and last
backbone positions.  The arithmetic formulation is meaningful at every
length and avoids manufacturing endpoints when the backbone is empty. -/
def HasOuterPair {n : Nat} (S : SecondaryStructure n) : Prop :=
  ∃ a ∈ S.arcs, a.left.val = 0 ∧ a.right.val + 1 = n

/-- An atomic design has an atomic word and one specified saturated compatible
target which is unique among all compatible noncrossing perfect matchings.
Noncrossingness is already a field of `SecondaryStructure`. -/
def AtomicDesign (z : Word) (R : SecondaryStructure z.length) : Prop :=
  Atomic z ∧
    SaturatedStructure R ∧
    StructureCompatible z.toSequence R ∧
    ∀ P : SecondaryStructure z.length,
      SaturatedStructure P →
      StructureCompatible z.toSequence P →
      P = R

/-! ## Equal-word transport -/

/-- Transport a structure across an equality of its underlying words.  This
changes only the dependent length index; no position or arc is altered. -/
def castStructureToEqualWord {x y : Word} (h : x = y)
    (S : SecondaryStructure x.length) : SecondaryStructure y.length := by
  subst y
  exact S

/-- Equal-word transport is faithful: equality after the dependent length
cast reflects equality of the original structures. -/
theorem castStructureToEqualWord_injective {x y : Word} (h : x = y) :
    Function.Injective (castStructureToEqualWord h) := by
  subst y
  intro S T hST
  exact hST

@[simp]
theorem saturated_castStructureToEqualWord {x y : Word} (h : x = y)
    (S : SecondaryStructure x.length) :
    SaturatedStructure (castStructureToEqualWord h S) ↔
      SaturatedStructure S := by
  subst y
  rfl

@[simp]
theorem compatible_castStructureToEqualWord {x y : Word} (h : x = y)
    (S : SecondaryStructure x.length) :
    StructureCompatible y.toSequence (castStructureToEqualWord h S) ↔
      StructureCompatible x.toSequence S := by
  subst y
  rfl

@[simp]
theorem hasOuterPair_castStructureToEqualWord {x y : Word} (h : x = y)
    (S : SecondaryStructure x.length) :
    HasOuterPair (castStructureToEqualWord h S) ↔ HasOuterPair S := by
  subst y
  rfl

/-- Atomic designs transport faithfully across a proved equality of complete
words.  The target structure is changed only by the corresponding dependent
length cast. -/
theorem atomicDesign_castStructureToEqualWord {x y : Word} (h : x = y)
    (S : SecondaryStructure x.length) (hDesign : AtomicDesign x S) :
    AtomicDesign y (castStructureToEqualWord h S) := by
  subst y
  exact hDesign

private theorem appendWords_not_hasOuterPair
    (x y : Word) (hx : x ≠ []) (hy : y ≠ [])
    (S : SecondaryStructure x.length) (T : SecondaryStructure y.length) :
    ¬ HasOuterPair (SecondaryStructure.appendWords x y S T) := by
  rintro ⟨a, ha, haleft, haright⟩
  unfold SecondaryStructure.appendWords at ha
  obtain ⟨a₀, ha₀, haMap⟩ :=
    (SecondaryStructure.mem_mapOrderEmbedding_iff
      (Fin.castOrderIso (by simp)).toOrderEmbedding
      (SecondaryStructure.appendConsecutive S T) a).1 ha
  rcases (SecondaryStructure.mem_appendConsecutive_iff S T a₀).1 ha₀ with
    hLeft | hRight
  · obtain ⟨b, hb, hbMap⟩ := hLeft
    have hrightEq : a.right.val = b.right.val := by
      have h₁ := congrArg Arc.right haMap
      have h₂ := congrArg Arc.right hbMap
      have h₃ := congrArg Fin.val h₁
      have h₄ := congrArg Fin.val h₂
      change a₀.right.val = a.right.val at h₃
      change b.right.val = a₀.right.val at h₄
      omega
    have hyPos : 0 < y.length := (List.length_pos_iff).2 hy
    have hbRight := b.right.isLt
    simp only [List.length_append] at haright
    omega
  · obtain ⟨b, hb, hbMap⟩ := hRight
    have hleftEq : a.left.val = x.length + b.left.val := by
      have h₁ := congrArg Arc.left haMap
      have h₂ := congrArg Arc.left hbMap
      have h₃ := congrArg Fin.val h₁
      have h₄ := congrArg Fin.val h₂
      change a₀.left.val = a.left.val at h₃
      change x.length + b.left.val = a₀.left.val at h₄
      omega
    have hxPos : 0 < x.length := (List.length_pos_iff).2 hx
    omega

/-! ## Atomic endpoint characterization (Lemma 16) -/

/-- A nonempty saturable word is atomic exactly when every compatible
noncrossing perfect matching contains its positional outer pair. -/
theorem atomic_iff_every_saturated_hasOuterPair
    (z : Word) (hzNonempty : z ≠ []) (hzSaturable : Saturable z) :
    Atomic z ↔
      ∀ P : SecondaryStructure z.length,
        SaturatedStructure P →
        StructureCompatible z.toSequence P →
        HasOuterPair P := by
  constructor
  · rintro ⟨_, _, hAtomic⟩ P hSat hCompat
    have hn : 0 < z.length := (List.length_pos_iff).2 hzNonempty
    let zero : Fin z.length := ⟨0, hn⟩
    obtain ⟨q, hq, hqInc⟩ := hSat zero
    have hqLeft : q.left.val = 0 := by
      rcases hqInc with hleft | hright
      · exact congrArg Fin.val hleft.symm
      · have hzeroRight : q.right.val = 0 := congrArg Fin.val hright.symm
        have := q.ordered
        omega
    by_cases hlast : q.right.val + 1 = z.length
    · exact ⟨q, hq, hqLeft, hlast⟩
    · have hkPos : 1 ≤ q.right.val + 1 := by omega
      have hkLt : q.right.val + 1 < z.length := by
        have := q.right.isLt
        omega
      have hPrefix : Saturable (z.take (q.right.val + 1)) :=
        prefix_saturable_of_arc_from_zero z P hCompat hSat q hq hqLeft
      exact False.elim (hAtomic (q.right.val + 1) hkPos hkLt hPrefix)
  · intro hOuter
    refine ⟨hzNonempty, hzSaturable, ?_⟩
    intro k hkPos hkProper hkPrefix
    let x := z.take k
    let y := z.drop k
    have hxNonempty : x ≠ [] := by
      intro hx
      have hxLen : x.length = 0 := by simp [hx]
      have : x.length = k := by simp [x, List.length_take, Nat.min_eq_left hkProper.le]
      omega
    have hyNonempty : y ≠ [] := by
      intro hy
      have hyLen : y.length = 0 := by simp [hy]
      have : y.length = z.length - k := by simp [y]
      omega
    have hySat : Saturable y := by
      have hconcat : Saturable (x ++ y) := by
        simpa [x, y] using hzSaturable
      exact suffix_saturable_of_concat_saturable_of_prefix_saturable
        x y hconcat hkPrefix
    obtain ⟨S, hSCompat, hSSat⟩ := hkPrefix
    obtain ⟨T, hTCompat, hTSat⟩ := hySat
    let P₀ := SecondaryStructure.appendWords x y S T
    have hword : x ++ y = z := by simp [x, y]
    let P := castStructureToEqualWord hword P₀
    have hPSat : SaturatedStructure P := by
      rw [saturated_castStructureToEqualWord]
      exact (SecondaryStructure.saturated_appendWords_iff x y S T).2
        ⟨hSSat, hTSat⟩
    have hPCompat : StructureCompatible z.toSequence P := by
      rw [compatible_castStructureToEqualWord]
      exact (SecondaryStructure.structureCompatible_appendWords_iff
        x y S T).2 ⟨hSCompat, hTCompat⟩
    have hHas := hOuter P hPSat hPCompat
    rw [hasOuterPair_castStructureToEqualWord] at hHas
    exact (appendWords_not_hasOuterPair x y hxNonempty hyNonempty S T) hHas

/-- A dependent package used to concatenate arbitrarily many atomic designs. -/
structure AtomicDesignBlock where
  word : Word
  target : SecondaryStructure word.length
  design : AtomicDesign word target

namespace AtomicDesignBlock

/-- Every packaged atomic-design word is nonempty. -/
theorem word_ne_nil (B : AtomicDesignBlock) : B.word ≠ [] :=
  B.design.1.1

/-- First nucleotide of a packaged atomic design. -/
def firstLetter (B : AtomicDesignBlock) : Nucleotide :=
  B.word.head B.word_ne_nil

/-- Last nucleotide of a packaged nonempty word. -/
def lastLetter (B : AtomicDesignBlock) : Nucleotide :=
  B.word.get ⟨B.word.length - 1, by
    have := (List.length_pos_iff).2 B.word_ne_nil
    omega⟩

/-- Atomicity forces the first and last letters of every packaged design to
be complementary. -/
theorem compatible_first_last (B : AtomicDesignBlock) :
    Compatible B.firstLetter B.lastLetter := by
  have hOuter :=
    (atomic_iff_every_saturated_hasOuterPair B.word B.word_ne_nil
      B.design.1.2.1).1 B.design.1 B.target B.design.2.1 B.design.2.2.1
  obtain ⟨q, hq, hqLeft, hqRight⟩ := hOuter
  have hCompat := B.design.2.2.1 q hq
  have hleft : q.left = ⟨0, (List.length_pos_iff).2 B.word_ne_nil⟩ :=
    Fin.ext hqLeft
  have hright : q.right =
      ⟨B.word.length - 1, by
        have := (List.length_pos_iff).2 B.word_ne_nil
        omega⟩ := by
    apply Fin.ext
    change q.right.val = B.word.length - 1
    omega
  rw [hleft, hright] at hCompat
  cases hword : B.word with
  | nil => exact False.elim (B.word_ne_nil hword)
  | cons c cs =>
      simpa [firstLetter, lastLetter, hword, Word.toSequence,
        List.get_eq_getElem] using hCompat

/-- The block-first nucleotides are pairwise distinct in list order. -/
def FirstLettersPairwiseDistinct (blocks : List AtomicDesignBlock) : Prop :=
  (blocks.map firstLetter).Pairwise (· ≠ ·)

/-- No block begins with the specified nucleotide. -/
def FirstLettersAvoid (blocks : List AtomicDesignBlock)
    (b : Nucleotide) : Prop :=
  ∀ B ∈ blocks, firstLetter B ≠ b

/-- Concatenation of all words in a list of packaged blocks. -/
def concatWord (blocks : List AtomicDesignBlock) : Word :=
  (blocks.map word).flatten

/-- Concatenate the packaged targets on the same consecutive block
decomposition as `concatWord`. -/
def concatTarget : (blocks : List AtomicDesignBlock) →
    SecondaryStructure (concatWord blocks).length
  | [] => SecondaryStructure.empty 0
  | B :: blocks =>
      SecondaryStructure.appendWords B.word (concatWord blocks)
        B.target (concatTarget blocks)

@[simp]
theorem concatWord_nil : concatWord [] = [] := rfl

@[simp]
theorem concatWord_cons (B : AtomicDesignBlock)
    (blocks : List AtomicDesignBlock) :
    concatWord (B :: blocks) = B.word ++ concatWord blocks := by
  rfl

@[simp]
theorem concatTarget_nil :
    concatTarget [] = SecondaryStructure.empty 0 := rfl

@[simp]
theorem concatTarget_cons (B : AtomicDesignBlock)
    (blocks : List AtomicDesignBlock) :
    concatTarget (B :: blocks) =
      SecondaryStructure.appendWords B.word (concatWord blocks)
        B.target (concatTarget blocks) := rfl

/-- The displayed concatenation target is saturated. -/
theorem saturated_concatTarget (blocks : List AtomicDesignBlock) :
    SaturatedStructure (concatTarget blocks) := by
  induction blocks with
  | nil =>
      intro i
      exact Fin.elim0 i
  | cons B blocks ih =>
      exact (SecondaryStructure.saturated_appendWords_iff
        B.word (concatWord blocks) B.target (concatTarget blocks)).2
          ⟨B.design.2.1, ih⟩

/-- The displayed concatenation target is compatible with the concatenated
complete word. -/
theorem compatible_concatTarget (blocks : List AtomicDesignBlock) :
    StructureCompatible (concatWord blocks).toSequence
      (concatTarget blocks) := by
  induction blocks with
  | nil =>
      intro a ha
      exact False.elim ((Finset.notMem_empty a) ha)
  | cons B blocks ih =>
      exact (SecondaryStructure.structureCompatible_appendWords_iff
        B.word (concatWord blocks) B.target (concatTarget blocks)).2
          ⟨B.design.2.2.1, ih⟩

/-! ## Block-prefix scan used by concatenation uniqueness -/

private theorem firstLetter_eq_of_common_complement
    {x y t : Nucleotide} (hx : Compatible x t) (hy : Compatible y t) :
    x = y := by
  rw [Compatible] at hx hy
  have hcomp : x.comp = y.comp := hx.symm.trans hy
  calc
    x = x.comp.comp := (Nucleotide.comp_comp x).symm
    _ = y.comp.comp := congrArg Nucleotide.comp hcomp
    _ = y := Nucleotide.comp_comp y

/-- A saturable prefix of a concatenation of atomic blocks, whose final
letter complements an avoided anchor, cannot exist. -/
private theorem no_saturable_prefix_ending_in_avoided_complement
    (anchor : Nucleotide) (blocks : List AtomicDesignBlock)
    (hAvoid : FirstLettersAvoid blocks anchor)
    (k : Nat) (hkPos : 1 ≤ k) (hkLe : k ≤ (concatWord blocks).length)
        (hSat : Saturable ((concatWord blocks).take k))
    (hEnd : Compatible anchor
      ((concatWord blocks).get ⟨k - 1, by omega⟩)) : False := by
  induction blocks generalizing k with
  | nil =>
      simp [concatWord] at hkLe
      omega
  | cons C blocks ih =>
      have hCPos : 0 < C.word.length :=
        (List.length_pos_iff).2 C.word_ne_nil
      by_cases hkC : k ≤ C.word.length
      · have htake : (concatWord (C :: blocks)).take k = C.word.take k := by
          simp only [concatWord_cons, List.take_append]
          rw [Nat.sub_eq_zero_of_le hkC,
            List.take_zero, List.append_nil]
        have hSatC : Saturable (C.word.take k) := by
          simpa only [htake] using hSat
        have hkEq : k = C.word.length := by
          by_contra hne
          have hkLt : k < C.word.length := lt_of_le_of_ne hkC hne
          exact C.design.1.2.2 k hkPos hkLt hSatC
        subst k
        have hEndLast :
            (concatWord (C :: blocks)).get
                ⟨C.word.length - 1, by
                  simp only [concatWord_cons, List.length_append]
                  omega⟩ = C.lastLetter := by
          simp only [concatWord_cons, lastLetter, List.get_eq_getElem]
          rw [List.getElem_append_left]
        have hAnchor : Compatible anchor C.lastLetter := by
          simpa only [hEndLast] using hEnd
        have hEq : anchor = C.firstLetter :=
          firstLetter_eq_of_common_complement hAnchor C.compatible_first_last
        exact (hAvoid C (by simp)) hEq.symm
      · have hkGt : C.word.length < k := lt_of_not_ge hkC
        let r := k - C.word.length
        have hrPos : 1 ≤ r := by dsimp [r]; omega
        have hrLe : r ≤ (concatWord blocks).length := by
          simp only [concatWord_cons, List.length_append] at hkLe
          dsimp [r]
          omega
        have htake : (concatWord (C :: blocks)).take k =
            C.word ++ (concatWord blocks).take r := by
          simp only [concatWord_cons, List.take_append]
          rw [List.take_of_length_le hkGt.le]
        have hConcatSat :
            Saturable (C.word ++ (concatWord blocks).take r) := by
          simpa only [htake] using hSat
        have hRestSat : Saturable ((concatWord blocks).take r) :=
          suffix_saturable_of_concat_saturable_of_prefix_saturable
            C.word ((concatWord blocks).take r) hConcatSat C.design.1.2.1
        have hEndRest : Compatible anchor
            ((concatWord blocks).get ⟨r - 1, by omega⟩) := by
          have hIndex : k - 1 = C.word.length + (r - 1) := by
            dsimp [r]
            omega
          have hGet :
              (concatWord (C :: blocks)).get
                  ⟨k - 1, by omega⟩ =
                (concatWord blocks).get ⟨r - 1, by omega⟩ := by
            simp only [concatWord_cons, List.get_eq_getElem]
            rw [List.getElem_append_right (by omega)]
            apply getElem_congr rfl
            omega
          simpa only [hGet] using hEnd
        exact ih (fun B hB => hAvoid B (by simp [hB])) r hrPos hrLe
          hRestSat hEndRest

private theorem concatWord_first_value
    (B : AtomicDesignBlock) (blocks : List AtomicDesignBlock) :
    (concatWord (B :: blocks)).toSequence
        ⟨0, by
          simp only [concatWord_cons, List.length_append]
          have := (List.length_pos_iff).2 B.word_ne_nil
          omega⟩ =
      B.firstLetter := by
  simp only [concatWord_cons, Word.toSequence, List.get_eq_getElem]
  rw [List.getElem_append_left ((List.length_pos_iff).2 B.word_ne_nil)]
  exact (List.head_eq_getElem B.word_ne_nil).symm

/-- In any compatible perfect matching of a concatenation with distinct block
first letters, the first position pairs to the end of the first block. -/
private theorem first_arc_closes_first_block
    (B : AtomicDesignBlock) (blocks : List AtomicDesignBlock)
    (hDistinct : FirstLettersPairwiseDistinct (B :: blocks))
    (P : SecondaryStructure (concatWord (B :: blocks)).length)
    (hSat : SaturatedStructure P)
    (hCompat : StructureCompatible (concatWord (B :: blocks)).toSequence P)
    (q : Arc (concatWord (B :: blocks)).length) (hq : q ∈ P.arcs)
    (hqLeft : q.left.val = 0) :
    q.right.val + 1 = B.word.length := by
  let k := q.right.val + 1
  have hkPos : 1 ≤ k := by dsimp [k]; omega
  have hkLe : k ≤ (concatWord (B :: blocks)).length := by
    dsimp [k]
    exact q.right.isLt
  have hPrefix : Saturable ((concatWord (B :: blocks)).take k) :=
    prefix_saturable_of_arc_from_zero
      (concatWord (B :: blocks)) P hCompat hSat q hq hqLeft
  have hqLeftFin : q.left =
      ⟨0, by
        simp only [concatWord_cons, List.length_append]
        have := (List.length_pos_iff).2 B.word_ne_nil
        omega⟩ :=
    Fin.ext hqLeft
  have hqRightFin : q.right = ⟨k - 1, by omega⟩ := by
    apply Fin.ext
    dsimp [k]
  have hEnd : Compatible B.firstLetter
      ((concatWord (B :: blocks)).get ⟨k - 1, by omega⟩) := by
    have h := hCompat q hq
    rw [hqLeftFin, hqRightFin] at h
    rw [concatWord_first_value B blocks] at h
    exact h
  by_cases hkFirst : k ≤ B.word.length
  · have htake : (concatWord (B :: blocks)).take k = B.word.take k := by
      simp only [concatWord_cons, List.take_append]
      rw [Nat.sub_eq_zero_of_le hkFirst, List.take_zero, List.append_nil]
    have hSatFirst : Saturable (B.word.take k) := by
      simpa only [htake] using hPrefix
    have hkEq : k = B.word.length := by
      by_contra hne
      have hkLt : k < B.word.length := lt_of_le_of_ne hkFirst hne
      exact B.design.1.2.2 k hkPos hkLt hSatFirst
    exact hkEq
  · have hkGt : B.word.length < k := lt_of_not_ge hkFirst
    let r := k - B.word.length
    have hrPos : 1 ≤ r := by dsimp [r]; omega
    have hrLe : r ≤ (concatWord blocks).length := by
      simp only [concatWord_cons, List.length_append] at hkLe
      dsimp [r]
      omega
    have htake : (concatWord (B :: blocks)).take k =
        B.word ++ (concatWord blocks).take r := by
      simp only [concatWord_cons, List.take_append]
      rw [List.take_of_length_le hkGt.le]
    have hConcatSat :
        Saturable (B.word ++ (concatWord blocks).take r) := by
      simpa only [htake] using hPrefix
    have hRestSat : Saturable ((concatWord blocks).take r) :=
      suffix_saturable_of_concat_saturable_of_prefix_saturable
        B.word ((concatWord blocks).take r) hConcatSat B.design.1.2.1
    have hEndRest : Compatible B.firstLetter
        ((concatWord blocks).get ⟨r - 1, by omega⟩) := by
      have hGet :
          (concatWord (B :: blocks)).get ⟨k - 1, by omega⟩ =
            (concatWord blocks).get ⟨r - 1, by omega⟩ := by
        simp only [concatWord_cons, List.get_eq_getElem]
        rw [List.getElem_append_right (by omega)]
        apply getElem_congr rfl
        dsimp [r]
        omega
      simpa only [hGet] using hEnd
    have hAvoid : FirstLettersAvoid blocks B.firstLetter := by
      intro C hC
      change (B.firstLetter :: (blocks.map firstLetter)).Pairwise (fun x y => x ≠ y)
        at hDistinct
      exact Ne.symm ((List.pairwise_cons.mp hDistinct).1 C.firstLetter
        (List.mem_map_of_mem hC))
    exact False.elim
      (no_saturable_prefix_ending_in_avoided_complement
        B.firstLetter blocks hAvoid r hrPos hrLe hRestSat hEndRest)

/-! ## Concatenating atomic designs (Lemma 17) -/

private theorem structure_eq_empty_zero
    (S : SecondaryStructure 0) :
    S = SecondaryStructure.empty 0 := by
  apply SecondaryStructure.ext
  ext q
  exact Fin.elim0 q.left

/-- A nonempty concatenation of atomic designs whose first nucleotides are
pairwise distinct has the displayed concatenated target as its unique
compatible noncrossing perfect matching. -/
theorem concatTarget_unique
    (blocks : List AtomicDesignBlock) (hNonempty : blocks ≠ [])
    (hDistinct : FirstLettersPairwiseDistinct blocks)
    (P : SecondaryStructure (concatWord blocks).length)
    (hSat : SaturatedStructure P)
    (hCompat : StructureCompatible (concatWord blocks).toSequence P) :
    P = concatTarget blocks := by
  induction blocks with
  | nil => exact False.elim (hNonempty rfl)
  | cons B blocks ih =>
      have hLenPos : 0 < (concatWord (B :: blocks)).length := by
        simp only [concatWord_cons, List.length_append]
        exact Nat.add_pos_left ((List.length_pos_iff).2 B.word_ne_nil) _
      let zero : Fin (concatWord (B :: blocks)).length := ⟨0, hLenPos⟩
      obtain ⟨q, hq, hqInc⟩ := hSat zero
      have hqLeft : q.left.val = 0 := by
        rcases hqInc with hleft | hright
        · exact congrArg Fin.val hleft.symm
        · have hzeroRight : q.right.val = 0 :=
            congrArg Fin.val hright.symm
          have hordered := q.ordered
          omega
      have hqRight : q.right.val + 1 = B.word.length :=
        first_arc_closes_first_block B blocks hDistinct P hSat hCompat q hq
          hqLeft
      obtain ⟨PL, PR, hPLSat, hPRSat, hSplit⟩ :=
        SecondaryStructure.splitAtOuterPrefix B.word (concatWord blocks)
          B.word_ne_nil P q hq hqLeft hqRight hSat
      have hAppendCompat :
          StructureCompatible (B.word ++ concatWord blocks).toSequence
            (SecondaryStructure.appendWords B.word (concatWord blocks) PL PR) := by
        rw [← hSplit]
        exact hCompat
      have hPartsCompat :=
        (SecondaryStructure.structureCompatible_appendWords_iff
          B.word (concatWord blocks) PL PR).1 hAppendCompat
      have hPLEq : PL = B.target :=
        B.design.2.2.2 PL hPLSat hPartsCompat.1
      have hTailDistinct : FirstLettersPairwiseDistinct blocks := by
        change (B.firstLetter :: blocks.map firstLetter).Pairwise
          (fun x y => x ≠ y) at hDistinct
        exact (List.pairwise_cons.mp hDistinct).2
      have hPREq : PR = concatTarget blocks := by
        by_cases hEmpty : blocks = []
        · subst blocks
          exact structure_eq_empty_zero PR
        · exact ih hEmpty hTailDistinct PR hPRSat hPartsCompat.2
      rw [hSplit, hPLEq, hPREq]
      rfl

/-- Audit-friendly name for canonical Lemma 17. -/
theorem concat_atomicDesigns
    (blocks : List AtomicDesignBlock) (hNonempty : blocks ≠ [])
    (hDistinct : FirstLettersPairwiseDistinct blocks)
    (P : SecondaryStructure (concatWord blocks).length)
    (hSat : SaturatedStructure P)
    (hCompat : StructureCompatible (concatWord blocks).toSequence P) :
    P = concatTarget blocks :=
  concatTarget_unique blocks hNonempty hDistinct P hSat hCompat

/-! ## Helpers for wrapping atomic blocks -/

/-- Removing complementary outer letters from a saturable word leaves a
saturable middle.  This is the free-group cancellation calculation used in
Lemma 18. -/
theorem middle_saturable_of_wrap_saturable
    (a b : Nucleotide) (z : Word) (hab : Compatible a b)
    (hWrap : Saturable (Word.wrap a b z)) : Saturable z := by
  have hPairRed : ReducesToEmpty ([a, b] : Word) := by
    apply Relation.ReflTransGen.single
    exact ⟨[], [], a, b, hab, rfl, rfl⟩
  have hPairProd : encodedProduct [a] * encodedProduct [b] = 1 := by
    rw [← encodedProduct_append]
    exact (reducesToEmpty_iff_encodedProduct_eq_one [a, b]).1 hPairRed
  have hbInv : encodedProduct [b] = (encodedProduct [a])⁻¹ :=
    eq_inv_of_mul_eq_one_right hPairProd
  have hWrapProd :
      encodedProduct [a] * encodedProduct z * encodedProduct [b] = 1 := by
    have h := (saturable_iff_encodedProduct_eq_one (Word.wrap a b z)).1 hWrap
    calc
      encodedProduct [a] * encodedProduct z * encodedProduct [b] =
          encodedProduct ([a] ++ z) * encodedProduct [b] := by
            rw [encodedProduct_append]
      _ = encodedProduct (([a] ++ z) ++ [b]) := by
            exact (encodedProduct_append ([a] ++ z) [b]).symm
      _ = encodedProduct (Word.wrap a b z) := by
            simp [Word.wrap]
      _ = 1 := h
  apply (saturable_iff_encodedProduct_eq_one z).2
  calc
    encodedProduct z =
        (encodedProduct [a])⁻¹ *
          (encodedProduct [a] * encodedProduct z * encodedProduct [b]) *
            encodedProduct [a] := by rw [hbInv]; simp [mul_assoc]
    _ = 1 := by rw [hWrapProd]; simp

/-- If a prefix of concatenated atomic blocks is saturable, then the next
letter cannot be a nucleotide avoided by all block-first letters. -/
private theorem next_letter_ne_of_saturable_prefix
    (b : Nucleotide) (blocks : List AtomicDesignBlock)
    (hAvoid : FirstLettersAvoid blocks b)
    (k : Nat) (hkLt : k < (concatWord blocks).length)
    (hSat : Saturable ((concatWord blocks).take k)) :
    (concatWord blocks).get ⟨k, hkLt⟩ ≠ b := by
  induction blocks generalizing k with
  | nil => simp [concatWord] at hkLt
  | cons C blocks ih =>
      have hCPos : 0 < C.word.length :=
        (List.length_pos_iff).2 C.word_ne_nil
      by_cases hkC : k < C.word.length
      · have htake : (concatWord (C :: blocks)).take k = C.word.take k := by
          simp only [concatWord_cons, List.take_append]
          rw [Nat.sub_eq_zero_of_le hkC.le, List.take_zero, List.append_nil]
        have hSatC : Saturable (C.word.take k) := by
          simpa only [htake] using hSat
        have hkZero : k = 0 := by
          by_contra hkNe
          have hkPos : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hkNe
          exact C.design.1.2.2 k hkPos hkC hSatC
        subst k
        have hFirst :
            (concatWord (C :: blocks)).get ⟨0, by
              simp only [concatWord_cons, List.length_append]
              omega⟩ = C.firstLetter := by
          change (concatWord (C :: blocks)).toSequence _ = C.firstLetter
          exact concatWord_first_value C blocks
        rw [hFirst]
        exact hAvoid C (by simp)
      · have hkGe : C.word.length ≤ k := Nat.le_of_not_gt hkC
        let r := k - C.word.length
        have hrLt : r < (concatWord blocks).length := by
          simp only [concatWord_cons, List.length_append] at hkLt
          dsimp [r]
          omega
        have htake : (concatWord (C :: blocks)).take k =
            C.word ++ (concatWord blocks).take r := by
          simp only [concatWord_cons, List.take_append]
          rw [List.take_of_length_le hkGe]
        have hConcatSat :
            Saturable (C.word ++ (concatWord blocks).take r) := by
          simpa only [htake] using hSat
        have hRestSat : Saturable ((concatWord blocks).take r) :=
          suffix_saturable_of_concat_saturable_of_prefix_saturable
            C.word ((concatWord blocks).take r) hConcatSat C.design.1.2.1
        have hGet :
            (concatWord (C :: blocks)).get ⟨k, hkLt⟩ =
              (concatWord blocks).get ⟨r, hrLt⟩ := by
          simp only [concatWord_cons, List.get_eq_getElem]
          rw [List.getElem_append_right hkGe]
        rw [hGet]
        exact ih (fun B hB => hAvoid B (by simp [hB])) r hrLt hRestSat

/-! ## Wrapping atomic designs (Lemma 18) -/

/-- Under the endpoint-avoidance hypothesis, every compatible perfect
matching of the wrapped concatenation must contain the full outer pair. -/
private theorem wrap_hasOuterPair
    (a b : Nucleotide) (blocks : List AtomicDesignBlock)
    (hab : Compatible a b) (hAvoid : FirstLettersAvoid blocks b)
    (P : SecondaryStructure
      (Word.wrap a b (concatWord blocks)).length)
    (hSat : SaturatedStructure P)
    (hCompat : StructureCompatible
      (Word.wrap a b (concatWord blocks)).toSequence P) :
    HasOuterPair P := by
  let z := concatWord blocks
  change SecondaryStructure (Word.wrap a b z).length at P
  have hLenPos : 0 < (Word.wrap a b z).length := by
    simp only [Word.length_wrap]
    omega
  let zero : Fin (Word.wrap a b z).length := ⟨0, hLenPos⟩
  obtain ⟨q, hq, hqInc⟩ := hSat zero
  have hqRightBound : q.right.val < (Word.wrap a b z).length := by
    simpa only [z] using q.right.isLt
  have hqLeft : q.left.val = 0 := by
    rcases hqInc with hleft | hright
    · exact congrArg Fin.val hleft.symm
    · have hzeroRight : q.right.val = 0 :=
        congrArg Fin.val hright.symm
      have hordered := q.ordered
      omega
  by_cases hOuter : q.right.val + 1 = (Word.wrap a b z).length
  · exact ⟨q, hq, hqLeft, hOuter⟩
  · let k := q.right.val - 1
    have hqRightPos : 1 ≤ q.right.val := by
      have hordered := q.ordered
      omega
    have hRightBeforeLast : q.right.val + 1 < (Word.wrap a b z).length := by
      have hbound := hqRightBound
      omega
    have hkLt : k < z.length := by
      have hlen := Word.length_wrap a b z
      dsimp [k]
      omega
    have hqRightVal : q.right.val = k + 1 := by
      dsimp [k]
      omega
    have hqLeftFin : q.left =
        ⟨0, by simp only [Word.length_wrap]; omega⟩ :=
      Fin.ext hqLeft
    have hqRightFin : q.right =
        ⟨k + 1, by rw [← hqRightVal]; exact hqRightBound⟩ := by
      apply Fin.ext
      exact hqRightVal
    have hEndCompat : Compatible a (z.get ⟨k, hkLt⟩) := by
      have h := hCompat q hq
      rw [hqLeftFin, hqRightFin] at h
      simpa [z, Word.wrap, Word.toSequence, List.get_eq_getElem, hkLt] using h
    have hEndEq : z.get ⟨k, hkLt⟩ = b := by
      rw [Compatible] at hEndCompat hab
      exact hEndCompat.trans hab.symm
    have hPrefix :
        Saturable ((Word.wrap a b z).take (q.right.val + 1)) :=
      prefix_saturable_of_arc_from_zero
        (Word.wrap a b z) P hCompat hSat q hq hqLeft
    have hPrefixWord :
        (Word.wrap a b z).take (q.right.val + 1) =
          Word.wrap a b (z.take k) := by
      calc
        (Word.wrap a b z).take (q.right.val + 1) =
            (a :: z ++ [b]).take (k + 2) := by
              simp only [Word.wrap, hqRightVal]
        _ = a :: (z ++ [b]).take (k + 1) := by
              simpa only [List.cons_append,
                show k + 2 = (k + 1) + 1 by omega] using
                (List.take_succ_cons (a := a) (as := z ++ [b]) (i := k + 1))
        _ = a :: z.take (k + 1) := by
              rw [List.take_append_of_le_length]
              omega
        _ = a :: (z.take k ++ [z.get ⟨k, hkLt⟩]) := by
              rw [List.get_eq_getElem, List.take_concat_get' z k hkLt]
        _ = Word.wrap a b (z.take k) := by
              rw [hEndEq]
              rfl
    have hWrappedPrefix : Saturable (Word.wrap a b (z.take k)) := by
      rw [← hPrefixWord]
      exact hPrefix
    have hMiddle : Saturable (z.take k) :=
      middle_saturable_of_wrap_saturable a b (z.take k) hab hWrappedPrefix
    have hNe := next_letter_ne_of_saturable_prefix b blocks hAvoid k hkLt hMiddle
    exact False.elim (hNe hEndEq)

/-- Wrapping the concatenation of atomic designs in one complementary outer
pair produces an atomic design, provided block-first letters are pairwise
distinct and avoid the closing nucleotide.  This includes the empty block
list, where the result is the complementary two-letter design. -/
theorem wrap_atomicDesigns
    (a b : Nucleotide) (blocks : List AtomicDesignBlock)
    (hab : Compatible a b)
    (hDistinct : FirstLettersPairwiseDistinct blocks)
    (hAvoid : FirstLettersAvoid blocks b) :
    AtomicDesign (Word.wrap a b (concatWord blocks))
      (SecondaryStructure.wrapWord a b (concatWord blocks)
        (concatTarget blocks)) := by
  let z := concatWord blocks
  let R := SecondaryStructure.wrapWord a b z (concatTarget blocks)
  have hRSat : SaturatedStructure R := by
    exact (SecondaryStructure.saturated_wrapWord_iff
      a b z (concatTarget blocks)).2 (saturated_concatTarget blocks)
  have hRCompat : StructureCompatible (Word.wrap a b z).toSequence R := by
    exact (SecondaryStructure.structureCompatible_wrapWord_iff
      a b z (concatTarget blocks)).2
        ⟨hab, compatible_concatTarget blocks⟩
  have hWordNonempty : Word.wrap a b z ≠ [] := by
    simp [Word.wrap]
  have hWordSaturable : Saturable (Word.wrap a b z) :=
    ⟨R, hRCompat, hRSat⟩
  have hAtomic : Atomic (Word.wrap a b z) :=
    (atomic_iff_every_saturated_hasOuterPair
      (Word.wrap a b z) hWordNonempty hWordSaturable).2 (by
        intro P hPSat hPCompat
        exact wrap_hasOuterPair a b blocks hab hAvoid P hPSat hPCompat)
  refine ⟨hAtomic, hRSat, hRCompat, ?_⟩
  intro P hPSat hPCompat
  have hHasOuter :=
    (atomic_iff_every_saturated_hasOuterPair
      (Word.wrap a b z) hWordNonempty hWordSaturable).1 hAtomic
        P hPSat hPCompat
  obtain ⟨q, hq, hqLeft, hqRight⟩ := hHasOuter
  obtain ⟨Q, hQSat, hSplit⟩ :=
    SecondaryStructure.splitOuterWrap a b z P q hq hqLeft hqRight hPSat
  have hWrapCompat :
      StructureCompatible (Word.wrap a b z).toSequence
        (SecondaryStructure.wrapWord a b z Q) := by
    rw [← hSplit]
    exact hPCompat
  have hQCompat : StructureCompatible z.toSequence Q :=
    ((SecondaryStructure.structureCompatible_wrapWord_iff a b z Q).1
      hWrapCompat).2
  have hQEq : Q = concatTarget blocks := by
    by_cases hEmpty : blocks = []
    · subst blocks
      exact structure_eq_empty_zero Q
    · exact concatTarget_unique blocks hEmpty hDistinct Q hQSat hQCompat
  rw [hSplit, hQEq]

/-- The proper-prefix content of the wrapping theorem, exposed separately for
clients that build atomic interval trees. -/
theorem wrap_atomicDesigns_no_saturable_proper_prefix
    (a b : Nucleotide) (blocks : List AtomicDesignBlock)
    (hab : Compatible a b)
    (hDistinct : FirstLettersPairwiseDistinct blocks)
    (hAvoid : FirstLettersAvoid blocks b)
    (k : Nat) (hkPos : 1 ≤ k)
    (hkProper : k < (Word.wrap a b (concatWord blocks)).length) :
    ¬ Saturable ((Word.wrap a b (concatWord blocks)).take k) :=
  (wrap_atomicDesigns a b blocks hab hDistinct hAvoid).1.2.2
    k hkPos hkProper

end AtomicDesignBlock

end RNA
