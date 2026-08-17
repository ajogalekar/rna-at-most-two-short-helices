module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Data.Finset.Max
public import RNA.Word
public import RNA.StructureTransport
import RNA.PositionRole

@[expose] public section

set_option autoImplicit false

/-!
# Saturable RNA words and adjacent complementary cancellation

This file connects the public matching model on `Fin n` with finite list words.
A saturated structure pairs every backbone position.  A word is saturable when
it admits a compatible saturated secondary structure.  The main result is the
adjacent-cancellation characterization, followed by its free-group normal-form
corollary and the suffix-cancellation theorem used by atomic designs.
-/

namespace RNA

variable {n : Nat}

/-- Every position of `S` is incident to a pair. -/
def SaturatedStructure (S : SecondaryStructure n) : Prop :=
  ∀ i : Fin n, S.positionPaired i

/-- A finite RNA word admits a compatible noncrossing perfect matching. -/
def Saturable (z : Word) : Prop :=
  ∃ S : SecondaryStructure z.length,
    StructureCompatible z.toSequence S ∧ SaturatedStructure S

/-- Delete one adjacent Watson--Crick complementary pair from a word. -/
def DeletesComplementaryPair (x y : Word) : Prop :=
  ∃ (u v : Word) (a b : Nucleotide),
    Compatible a b ∧ x = u ++ a :: b :: v ∧ y = u ++ v

/-- Reflexive-transitive adjacent complementary deletion. -/
abbrev ComplementaryReduction : Word → Word → Prop :=
  Relation.ReflTransGen DeletesComplementaryPair

/-- The word can be reduced to the empty word by adjacent complementary
deletions. -/
def ReducesToEmpty (x : Word) : Prop :=
  ComplementaryReduction x []

/-! ## Signed-generator encoding -/

/-- The two Watson--Crick pair types are the two generators of a free group;
the Boolean records the sign. -/
@[simp]
def nucleotideSignedGenerator : Nucleotide → Fin 2 × Bool
  | Nucleotide.A => (⟨0, by omega⟩, true)
  | Nucleotide.U => (⟨0, by omega⟩, false)
  | Nucleotide.C => (⟨1, by omega⟩, true)
  | Nucleotide.G => (⟨1, by omega⟩, false)

/-- Explicit inverse to `nucleotideSignedGenerator`. -/
@[simp]
def nucleotideOfSignedGenerator : Fin 2 × Bool → Nucleotide
  | (⟨0, _⟩, true) => Nucleotide.A
  | (⟨0, _⟩, false) => Nucleotide.U
  | (⟨1, _⟩, true) => Nucleotide.C
  | (⟨1, _⟩, false) => Nucleotide.G

@[simp]
theorem nucleotideOfSignedGenerator_encode (a : Nucleotide) :
    nucleotideOfSignedGenerator (nucleotideSignedGenerator a) = a := by
  cases a <;> rfl

@[simp]
theorem nucleotideSignedGenerator_decode (p : Fin 2 × Bool) :
    nucleotideSignedGenerator (nucleotideOfSignedGenerator p) = p := by
  rcases p with ⟨⟨i, hi⟩, b⟩
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl <;> cases b <;> rfl

theorem nucleotideSignedGenerator_injective :
    Function.Injective nucleotideSignedGenerator :=
  fun _ _ h => by
    simpa only [nucleotideOfSignedGenerator_encode] using
      congrArg nucleotideOfSignedGenerator h

@[simp]
theorem nucleotideSignedGenerator_comp (a : Nucleotide) :
    nucleotideSignedGenerator a.comp =
      ((nucleotideSignedGenerator a).1, !(nucleotideSignedGenerator a).2) := by
  cases a <;> rfl

@[simp]
theorem nucleotideOfSignedGenerator_not (g : Fin 2) (b : Bool) :
    nucleotideOfSignedGenerator (g, !b) =
      (nucleotideOfSignedGenerator (g, b)).comp := by
  rcases g with ⟨i, hi⟩
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl <;> cases b <;> rfl

/-- The signed-generator list underlying a nucleotide word. -/
def encodedWord (x : Word) : List (Fin 2 × Bool) :=
  x.map nucleotideSignedGenerator

/-- The free-group product encoded by a nucleotide word. -/
def encodedProduct (x : Word) : FreeGroup (Fin 2) :=
  FreeGroup.mk (encodedWord x)

@[simp]
theorem encodedWord_nil : encodedWord [] = [] := rfl

@[simp]
theorem encodedWord_append (x y : Word) :
    encodedWord (x ++ y) = encodedWord x ++ encodedWord y := by
  simp [encodedWord]

@[simp]
theorem decode_encodedWord (x : Word) :
    (encodedWord x).map nucleotideOfSignedGenerator = x := by
  induction x with
  | nil => rfl
  | cons a x ih =>
      change nucleotideOfSignedGenerator (nucleotideSignedGenerator a) ::
          (encodedWord x).map nucleotideOfSignedGenerator = a :: x
      rw [nucleotideOfSignedGenerator_encode, ih]

@[simp]
theorem encodedProduct_nil : encodedProduct [] = 1 := rfl

theorem encodedProduct_append (x y : Word) :
    encodedProduct (x ++ y) = encodedProduct x * encodedProduct y := by
  simp only [encodedProduct, encodedWord_append, FreeGroup.mul_mk]

private theorem freeGroupStep_of_deletes {x y : Word}
    (h : DeletesComplementaryPair x y) :
    FreeGroup.Red.Step (encodedWord x) (encodedWord y) := by
  rcases h with ⟨u, v, a, b, hab, rfl, rfl⟩
  rw [compatible_iff_eq_comp] at hab
  subst b
  simp only [encodedWord, List.map_append, List.map_cons, List.map_nil,
    nucleotideSignedGenerator_comp]
  exact FreeGroup.Red.Step.not

private theorem freeGroupRed_of_reduction {x y : Word}
    (h : ComplementaryReduction x y) :
    FreeGroup.Red (encodedWord x) (encodedWord y) := by
  exact Relation.ReflTransGen.lift encodedWord
    (fun _ _ hstep => freeGroupStep_of_deletes hstep) _ _ h

private theorem deletes_of_freeGroupStep
    {L₁ L₂ : List (Fin 2 × Bool)}
    (h : FreeGroup.Red.Step L₁ L₂) :
    DeletesComplementaryPair
      (L₁.map nucleotideOfSignedGenerator)
      (L₂.map nucleotideOfSignedGenerator) := by
  rcases h with @⟨u, v, g, b⟩
  refine ⟨u.map nucleotideOfSignedGenerator,
    v.map nucleotideOfSignedGenerator,
    nucleotideOfSignedGenerator (g, b),
    nucleotideOfSignedGenerator (g, !b), ?_, ?_, ?_⟩
  · simp only [Compatible, nucleotideOfSignedGenerator_not]
  · simp
  · simp

private theorem reduction_of_freeGroupRed
    {L₁ L₂ : List (Fin 2 × Bool)}
    (h : FreeGroup.Red L₁ L₂) :
    ComplementaryReduction
      (L₁.map nucleotideOfSignedGenerator)
      (L₂.map nucleotideOfSignedGenerator) := by
  exact Relation.ReflTransGen.lift
    (List.map nucleotideOfSignedGenerator)
    (fun _ _ hstep => deletes_of_freeGroupStep hstep) _ _ h

theorem reducesToEmpty_iff_encodedProduct_eq_one (x : Word) :
    ReducesToEmpty x ↔ encodedProduct x = 1 := by
  constructor
  · intro hx
    have hred : FreeGroup.Red (encodedWord x) [] := by
      simpa only [encodedWord_nil] using freeGroupRed_of_reduction hx
    rw [encodedProduct, FreeGroup.one_eq_mk]
    exact (FreeGroup.Red.exact).2 ⟨[], hred, FreeGroup.Red.refl⟩
  · intro hx
    rw [encodedProduct, FreeGroup.one_eq_mk] at hx
    obtain ⟨L, hL, hnil⟩ := (FreeGroup.Red.exact).1 hx
    have hLnil : L = [] := (FreeGroup.Red.nil_iff).1 hnil
    subst L
    have hdecoded := reduction_of_freeGroupRed hL
    simpa only [decode_encodedWord, List.map_nil, ReducesToEmpty] using hdecoded

/-! ## The adjacent skip-two word bridge -/

private def wordSkipTwoOrderEmbedding
    (u v : Word) (a b : Nucleotide) :
    Fin (u ++ v).length ↪o Fin (u ++ a :: b :: v).length :=
  (Fin.castOrderIso (by simp)).toOrderEmbedding |>.trans
    ((Fin.skipTwoOrderEmbedding u.length v.length).trans
      (Fin.castOrderIso (by simp; omega)).toOrderEmbedding)

private theorem wordSkipTwoOrderEmbedding_val
    (u v : Word) (a b : Nucleotide) (i : Fin (u ++ v).length) :
    (wordSkipTwoOrderEmbedding u v a b i).val =
      if i.val < u.length then i.val else i.val + 2 := by
  by_cases hi : i.val < u.length <;>
    simp [wordSkipTwoOrderEmbedding, Fin.skipTwoOrderEmbedding,
      Fin.castOrderIso, hi]

private theorem toSequence_skipTwo
    (u v : Word) (a b : Nucleotide) (i : Fin (u ++ v).length) :
    (u ++ a :: b :: v).toSequence
      (wordSkipTwoOrderEmbedding u v a b i) =
      (u ++ v).toSequence i := by
  by_cases hi : i.val < u.length
  · have hval := wordSkipTwoOrderEmbedding_val u v a b i
    rw [if_pos hi] at hval
    have hi' : (wordSkipTwoOrderEmbedding u v a b i).val < u.length := by omega
    change (u ++ a :: b :: v).get _ = (u ++ v).get _
    calc
      (u ++ a :: b :: v).get (wordSkipTwoOrderEmbedding u v a b i) =
          u[i.val] := by
        rw [List.get_eq_getElem, List.getElem_append_left hi']
        congr
      _ = (u ++ v).get i := by
        rw [List.get_eq_getElem, List.getElem_append_left hi]
  · have hle : u.length ≤ i.val := Nat.le_of_not_gt hi
    have heval := wordSkipTwoOrderEmbedding_val u v a b i
    rw [if_neg hi] at heval
    have hiv : i.val - u.length < v.length := by
      have := i.isLt
      simp only [List.length_append] at this
      omega
    have hleU : u.length ≤
        (wordSkipTwoOrderEmbedding u v a b i).val := by omega
    have htail :
        (wordSkipTwoOrderEmbedding u v a b i).val - u.length <
          (a :: b :: v).length := by simp; omega
    have hleTwo : 2 ≤
        (wordSkipTwoOrderEmbedding u v a b i).val - u.length := by omega
    have hneZero :
        (wordSkipTwoOrderEmbedding u v a b i).val - u.length ≠ 0 := by omega
    have htail' :
        (wordSkipTwoOrderEmbedding u v a b i).val - u.length - 1 <
          (b :: v).length := by simp; omega
    have hneZero' :
        (wordSkipTwoOrderEmbedding u v a b i).val - u.length - 1 ≠ 0 := by omega
    change (u ++ a :: b :: v).get _ = (u ++ v).get _
    calc
      (u ++ a :: b :: v).get (wordSkipTwoOrderEmbedding u v a b i) =
          v[i.val - u.length]'hiv := by
        rw [List.get_eq_getElem, List.getElem_append_right hleU]
        rw [List.getElem_cons htail]
        simp only [dif_neg hneZero]
        rw [List.getElem_cons htail']
        simp only [dif_neg hneZero']
        apply getElem_congr rfl
        omega
      _ = (u ++ v).get i := by
        rw [List.get_eq_getElem, List.getElem_append_right hle]

/-! ## Reinserting an adjacent pair -/

private def insertedAdjacentArc
    (u v : Word) (a b : Nucleotide) : Arc (u ++ a :: b :: v).length where
  left := ⟨u.length, by simp⟩
  right := ⟨u.length + 1, by simp⟩
  ordered := by simp

@[simp]
private theorem insertedAdjacentArc_left_val
    (u v : Word) (a b : Nucleotide) :
    (insertedAdjacentArc u v a b).left.val = u.length := rfl

@[simp]
private theorem insertedAdjacentArc_right_val
    (u v : Word) (a b : Nucleotide) :
    (insertedAdjacentArc u v a b).right.val = u.length + 1 := rfl

private theorem wordSkipTwo_ne_deleted
    (u v : Word) (a b : Nucleotide) (i : Fin (u ++ v).length) :
    wordSkipTwoOrderEmbedding u v a b i ≠
        (insertedAdjacentArc u v a b).left ∧
      wordSkipTwoOrderEmbedding u v a b i ≠
        (insertedAdjacentArc u v a b).right := by
  have hval := wordSkipTwoOrderEmbedding_val u v a b i
  split at hval <;> constructor <;> intro h <;>
    have := congrArg Fin.val h <;> simp at this <;> omega

private theorem insertedAdjacentArc_not_share_mapped
    (u v : Word) (a b : Nucleotide) (c : Arc (u ++ v).length) :
    ¬ (insertedAdjacentArc u v a b).ShareEndpoint
      (c.mapOrderEmbedding (wordSkipTwoOrderEmbedding u v a b)) := by
  rintro ⟨p, hp, hpc⟩
  rcases hp with rfl | rfl
  · rcases hpc with hpc | hpc
    · exact (wordSkipTwo_ne_deleted u v a b c.left).1 hpc.symm
    · exact (wordSkipTwo_ne_deleted u v a b c.right).1 hpc.symm
  · rcases hpc with hpc | hpc
    · exact (wordSkipTwo_ne_deleted u v a b c.left).2 hpc.symm
    · exact (wordSkipTwo_ne_deleted u v a b c.right).2 hpc.symm

private theorem insertedAdjacentArc_not_crosses
    (u v : Word) (a b : Nucleotide)
    (c : Arc (u ++ a :: b :: v).length) :
    ¬ (insertedAdjacentArc u v a b).Crosses c := by
  simp only [Arc.Crosses]
  change
    ¬ ((u.length < c.left.val ∧ c.left.val < u.length + 1 ∧
          u.length + 1 < c.right.val) ∨
        (c.left.val < u.length ∧ u.length < c.right.val ∧
          c.right.val < u.length + 1))
  omega

/-- Reinsert an adjacent pair and shift every old arc across it. -/
private def insertAdjacentStructure
    (u v : Word) (a b : Nucleotide)
    (S : SecondaryStructure (u ++ v).length) :
    SecondaryStructure (u ++ a :: b :: v).length := by
  let e := wordSkipTwoOrderEmbedding u v a b
  let M := S.mapOrderEmbedding e
  let q := insertedAdjacentArc u v a b
  refine
    { arcs := insert q M.arcs
      isPartialMatching := ?_
      isNoncrossing := ?_ }
  · intro c hc d hd hshare
    simp only [Finset.mem_insert] at hc hd
    rcases hc with rfl | hc <;> rcases hd with rfl | hd
    · rfl
    · obtain ⟨d₀, hd₀, rfl⟩ :=
        (SecondaryStructure.mem_mapOrderEmbedding_iff e S d).1 hd
      exact False.elim (insertedAdjacentArc_not_share_mapped u v a b d₀ hshare)
    · obtain ⟨c₀, hc₀, rfl⟩ :=
        (SecondaryStructure.mem_mapOrderEmbedding_iff e S c).1 hc
      exact False.elim (insertedAdjacentArc_not_share_mapped u v a b c₀
        ((Arc.shareEndpoint_symm).2 hshare))
    · exact M.isPartialMatching hc hd hshare
  · intro c hc d hd hcross
    simp only [Finset.mem_insert] at hc hd
    rcases hc with rfl | hc <;> rcases hd with rfl | hd
    · exact (insertedAdjacentArc_not_crosses u v a b q) hcross
    · exact (insertedAdjacentArc_not_crosses u v a b d) hcross
    · exact (insertedAdjacentArc_not_crosses u v a b c)
        ((Arc.crosses_symm).2 hcross)
    · exact M.isNoncrossing hc hd hcross

private theorem wordSkipTwo_exists_of_not_deleted
    (u v : Word) (a b : Nucleotide)
    (p : Fin (u ++ a :: b :: v).length)
    (hl : p ≠ (insertedAdjacentArc u v a b).left)
    (hr : p ≠ (insertedAdjacentArc u v a b).right) :
    ∃ i : Fin (u ++ v).length,
      wordSkipTwoOrderEmbedding u v a b i = p := by
  by_cases hp : p.val < u.length
  · let i : Fin (u ++ v).length := ⟨p.val, by simp; omega⟩
    refine ⟨i, Fin.ext ?_⟩
    rw [wordSkipTwoOrderEmbedding_val]
    simp [i, hp]
  · have hpne : p.val ≠ u.length := by
      intro h
      apply hl
      apply Fin.ext
      exact h
    have hpne' : p.val ≠ u.length + 1 := by
      intro h
      apply hr
      apply Fin.ext
      exact h
    have hpge : u.length + 2 ≤ p.val := by omega
    have hpBound := p.isLt
    simp only [List.length_append, List.length_cons, List.length_nil] at hpBound
    let i : Fin (u ++ v).length := ⟨p.val - 2, by
      simp only [List.length_append]
      omega⟩
    refine ⟨i, Fin.ext ?_⟩
    rw [wordSkipTwoOrderEmbedding_val]
    have hi : ¬ i.val < u.length := by simp [i]; omega
    rw [if_neg hi]
    simp [i]
    omega

private theorem insertAdjacentStructure_compatible
    (u v : Word) (a b : Nucleotide) (hab : Compatible a b)
    (S : SecondaryStructure (u ++ v).length)
    (hS : StructureCompatible (u ++ v).toSequence S) :
    StructureCompatible (u ++ a :: b :: v).toSequence
      (insertAdjacentStructure u v a b S) := by
  let e := wordSkipTwoOrderEmbedding u v a b
  let M := S.mapOrderEmbedding e
  let q := insertedAdjacentArc u v a b
  intro c hc
  change c ∈ insert q M.arcs at hc
  simp only [Finset.mem_insert] at hc
  rcases hc with rfl | hc
  · simpa [q, insertedAdjacentArc, Word.toSequence,
      List.get_eq_getElem] using hab
  · obtain ⟨c₀, hc₀, rfl⟩ :=
      (SecondaryStructure.mem_mapOrderEmbedding_iff e S c).1 hc
    have hccomp := hS c₀ hc₀
    simpa only [e, Arc.mapOrderEmbedding_left,
      Arc.mapOrderEmbedding_right, toSequence_skipTwo] using hccomp

private theorem insertAdjacentStructure_saturated
    (u v : Word) (a b : Nucleotide)
    (S : SecondaryStructure (u ++ v).length)
    (hS : SaturatedStructure S) :
    SaturatedStructure (insertAdjacentStructure u v a b S) := by
  intro p
  let q := insertedAdjacentArc u v a b
  by_cases hl : p = q.left
  · exact ⟨q, by simp [insertAdjacentStructure, q], Or.inl hl⟩
  by_cases hr : p = q.right
  · exact ⟨q, by simp [insertAdjacentStructure, q], Or.inr hr⟩
  obtain ⟨i, hi⟩ := wordSkipTwo_exists_of_not_deleted u v a b p hl hr
  obtain ⟨c, hc, hci⟩ := hS i
  let e := wordSkipTwoOrderEmbedding u v a b
  refine ⟨c.mapOrderEmbedding e, ?_, ?_⟩
  · change c.mapOrderEmbedding e ∈
        insert (insertedAdjacentArc u v a b)
          (S.mapOrderEmbedding e).arcs
    exact Finset.mem_insert_of_mem
      ((SecondaryStructure.mapOrderEmbedding_mem_iff e S c).2 hc)
  · subst p
    exact (Arc.mapOrderEmbedding_incident_iff e c i).2 hci

private theorem saturable_of_deletes
    {x y : Word} (hxy : DeletesComplementaryPair x y)
    (hy : Saturable y) : Saturable x := by
  rcases hxy with ⟨u, v, a, b, hab, rfl, rfl⟩
  obtain ⟨S, hCompat, hSat⟩ := hy
  exact ⟨insertAdjacentStructure u v a b S,
    insertAdjacentStructure_compatible u v a b hab S hCompat,
    insertAdjacentStructure_saturated u v a b S hSat⟩

/-- The empty word is saturated by the empty secondary structure. -/
@[simp]
theorem saturable_empty : Saturable ([] : Word) := by
  refine ⟨SecondaryStructure.empty 0, ?_, ?_⟩
  · intro a ha
    simp [SecondaryStructure.empty] at ha
  · intro i
    exact Fin.elim0 i

/-- Reversing any finite adjacent-deletion history constructs a compatible
perfect noncrossing matching. -/
theorem saturable_of_reducesToEmpty {x : Word}
    (hx : ReducesToEmpty x) : Saturable x := by
  exact Relation.ReflTransGen.head_induction_on hx saturable_empty
    (fun hstep _ ih => saturable_of_deletes hstep ih)

/-! ## Minimum-span arcs -/

/-- Numeric span of an arc. -/
def Arc.span {n : Nat} (a : Arc n) : Nat :=
  a.right.val - a.left.val

@[simp]
theorem Arc.span_pos {n : Nat} (a : Arc n) : 0 < a.span := by
  simp only [Arc.span]
  have := a.ordered
  omega

/-- An arc minimizing span in a saturated nonempty structure must have
adjacent endpoints. -/
theorem exists_minimumSpanArc_adjacent
    (S : SecondaryStructure n) (hSat : SaturatedStructure S)
    (hn : 0 < n) :
    ∃ a ∈ S.arcs,
      a.right.val = a.left.val + 1 ∧
      ∀ b ∈ S.arcs, a.span ≤ b.span := by
  let zero : Fin n := ⟨0, hn⟩
  obtain ⟨a₀, ha₀, hinc₀⟩ := hSat zero
  have hne : S.arcs.Nonempty := ⟨a₀, ha₀⟩
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S.arcs Arc.span hne
  refine ⟨a, ha, ?_, hmin⟩
  by_contra hAdjacent
  have hgap : a.left.val + 1 < a.right.val := by
    have := a.ordered
    omega
  let p : Fin n := ⟨a.left.val + 1, by omega⟩
  obtain ⟨b, hb, hbp⟩ := hSat p
  have hba : b ≠ a := by
    intro h
    subst b
    rcases hbp with hp | hp <;>
      have := congrArg Fin.val hp <;> simp [p] at this <;> omega
  rcases hbp with hpLeft | hpRight
  · have hpLeftVal : b.left.val = a.left.val + 1 := by
      have := congrArg Fin.val hpLeft
      simpa [p] using this.symm
    have hrightNe : b.right ≠ a.right := by
      intro h
      have hEq : b = a :=
        S.eq_of_mem_of_incident hb ha b.incident_right (Or.inr h)
      exact hba hEq
    have hrightLt : b.right.val < a.right.val := by
      by_contra hnot
      have hgt : a.right.val < b.right.val := by
        have hneVal : b.right.val ≠ a.right.val := by
          intro he
          exact hrightNe (Fin.ext he)
        omega
      have hcross : a.Crosses b := by
        unfold Arc.Crosses
        left
        omega
      exact S.isNoncrossing ha hb hcross
    have hstrict : b.span < a.span := by
      simp only [Arc.span]
      omega
    exact (Nat.not_lt_of_ge (hmin b hb)) hstrict
  · have hpRightVal : b.right.val = a.left.val + 1 := by
      have := congrArg Fin.val hpRight
      simpa [p] using this.symm
    have hleftNe : b.left ≠ a.left := by
      intro h
      have hEq : b = a :=
        S.eq_of_mem_of_incident hb ha b.incident_left (Or.inl h)
      exact hba hEq
    have hleftLt : b.left.val < a.left.val := by
      have hle : b.left.val ≤ a.left.val := by
        have := b.ordered
        omega
      have hneVal : b.left.val ≠ a.left.val := by
        intro he
        exact hleftNe (Fin.ext he)
      omega
    have hcross : a.Crosses b := by
      unfold Arc.Crosses
      right
      omega
    exact S.isNoncrossing ha hb hcross

/-! ## Deleting an adjacent matched pair -/

private theorem exists_split_two (z : Word) (k : Nat)
    (hk : k + 1 < z.length) :
    ∃ (u v : Word) (a b : Nucleotide),
      z = u ++ a :: b :: v ∧ u.length = k := by
  induction z generalizing k with
  | nil => simp at hk
  | cons c z ih =>
      cases k with
      | zero =>
          cases z with
          | nil => simp at hk
          | cons d z => exact ⟨[], z, c, d, rfl, rfl⟩
      | succ k =>
          have hk' : k + 1 < z.length := by simp at hk; omega
          obtain ⟨u, v, a, b, hz, hu⟩ := ih k hk'
          refine ⟨c :: u, v, a, b, ?_, by simp [hu]⟩
          simp [hz]

private theorem arc_preimage_of_avoids_deleted
    (u v : Word) (a b : Nucleotide)
    (c : Arc (u ++ a :: b :: v).length)
    (hll : c.left ≠ (insertedAdjacentArc u v a b).left)
    (hlr : c.left ≠ (insertedAdjacentArc u v a b).right)
    (hrl : c.right ≠ (insertedAdjacentArc u v a b).left)
    (hrr : c.right ≠ (insertedAdjacentArc u v a b).right) :
    ∃ d : Arc (u ++ v).length,
      d.mapOrderEmbedding (wordSkipTwoOrderEmbedding u v a b) = c := by
  obtain ⟨i, hi⟩ :=
    wordSkipTwo_exists_of_not_deleted u v a b c.left hll hlr
  obtain ⟨j, hj⟩ :=
    wordSkipTwo_exists_of_not_deleted u v a b c.right hrl hrr
  have hij : i < j := by
    apply (wordSkipTwoOrderEmbedding u v a b).lt_iff_lt.mp
    simpa [hi, hj] using c.ordered
  let d : Arc (u ++ v).length :=
    { left := i
      right := j
      ordered := hij }
  refine ⟨d, Arc.ext ?_ ?_⟩
  · exact hi
  · exact hj

private theorem pullback_saturated_after_adjacent_pair
    (u v : Word) (a b : Nucleotide)
    (S : SecondaryStructure (u ++ a :: b :: v).length)
    (hSat : SaturatedStructure S)
    (hq : insertedAdjacentArc u v a b ∈ S.arcs) :
    SaturatedStructure
      (S.pullbackOrderEmbedding (wordSkipTwoOrderEmbedding u v a b)) := by
  intro i
  let e := wordSkipTwoOrderEmbedding u v a b
  let q := insertedAdjacentArc u v a b
  obtain ⟨c, hc, hci⟩ := hSat (e i)
  have hcne : c ≠ q := by
    intro h
    subst c
    rcases hci with hci | hci
    · exact (wordSkipTwo_ne_deleted u v a b i).1 hci
    · exact (wordSkipTwo_ne_deleted u v a b i).2 hci
  have hll : c.left ≠ q.left := by
    intro h
    exact hcne (S.eq_of_mem_of_incident hc hq c.incident_left (Or.inl h))
  have hlr : c.left ≠ q.right := by
    intro h
    exact hcne (S.eq_of_mem_of_incident hc hq c.incident_left (Or.inr h))
  have hrl : c.right ≠ q.left := by
    intro h
    exact hcne (S.eq_of_mem_of_incident hc hq c.incident_right (Or.inl h))
  have hrr : c.right ≠ q.right := by
    intro h
    exact hcne (S.eq_of_mem_of_incident hc hq c.incident_right (Or.inr h))
  obtain ⟨d, hd⟩ :=
    arc_preimage_of_avoids_deleted u v a b c hll hlr hrl hrr
  refine ⟨d, ?_, ?_⟩
  · rw [SecondaryStructure.mem_pullbackOrderEmbedding_iff, hd]
    exact hc
  · have hmapInc : (d.mapOrderEmbedding e).Incident (e i) := by
      rw [show d.mapOrderEmbedding e = c from hd]
      exact hci
    exact (Arc.mapOrderEmbedding_incident_iff e d i).1 hmapInc

private theorem delete_adjacent_saturable
    (z : Word) (S : SecondaryStructure z.length)
    (hCompat : StructureCompatible z.toSequence S)
    (hSat : SaturatedStructure S)
    (q : Arc z.length) (hq : q ∈ S.arcs)
    (hAdjacent : q.right.val = q.left.val + 1) :
    ∃ y : Word, DeletesComplementaryPair z y ∧ Saturable y ∧
      y.length + 2 = z.length := by
  have hk : q.left.val + 1 < z.length := by
    rw [← hAdjacent]
    exact q.right.isLt
  obtain ⟨u, v, a, b, hz, hu⟩ := exists_split_two z q.left.val hk
  subst z
  have hqEq : q = insertedAdjacentArc u v a b := by
    apply Arc.ext <;> apply Fin.ext
    · simpa using hu.symm
    · simp [hAdjacent, hu]
  subst q
  have hab : Compatible a b := by
    have := hCompat (insertedAdjacentArc u v a b) hq
    simpa [insertedAdjacentArc, Word.toSequence, List.get_eq_getElem] using this
  let R := S.pullbackOrderEmbedding (wordSkipTwoOrderEmbedding u v a b)
  have hRCompat : StructureCompatible (u ++ v).toSequence R := by
    have h := SecondaryStructure.structureCompatible_pullbackOrderEmbedding
      (wordSkipTwoOrderEmbedding u v a b) S
      (u ++ a :: b :: v).toSequence hCompat
    simpa only [toSequence_skipTwo] using h
  have hRSat : SaturatedStructure R :=
    pullback_saturated_after_adjacent_pair u v a b S hSat hq
  refine ⟨u ++ v, ?_, ⟨R, hRCompat, hRSat⟩, ?_⟩
  · exact ⟨u, v, a, b, hab, rfl, rfl⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-! ## Saturability is adjacent cancellation -/

/-- A compatible saturated noncrossing matching always exposes an adjacent
matched pair; deleting a minimum-span pair and recurring reduces the word to
empty. -/
theorem reducesToEmpty_of_saturable (z : Word) (hz : Saturable z) :
    ReducesToEmpty z := by
  by_cases hnil : z = []
  · subst z
    exact Relation.ReflTransGen.refl
  · have hn : 0 < z.length := (List.length_pos_iff).2 hnil
    obtain ⟨S, hCompat, hSat⟩ := hz
    obtain ⟨q, hq, hAdjacent, hmin⟩ :=
      exists_minimumSpanArc_adjacent S hSat hn
    obtain ⟨y, hstep, hy, hlen⟩ :=
      delete_adjacent_saturable z S hCompat hSat q hq hAdjacent
    have hylt : y.length < z.length := by omega
    exact Relation.ReflTransGen.head hstep
      (reducesToEmpty_of_saturable y hy)
termination_by z.length

/-- Perfect compatible noncrossing matchability is exactly reducibility by
adjacent complementary cancellation.  This theorem is independent of target
class and coloring. -/
theorem saturable_iff_reducesToEmpty (z : Word) :
    Saturable z ↔ ReducesToEmpty z :=
  ⟨reducesToEmpty_of_saturable z, saturable_of_reducesToEmpty⟩

/-- Free-group characterization of saturability. -/
theorem saturable_iff_encodedProduct_eq_one (z : Word) :
    Saturable z ↔ encodedProduct z = 1 :=
  (saturable_iff_reducesToEmpty z).trans
    (reducesToEmpty_iff_encodedProduct_eq_one z)

/-- If a concatenation and its prefix are both saturable, then the remaining
suffix is saturable.  This is the cancellation law used in Lemmas 16--18. -/
theorem suffix_saturable_of_concat_saturable_of_prefix_saturable
    (x y : Word) (hxy : Saturable (x ++ y)) (hx : Saturable x) :
    Saturable y := by
  rw [saturable_iff_encodedProduct_eq_one] at hxy hx ⊢
  rw [encodedProduct_append] at hxy
  calc
    encodedProduct y = 1 * encodedProduct y := by simp
    _ = encodedProduct x * encodedProduct y := by rw [hx]
    _ = 1 := hxy

/-! ## Structural counting facts -/

/-- Saturation accounts for every backbone position exactly once as a left
or right endpoint. -/
theorem two_mul_pairCount_eq_of_saturated
    (S : SecondaryStructure n) (hSat : SaturatedStructure S) :
    2 * pairCount S = n := by
  letI : IsEmpty (UnpairedPosition S) :=
    ⟨fun u => u.property (hSat u.val)⟩
  have hcard := Fintype.card_congr (positionRoleEquiv S)
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hcard
  have hside : Fintype.card EndpointSide = 2 := by decide
  rw [hside] at hcard
  simpa only [pairCount, PairedNode, Fintype.card_coe, Fintype.card_eq_zero,
    Nat.zero_add, Nat.mul_comm] using hcard

/-- A saturated structure has exactly half as many arcs as positions. -/
theorem pairCount_eq_half_of_saturated
    (S : SecondaryStructure n) (hSat : SaturatedStructure S) :
    pairCount S = n / 2 := by
  have h := two_mul_pairCount_eq_of_saturated S hSat
  omega

/-- Every saturable word has even length. -/
theorem even_length_of_saturable (z : Word) (hz : Saturable z) :
    ∃ k : Nat, z.length = 2 * k := by
  obtain ⟨S, hCompat, hSat⟩ := hz
  refine ⟨pairCount S, ?_⟩
  simpa [Nat.mul_comm] using (two_mul_pairCount_eq_of_saturated S hSat).symm

/-- Pair count of any chosen saturated witness for a word. -/
theorem pairCount_eq_word_length_div_two
    (z : Word) (S : SecondaryStructure z.length)
    (hSat : SaturatedStructure S) :
    pairCount S = z.length / 2 :=
  pairCount_eq_half_of_saturated S hSat

/-! ## Closed-prefix restriction at an arc from the first position -/

private def takeOrderEmbedding (z : Word) (k : Nat) (hk : k ≤ z.length) :
    Fin (z.take k).length ↪o Fin z.length :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨i.val, by
      exact lt_of_lt_of_le i.isLt (List.length_take_le k z |>.trans hk)⟩)
    (by
      intro i j hij
      exact hij)

@[simp]
private theorem takeOrderEmbedding_val
    (z : Word) (k : Nat) (hk : k ≤ z.length)
    (i : Fin (z.take k).length) :
    (takeOrderEmbedding z k hk i).val = i.val := rfl

private theorem toSequence_takeOrderEmbedding
    (z : Word) (k : Nat) (hk : k ≤ z.length)
    (i : Fin (z.take k).length) :
    z.toSequence (takeOrderEmbedding z k hk i) =
      Word.toSequence (z.take k) i := by
  simp only [Word.toSequence, List.get_eq_getElem]
  exact (List.getElem_take).symm

private theorem arc_preimage_takeOrderEmbedding
    (z : Word) (k : Nat) (hk : k ≤ z.length)
    (c : Arc z.length) (hleft : c.left.val < k)
    (hright : c.right.val < k) :
    ∃ d : Arc (z.take k).length,
      d.mapOrderEmbedding (takeOrderEmbedding z k hk) = c := by
  have htake : (z.take k).length = k := by
    simp [List.length_take, Nat.min_eq_left hk]
  let i : Fin (z.take k).length := ⟨c.left.val, by simpa [htake]⟩
  let j : Fin (z.take k).length := ⟨c.right.val, by simpa [htake]⟩
  let d : Arc (z.take k).length :=
    { left := i
      right := j
      ordered := by simpa [i, j] using c.ordered }
  refine ⟨d, Arc.ext ?_ ?_⟩ <;> apply Fin.ext <;> rfl

/-- If a saturated structure contains an arc from the first position to `j`,
then the closed prefix ending at `j` is itself saturable. -/
theorem prefix_saturable_of_arc_from_zero
    (z : Word) (S : SecondaryStructure z.length)
    (hCompat : StructureCompatible z.toSequence S)
    (hSat : SaturatedStructure S)
    (q : Arc z.length) (hq : q ∈ S.arcs)
    (hqLeft : q.left.val = 0) :
    Saturable (z.take (q.right.val + 1)) := by
  let k := q.right.val + 1
  have hk : k ≤ z.length := by
    dsimp [k]
    exact q.right.isLt
  let e := takeOrderEmbedding z k hk
  let R := S.pullbackOrderEmbedding e
  have hRCompat : StructureCompatible (Word.toSequence (z.take k)) R := by
    have h := SecondaryStructure.structureCompatible_pullbackOrderEmbedding
      e S z.toSequence hCompat
    simpa only [e, toSequence_takeOrderEmbedding] using h
  have hRSat : SaturatedStructure R := by
    intro i
    obtain ⟨c, hc, hci⟩ := hSat (e i)
    have hip : (e i).val ≤ q.right.val := by
      have hi := i.isLt
      simp only [e, takeOrderEmbedding_val, List.length_take,
        Nat.min_eq_left hk] at hi ⊢
      dsimp [k] at hi
      omega
    have hEndpoints : c.left.val < k ∧ c.right.val < k := by
      rcases hci with hpLeft | hpRight
      · have hpVal : c.left.val = (e i).val :=
          congrArg Fin.val hpLeft.symm
        have hrightLe : c.right.val ≤ q.right.val := by
          by_contra hnot
          have hrightGt : q.right.val < c.right.val := by omega
          have hcq : c ≠ q := by
            intro h
            subst c
            have := q.ordered
            omega
          have hleftPos : q.left.val < c.left.val := by
            have hleftNe : c.left ≠ q.left := by
              intro h
              exact hcq (S.eq_of_mem_of_incident hc hq
                c.incident_left (Or.inl h))
            omega
          have hleftBeforeRight : c.left.val < q.right.val := by
            by_contra hnot'
            have hEq : c.left = q.right := by
              apply Fin.ext
              omega
            exact hcq (S.eq_of_mem_of_incident hc hq
              c.incident_left (Or.inr hEq))
          have hcross : q.Crosses c := by
            unfold Arc.Crosses
            left
            omega
          exact S.isNoncrossing hq hc hcross
        dsimp [k]
        constructor <;> omega
      · have hpVal : c.right.val = (e i).val :=
          congrArg Fin.val hpRight.symm
        have hcOrder := c.ordered
        dsimp [k]
        constructor <;> omega
    obtain ⟨d, hd⟩ := arc_preimage_takeOrderEmbedding z k hk c
      hEndpoints.1 hEndpoints.2
    refine ⟨d, ?_, ?_⟩
    · rw [SecondaryStructure.mem_pullbackOrderEmbedding_iff, hd]
      exact hc
    · have hmap : (d.mapOrderEmbedding e).Incident (e i) := by
        rw [show d.mapOrderEmbedding e = c from hd]
        exact hci
      exact (Arc.mapOrderEmbedding_incident_iff e d i).1 hmap
  exact ⟨R, hRCompat, hRSat⟩

end RNA
