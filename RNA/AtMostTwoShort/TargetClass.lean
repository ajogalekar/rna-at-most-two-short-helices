module

public import RNA.TargetClass

@[expose] public section

set_option autoImplicit false

/-!
# Targets with at most two short maximal helices

This module defines the global, presentation-free count of maximal helices of
length two and the enlarged target class used by the resource induction.
-/

namespace RNA

variable {n : Nat}

/-- The finite set of all maximal helices whose exact run length is two. -/
def lengthTwoHelices (T : SecondaryStructure n) : Finset (MaximalHelix T) :=
  maximalHelicesOfLength T 2

/-- The number of maximal helices whose exact run length is two. -/
def shortHelixCount (T : SecondaryStructure n) : Nat :=
  (lengthTwoHelices T).card

@[simp]
theorem mem_lengthTwoHelices_iff (T : SecondaryStructure n)
    (H : MaximalHelix T) :
    H ∈ lengthTwoHelices T ↔ H.length = 2 := by
  simp [lengthTwoHelices]

/-- The same length-two helices represented by their canonical outer arcs. -/
def lengthTwoHelixOuters (T : SecondaryStructure n) : Finset (Arc n) :=
  (lengthTwoHelices T).image MaximalHelix.outer

@[simp]
theorem mem_lengthTwoHelixOuters_iff (T : SecondaryStructure n)
    (a : Arc n) :
    a ∈ lengthTwoHelixOuters T ↔
      ∃ H : MaximalHelix T, H.length = 2 ∧ H.outer = a := by
  simp [lengthTwoHelixOuters]

theorem maximalHelix_outer_injective (T : SecondaryStructure n) :
    Function.Injective (MaximalHelix.outer : MaximalHelix T → Arc n) :=
  MaximalHelix.outer_injective

/-- Counting canonical head nodes gives the same answer as counting maximal
helix descriptors.  In particular, the count makes no choice of a preferred
presentation of a maximal run. -/
theorem lengthTwoHelixOuters_card (T : SecondaryStructure n) :
    (lengthTwoHelixOuters T).card = shortHelixCount T := by
  rw [lengthTwoHelixOuters, shortHelixCount]
  exact Finset.card_image_of_injective _ (maximalHelix_outer_injective T)

theorem shortHelixCount_eq_zero_iff (T : SecondaryStructure n) :
    shortHelixCount T = 0 ↔
      ∀ H : MaximalHelix T, H.length ≠ 2 := by
  rw [shortHelixCount, Finset.card_eq_zero]
  constructor
  · intro hempty H hlen
    have hmem : H ∈ lengthTwoHelices T :=
      (mem_lengthTwoHelices_iff T H).2 hlen
    rw [hempty] at hmem
    simp at hmem
  · intro hnone
    apply Finset.eq_empty_iff_forall_notMem.2
    intro H hmem
    exact hnone H ((mem_lengthTwoHelices_iff T H).1 hmem)

theorem shortHelixCount_eq_one_iff (T : SecondaryStructure n) :
    shortHelixCount T = 1 ↔
      ∃! H : MaximalHelix T, H.length = 2 := by
  change (lengthTwoHelices T).card = 1 ↔ _
  rw [Finset.card_eq_one_iff_existsUnique]
  simp only [mem_lengthTwoHelices_iff]

/-- Cardinality two is equivalent to two distinct witnesses exhausting every
length-two maximal helix. -/
theorem shortHelixCount_eq_two_iff (T : SecondaryStructure n) :
    shortHelixCount T = 2 ↔
      ∃ H K : MaximalHelix T,
        H ≠ K ∧ H.length = 2 ∧ K.length = 2 ∧
          ∀ L : MaximalHelix T, L.length = 2 → L = H ∨ L = K := by
  change (lengthTwoHelices T).card = 2 ↔ _
  rw [Finset.card_eq_two]
  constructor
  · rintro ⟨H, K, hne, hset⟩
    refine ⟨H, K, hne, ?_, ?_, ?_⟩
    · have : H ∈ lengthTwoHelices T := by simp [hset]
      exact (mem_lengthTwoHelices_iff T H).1 this
    · have : K ∈ lengthTwoHelices T := by simp [hset]
      exact (mem_lengthTwoHelices_iff T K).1 this
    · intro L hlen
      have hmem : L ∈ lengthTwoHelices T :=
        (mem_lengthTwoHelices_iff T L).2 hlen
      simpa [hset] using hmem
  · rintro ⟨H, K, hne, hH, hK, hall⟩
    refine ⟨H, K, hne, ?_⟩
    ext L
    simp only [mem_lengthTwoHelices_iff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · exact hall L
    · rintro (rfl | rfl) <;> assumption

/-- The at-most-two class.  The explicit no-length-one clause is retained as
part of the scientific statement even though the next clause also rules out
length one. -/
def InTargetClassKLeTwo (T : SecondaryStructure n) : Prop :=
  shortHelixCount T ≤ 2 ∧
    (∀ H : MaximalHelix T, H.length ≠ 1) ∧
    (∀ H : MaximalHelix T, H.length ≠ 2 → 3 ≤ H.length) ∧
    ¬ HasM5 T ∧
    ¬ HasM3Dot T

instance instDecidableInTargetClassKLeTwo (T : SecondaryStructure n) :
    Decidable (InTargetClassKLeTwo T) := by
  unfold InTargetClassKLeTwo
  infer_instance

/-- The exact-two subclass, useful as a corollary but not as the induction
hypothesis. -/
def InTargetClassK2 (T : SecondaryStructure n) : Prop :=
  InTargetClassKLeTwo T ∧ shortHelixCount T = 2

instance instDecidableInTargetClassK2 (T : SecondaryStructure n) :
    Decidable (InTargetClassK2 T) := by
  unfold InTargetClassK2
  infer_instance

theorem targetClassKLeTwo_shortHelixCount_le {T : SecondaryStructure n}
    (hK : InTargetClassKLeTwo T) : shortHelixCount T ≤ 2 :=
  hK.1

theorem targetClassKLeTwo_no_length_one {T : SecondaryStructure n}
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T) :
    H.length ≠ 1 :=
  hK.2.1 H

theorem targetClassKLeTwo_nonshort_length_at_least_three
    {T : SecondaryStructure n} (hK : InTargetClassKLeTwo T)
    (H : MaximalHelix T) (hlen : H.length ≠ 2) :
    3 ≤ H.length :=
  hK.2.2.1 H hlen

theorem targetClassKLeTwo_motifFree {T : SecondaryStructure n}
    (hK : InTargetClassKLeTwo T) : MotifFree T :=
  ⟨hK.2.2.2.1, hK.2.2.2.2⟩

theorem targetClassK2_shortHelixCount_eq_two {T : SecondaryStructure n}
    (hK : InTargetClassK2 T) : shortHelixCount T = 2 :=
  hK.2

/-- The completed one-short class has global short count exactly one. -/
theorem shortHelixCount_eq_one_of_inTargetClassK {T : SecondaryStructure n}
    (hK : InTargetClassK T) : shortHelixCount T = 1 := by
  apply (shortHelixCount_eq_one_iff T).2
  obtain ⟨H, hlen, hunique, _⟩ := hK
  exact ⟨H, hlen, fun K hKlen => hunique K hKlen⟩

/-- Every completed one-short target belongs to the enlarged at-most-two
class.  This is a relation between hypotheses, not an appeal to the old
designability theorem. -/
theorem inTargetClassKLeTwo_of_inTargetClassK {T : SecondaryStructure n}
    (hK : InTargetClassK T) : InTargetClassKLeTwo T := by
  have hcount := shortHelixCount_eq_one_of_inTargetClassK hK
  obtain ⟨selected, hselected, hunique, hnone, hlong, hm5, hm3⟩ := hK
  refine ⟨?_, hnone, ?_, hm5, hm3⟩
  · rw [hcount]
    omega
  · intro H hHtwo
    apply hlong H
    intro hEq
    subst H
    exact hHtwo hselected

end RNA
