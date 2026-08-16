module

public import RNA.Color

@[expose] public section

set_option autoImplicit false

/-!
# Local transfer along a helix

A local helix word is represented by a `List Color` together with an explicit
length equation in the transfer specification.  `exitResidue` and `GreysAt`
walk that word from the parent interface, so they are the parity-level analogue
of the inclusive global level recurrence.
-/

namespace RNA

/-- The residue after walking a local helix colour word from its entry
interface. -/
def exitResidue : Parity → List Color → Parity
  | entry, [] => entry
  | entry, c :: cs => exitResidue (entry + c.deltaParity) cs

/-- Inclusive running residue at a specified position of a colour word. -/
def inclusiveResidueAt (entry : Parity) (colors : List Color)
    (k : Fin colors.length) : Parity :=
  exitResidue entry (colors.take (k.val + 1))

/-- Every grey occurrence in a word has inclusive residue `eta`. -/
def GreysAt (eta : Parity) : Parity → List Color → Prop
  | _entry, [] => True
  | entry, c :: cs =>
      (c = Color.grey → entry + c.deltaParity = eta) ∧
        GreysAt eta (entry + c.deltaParity) cs

def decidableGreysAt (eta : Parity) :
    (entry : Parity) → (colors : List Color) → Decidable (GreysAt eta entry colors)
  | _entry, [] => isTrue trivial
  | entry, c :: cs => by
      simp only [GreysAt]
      letI : Decidable (GreysAt eta (entry + c.deltaParity) cs) :=
        decidableGreysAt eta (entry + c.deltaParity) cs
      infer_instance

instance (eta entry : Parity) (colors : List Color) :
    Decidable (GreysAt eta entry colors) :=
  decidableGreysAt eta entry colors

/-- Pointwise characterization of the grey-residue invariant. -/
theorem greysAt_iff_get_inclusiveResidueAt
    (eta entry : Parity) (colors : List Color) :
    GreysAt eta entry colors ↔
      ∀ k : Fin colors.length,
        colors.get k = Color.grey → inclusiveResidueAt entry colors k = eta := by
  induction colors generalizing entry with
  | nil => simp [GreysAt]
  | cons c cs ih =>
      constructor
      · rintro ⟨hhead, htail⟩ k hkgrey
        revert hkgrey
        refine Fin.cases ?_ (fun j => ?_) k
        · intro hkgrey
          have hc : c = Color.grey := by simpa using hkgrey
          simpa [inclusiveResidueAt, exitResidue] using hhead hc
        · intro hkgrey
          have hj : cs.get j = Color.grey := by simpa using hkgrey
          have ht := (ih (entry + c.deltaParity)).1 htail j hj
          simpa [inclusiveResidueAt, exitResidue] using ht
      · intro hall
        constructor
        · intro hc
          have hz := hall ⟨0, by simp⟩ (by simpa using hc)
          simpa [inclusiveResidueAt, exitResidue] using hz
        · apply (ih (entry + c.deltaParity)).2
          intro j hj
          have hs := hall j.succ (by simpa using hj)
          simpa [inclusiveResidueAt, exitResidue] using hs

/-- Proper exposed multisets at every adjacency internal to a helix word. -/
def InternallyProper : List Color → Prop
  | [] => True
  | [_] => True
  | outer :: inner :: rest =>
      ProperAdjacent outer inner ∧ InternallyProper (inner :: rest)

def decidableInternallyProper :
    (colors : List Color) → Decidable (InternallyProper colors)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | outer :: inner :: rest => by
      simp only [InternallyProper]
      letI : Decidable (InternallyProper (inner :: rest)) :=
        decidableInternallyProper (inner :: rest)
      infer_instance

instance (colors : List Color) : Decidable (InternallyProper colors) :=
  decidableInternallyProper colors

/-- Pointwise adjacent properness implies the recursive list predicate. -/
theorem internallyProper_of_get_succ (colors : List Color)
    (hproper : ∀ (k : Nat) (hk : k + 1 < colors.length),
      ProperAdjacent
        (colors.get ⟨k, by omega⟩)
        (colors.get ⟨k + 1, hk⟩)) :
    InternallyProper colors := by
  induction colors with
  | nil => trivial
  | cons a rest ih =>
      cases rest with
      | nil => trivial
      | cons b tail =>
          constructor
          · simpa using hproper 0 (by simp)
          · apply ih
            intro k hk
            have hnext := hproper (k + 1) (by simpa using hk)
            simpa [Nat.add_assoc] using hnext

/-- The final colour is present and non-grey. -/
def ClosesNonGrey (colors : List Color) : Prop :=
  ∃ c : Color, colors.getLast? = some c ∧ c.NonGrey

instance (colors : List Color) : Decidable (ClosesNonGrey colors) := by
  unfold ClosesNonGrey
  infer_instance

/-- Complete local postcondition for a helix of length `h`.  The requested
opposite-of-grey exit must close non-grey. -/
structure LocalTransfer
    (h : Nat) (entry eta target : Parity) (first : Color) where
  colors : List Color
  length_eq : colors.length = h
  first_eq : colors.head? = some first
  internallyProper : InternallyProper colors
  greysAtEta : GreysAt eta entry colors
  exit_eq : exitResidue entry colors = target
  closesNonGrey : target = eta.opposite → ClosesNonGrey colors

/-- The local admissibility plus the manuscript's deliberately stronger
length-two policy. -/
def Safe (h : Nat) (entry eta : Parity) (first : Color) : Prop :=
  first.AdmissibleAt entry eta ∧
    (h = 2 ∧ entry = eta → first = Color.grey)

instance (h : Nat) (entry eta : Parity) (first : Color) :
    Decidable (Safe h entry eta first) := by
  unfold Safe
  infer_instance

theorem Safe.admissible {h : Nat} {entry eta : Parity} {first : Color}
    (hsafe : Safe h entry eta first) : first.AdmissibleAt entry eta :=
  hsafe.1

theorem Safe.short_eta_first_grey {entry eta : Parity} {first : Color}
    (hsafe : Safe 2 entry eta first) (hentry : entry = eta) :
    first = Color.grey := by
  exact hsafe.2 ⟨rfl, hentry⟩

theorem safe_of_admissible_of_ne_two {h : Nat} {entry eta : Parity} {first : Color}
    (hadm : first.AdmissibleAt entry eta) (hne : h ≠ 2) :
    Safe h entry eta first := by
  refine ⟨hadm, ?_⟩
  rintro ⟨hh, _⟩
  exact (hne hh).elim

/-- Validity of a proposed colour pair for a length-two helix. -/
def ValidTwoPair (entry eta target : Parity) (pair : Color × Color) : Prop :=
  InternallyProper [pair.1, pair.2] ∧
    GreysAt eta entry [pair.1, pair.2] ∧
    exitResidue entry [pair.1, pair.2] = target

instance (entry eta target : Parity) (pair : Color × Color) :
    Decidable (ValidTwoPair entry eta target pair) := by
  unfold ValidTwoPair
  infer_instance

/-- The four rows displayed in Lemma 11 of the canonical manuscript. -/
def twoPairTable (xi eta entry target : Parity) : Finset (Color × Color) :=
  if entry = xi ∧ target = xi then
    {(Color.black, Color.black), (Color.white, Color.white)}
  else if entry = xi ∧ target = eta then
    {(Color.black, Color.grey), (Color.white, Color.grey)}
  else if entry = eta ∧ target = xi then
    {(Color.grey, Color.black), (Color.grey, Color.white)}
  else
    {(Color.black, Color.black), (Color.white, Color.white),
      (Color.grey, Color.grey)}

/-- Exact two-pair bridge: the valid pairs are precisely the entries in the
canonical four-row table. -/
theorem validTwoPair_iff_mem_table
    (xi eta entry target : Parity) (pair : Color × Color)
    (hopposite : eta = xi.opposite) :
    ValidTwoPair entry eta target pair ↔
      pair ∈ twoPairTable xi eta entry target := by
  have hxi_eta : xi ≠ eta := by
    rw [hopposite]
    exact xi.ne_opposite
  have heta_xi : eta ≠ xi := hxi_eta.symm
  have hentry : entry = xi ∨ entry = eta := by
    rcases xi.eq_or_eq_opposite entry with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hopposite.symm)
  have htarget : target = xi ∨ target = eta := by
    rcases xi.eq_or_eq_opposite target with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hopposite.symm)
  rcases pair with ⟨first, second⟩
  rcases hentry with rfl | rfl <;> rcases htarget with rfl | rfl <;>
    cases first <;> cases second <;>
    simp [ValidTwoPair, InternallyProper, GreysAt, exitResidue, twoPairTable,
      ProperAdjacent, adjacentExposure, ProperExposure,
      Parity.add_one_eq_opposite, hopposite]

/-- Equality-of-finite-sets form of the complete bridge theorem. -/
theorem validTwoPairFinset_eq_table
    (xi eta entry target : Parity) (hopposite : eta = xi.opposite) :
    Finset.univ.filter (ValidTwoPair entry eta target) =
      twoPairTable xi eta entry target := by
  ext pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact validTwoPair_iff_mem_table xi eta entry target pair hopposite

/-- The `eta → xi` bridge row forces the first colour to be grey. -/
theorem eta_to_xi_first_grey
    (xi eta : Parity) (pair : Color × Color)
    (hopposite : eta = xi.opposite)
    (hvalid : ValidTwoPair eta eta xi pair) :
    pair.1 = Color.grey := by
  have hmem := (validTwoPair_iff_mem_table xi eta eta xi pair hopposite).1 hvalid
  have hmem' : pair = (Color.grey, Color.black) ∨
      pair = (Color.grey, Color.white) := by
    simpa [twoPairTable, hopposite] using hmem
  rcases hmem' with h | h <;> simp [h]

/-- The `xi → eta` bridge row forces the second colour to be grey. -/
theorem xi_to_eta_second_grey
    (xi eta : Parity) (pair : Color × Color)
    (hopposite : eta = xi.opposite)
    (hvalid : ValidTwoPair xi eta eta pair) :
    pair.2 = Color.grey := by
  have hmem := (validTwoPair_iff_mem_table xi eta xi eta pair hopposite).1 hvalid
  have hmem' : pair = (Color.black, Color.grey) ∨
      pair = (Color.white, Color.grey) := by
    simpa [twoPairTable, hopposite] using hmem
  rcases hmem' with h | h <;> simp [h]

/-- The stronger safe policy selects `GG` in the `eta → eta` row. -/
theorem safe_eta_to_eta_eq_grey_grey
    (eta : Parity) (pair : Color × Color)
    (hsafe : Safe 2 eta eta pair.1)
    (hvalid : ValidTwoPair eta eta eta pair) :
    pair = (Color.grey, Color.grey) := by
  have hfirst : pair.1 = Color.grey := hsafe.short_eta_first_grey rfl
  rcases pair with ⟨first, second⟩
  simp only at hfirst
  subst first
  cases second <;> simp_all [ValidTwoPair, InternallyProper, GreysAt, exitResidue,
    ProperAdjacent, adjacentExposure, ProperExposure, Color.NonGrey,
    Color.AdmissibleAt, Safe]

/-- `BB` witnesses that the stronger safe clause is not logically necessary
for an `eta → eta` transition. -/
theorem eta_to_eta_black_black_valid (eta : Parity) :
    ValidTwoPair eta eta eta (Color.black, Color.black) := by
  simp [ValidTwoPair, InternallyProper, GreysAt, exitResidue,
    ProperAdjacent, adjacentExposure, ProperExposure]

/-- `GG` is valid and satisfies the stronger safe policy at an eta entry. -/
theorem eta_to_eta_grey_grey_safe (eta : Parity) :
    ValidTwoPair eta eta eta (Color.grey, Color.grey) ∧
      Safe 2 eta eta Color.grey := by
  simp [ValidTwoPair, InternallyProper, GreysAt, exitResidue, Safe,
    ProperAdjacent, adjacentExposure, ProperExposure, Color.AdmissibleAt,
    Color.NonGrey]

/-! ## General word lemmas used by the long-helix construction -/

theorem exitResidue_append (entry : Parity) (xs ys : List Color) :
    exitResidue entry (xs ++ ys) = exitResidue (exitResidue entry xs) ys := by
  induction xs generalizing entry with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append, exitResidue]
      exact ih (entry + c.deltaParity)

theorem exitResidue_replicate_grey (entry : Parity) (k : Nat) :
    exitResidue entry (List.replicate k Color.grey) = entry := by
  induction k generalizing entry with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, exitResidue, Color.deltaParity_grey]
      rw [Parity.add_zero, ih]

theorem exitResidue_replicate_nonGrey (entry : Parity) (k : Nat) (c : Color)
    (hc : c.NonGrey) :
    exitResidue entry (List.replicate k c) = entry + (k : Parity) := by
  have hdelta : c.deltaParity = 1 := (Color.deltaParity_eq_one_iff c).2 hc
  induction k generalizing entry with
  | zero => simp [exitResidue]
  | succ k ih =>
      simp only [List.replicate_succ, exitResidue, hdelta, ih]
      rw [Nat.cast_succ]
      ac_rfl

theorem greysAt_replicate_nonGrey (eta entry : Parity) (k : Nat) (c : Color)
    (hc : c.NonGrey) :
    GreysAt eta entry (List.replicate k c) := by
  induction k generalizing entry with
  | zero => trivial
  | succ k ih =>
      simp only [List.replicate_succ, GreysAt]
      exact ⟨fun hgrey => (hc hgrey).elim, ih (entry + c.deltaParity)⟩

theorem greysAt_replicate_grey (eta : Parity) (k : Nat) :
    GreysAt eta eta (List.replicate k Color.grey) := by
  induction k with
  | zero => trivial
  | succ k ih =>
      simp only [List.replicate_succ, GreysAt, Color.deltaParity_grey]
      constructor
      · intro _
        exact Parity.add_zero eta
      · simpa only [Parity.add_zero] using ih

theorem properAdjacent_self (c : Color) : ProperAdjacent c c := by
  cases c <;> decide

theorem internallyProper_replicate (k : Nat) (c : Color) :
    InternallyProper (List.replicate k c) := by
  induction k with
  | zero => trivial
  | succ k ih =>
      cases k with
      | zero => trivial
      | succ k =>
          simp only [List.replicate_succ, InternallyProper]
          exact ⟨properAdjacent_self c, ih⟩

theorem closesNonGrey_replicate (k : Nat) (c : Color)
    (hk : 0 < k) (hc : c.NonGrey) :
    ClosesNonGrey (List.replicate k c) := by
  refine ⟨c, ?_, hc⟩
  rw [List.getLast?_replicate]
  simp [Nat.ne_of_gt hk]

/-- Option A in Lemma 10: the constant non-grey word `a^h`. -/
def constantHelixWord (h : Nat) (a : Color) : List Color :=
  List.replicate h a

/-- The position-two instance of Option B: `a G a^(h-2)`. -/
def oneGreyAtTwoWord (h : Nat) (a : Color) : List Color :=
  a :: Color.grey :: List.replicate (h - 2) a

/-- The position-three instance of Option B: `a a G a^(h-3)`. -/
def oneGreyAtThreeWord (h : Nat) (a : Color) : List Color :=
  a :: a :: Color.grey :: List.replicate (h - 3) a

theorem internallyProper_oneGreyAtTwo (h : Nat) (a : Color) (ha : a.NonGrey) :
    InternallyProper (oneGreyAtTwoWord h a) := by
  unfold oneGreyAtTwoWord
  rcases (Color.nonGrey_iff a).1 ha with rfl | rfl
  all_goals
    cases h - 2 with
    | zero => decide
    | succ k =>
        simp only [List.replicate_succ, InternallyProper]
        exact ⟨by decide, by decide, internallyProper_replicate (k + 1) _⟩

theorem internallyProper_oneGreyAtThree (h : Nat) (a : Color) (ha : a.NonGrey) :
    InternallyProper (oneGreyAtThreeWord h a) := by
  unfold oneGreyAtThreeWord
  rcases (Color.nonGrey_iff a).1 ha with rfl | rfl
  all_goals
    cases h - 3 with
    | zero => decide
    | succ k =>
        simp only [List.replicate_succ, InternallyProper]
        exact ⟨by decide, by decide, by decide,
          internallyProper_replicate (k + 1) _⟩

@[simp]
theorem constantHelixWord_length (h : Nat) (a : Color) :
    (constantHelixWord h a).length = h := by
  simp [constantHelixWord]

theorem oneGreyAtTwoWord_length (h : Nat) (a : Color) (hh : 2 ≤ h) :
    (oneGreyAtTwoWord h a).length = h := by
  simp [oneGreyAtTwoWord]
  omega

theorem oneGreyAtThreeWord_length (h : Nat) (a : Color) (hh : 3 ≤ h) :
    (oneGreyAtThreeWord h a).length = h := by
  simp [oneGreyAtThreeWord]
  omega

@[simp]
theorem constantHelixWord_head (h : Nat) (a : Color) (hh : 0 < h) :
    (constantHelixWord h a).head? = some a := by
  cases h with
  | zero => omega
  | succ k =>
      rw [constantHelixWord, List.replicate_succ]
      rfl

@[simp]
theorem oneGreyAtTwoWord_head (h : Nat) (a : Color) :
    (oneGreyAtTwoWord h a).head? = some a := by
  rfl

@[simp]
theorem oneGreyAtThreeWord_head (h : Nat) (a : Color) :
    (oneGreyAtThreeWord h a).head? = some a := by
  rfl

theorem greysAt_oneGreyAtTwo (eta entry : Parity) (h : Nat) (a : Color)
    (ha : a.NonGrey) (hgrey : entry + a.deltaParity = eta) :
    GreysAt eta entry (oneGreyAtTwoWord h a) := by
  unfold oneGreyAtTwoWord
  simp only [GreysAt, Color.deltaParity_grey]
  refine ⟨fun hag => (ha hag).elim, ?_⟩
  refine ⟨fun _ => ?_, ?_⟩
  · simpa only [Parity.add_zero] using hgrey
  · simpa only [Parity.add_zero] using
      greysAt_replicate_nonGrey eta (entry + a.deltaParity) (h - 2) a ha

theorem greysAt_oneGreyAtThree (eta entry : Parity) (h : Nat) (a : Color)
    (ha : a.NonGrey)
    (hgrey : entry + a.deltaParity + a.deltaParity = eta) :
    GreysAt eta entry (oneGreyAtThreeWord h a) := by
  unfold oneGreyAtThreeWord
  simp only [GreysAt, Color.deltaParity_grey]
  refine ⟨fun hag => (ha hag).elim, ?_⟩
  refine ⟨fun hag => (ha hag).elim, ?_⟩
  refine ⟨fun _ => ?_, ?_⟩
  · simpa only [Parity.add_zero] using hgrey
  · simpa only [Parity.add_zero] using
      greysAt_replicate_nonGrey eta
        (entry + a.deltaParity + a.deltaParity) (h - 3) a ha

theorem exitResidue_oneGreyAtTwo (entry : Parity) (h : Nat) (a : Color)
    (ha : a.NonGrey) :
    exitResidue entry (oneGreyAtTwoWord h a) =
      entry + a.deltaParity + (h - 2 : Nat) := by
  unfold oneGreyAtTwoWord
  simp only [exitResidue, Color.deltaParity_grey, Parity.add_zero]
  exact exitResidue_replicate_nonGrey _ _ _ ha

theorem exitResidue_oneGreyAtThree (entry : Parity) (h : Nat) (a : Color)
    (ha : a.NonGrey) :
    exitResidue entry (oneGreyAtThreeWord h a) =
      entry + a.deltaParity + a.deltaParity + (h - 3 : Nat) := by
  unfold oneGreyAtThreeWord
  simp only [exitResidue, Color.deltaParity_grey, Parity.add_zero]
  exact exitResidue_replicate_nonGrey _ _ _ ha

theorem closesNonGrey_oneGreyAtTwo (h : Nat) (a : Color)
    (hh : 3 ≤ h) (ha : a.NonGrey) :
    ClosesNonGrey (oneGreyAtTwoWord h a) := by
  refine ⟨a, ?_, ha⟩
  unfold oneGreyAtTwoWord
  rw [List.getLast?_cons, List.getLast?_cons, List.getLast?_replicate]
  simp [show h - 2 ≠ 0 by omega]

theorem closesNonGrey_oneGreyAtThree (h : Nat) (a : Color)
    (hh : 4 ≤ h) (ha : a.NonGrey) :
    ClosesNonGrey (oneGreyAtThreeWord h a) := by
  refine ⟨a, ?_, ha⟩
  unfold oneGreyAtThreeWord
  rw [List.getLast?_cons, List.getLast?_cons, List.getLast?_cons,
    List.getLast?_replicate]
  simp [show h - 3 ≠ 0 by omega]

/-- The grey-first eta-exit word `G^h`. -/
def allGreyHelixWord (h : Nat) : List Color :=
  List.replicate h Color.grey

/-- The grey-first xi-exit word `G^(h-1)B`; black is the deterministic
non-grey closing choice. -/
def greyThenBlackHelixWord (h : Nat) : List Color :=
  List.replicate (h - 1) Color.grey ++ [Color.black]

theorem internallyProper_greyThenBlack (k : Nat) (hk : 0 < k) :
    InternallyProper (List.replicate k Color.grey ++ [Color.black]) := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero => decide
      | succ k =>
          simp only [List.replicate_succ, List.cons_append, InternallyProper]
          exact ⟨by decide, ih (by omega)⟩

theorem greysAt_greyThenBlack (eta : Parity) (k : Nat) :
    GreysAt eta eta (List.replicate k Color.grey ++ [Color.black]) := by
  induction k with
  | zero =>
      simp [GreysAt]
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, GreysAt,
        Color.deltaParity_grey]
      exact ⟨fun _ => Parity.add_zero eta,
        by simpa only [Parity.add_zero] using ih⟩

theorem exitResidue_constantHelixWord (entry : Parity) (h : Nat) (a : Color)
    (ha : a.NonGrey) :
    exitResidue entry (constantHelixWord h a) = entry + (h : Parity) := by
  exact exitResidue_replicate_nonGrey entry h a ha

/-- Option B has the parity opposite to Option A because exactly one non-grey
contribution is replaced by grey. -/
theorem exitResidue_oneGreyAtTwo_eq_constant_opposite
    (entry : Parity) (h : Nat) (a : Color) (hh : 2 ≤ h) (ha : a.NonGrey) :
    exitResidue entry (oneGreyAtTwoWord h a) =
      (exitResidue entry (constantHelixWord h a)).opposite := by
  rw [exitResidue_oneGreyAtTwo entry h a ha,
    exitResidue_constantHelixWord entry h a ha]
  have hnat : h - 2 + 2 = h := Nat.sub_add_cancel hh
  have hcast := congrArg (fun k : Nat => (k : Parity)) hnat
  rw [Nat.cast_add,
    show ((2 : Nat) : Parity) = 0 by decide, Parity.add_zero] at hcast
  have hdelta : a.deltaParity = 1 := (Color.deltaParity_eq_one_iff a).2 ha
  rw [hdelta, ← hcast]
  rw [← Parity.add_one_eq_opposite (entry + (h - 2 : Nat))]
  ac_rfl

theorem exitResidue_oneGreyAtThree_eq_constant_opposite
    (entry : Parity) (h : Nat) (a : Color) (hh : 3 ≤ h) (ha : a.NonGrey) :
    exitResidue entry (oneGreyAtThreeWord h a) =
      (exitResidue entry (constantHelixWord h a)).opposite := by
  rw [exitResidue_oneGreyAtThree entry h a ha,
    exitResidue_constantHelixWord entry h a ha]
  have hnat : h - 3 + 3 = h := Nat.sub_add_cancel hh
  have hcast := congrArg (fun k : Nat => (k : Parity)) hnat
  rw [Nat.cast_add, show ((3 : Nat) : Parity) = 1 by decide] at hcast
  have hdelta : a.deltaParity = 1 := (Color.deltaParity_eq_one_iff a).2 ha
  rw [hdelta, ← hcast]
  calc
    entry + 1 + 1 + (h - 3 : Nat) = entry + (h - 3 : Nat) := by
      rw [add_assoc entry, Parity.one_add_one, Parity.add_zero]
    _ = (entry + ((h - 3 : Nat) + 1)).opposite := by
      unfold Parity.opposite
      rw [add_assoc, add_assoc, Parity.one_add_one, Parity.add_zero]

theorem allGreyHelixWord_length (h : Nat) :
    (allGreyHelixWord h).length = h := by
  simp [allGreyHelixWord]

theorem allGreyHelixWord_head (h : Nat) (hh : 0 < h) :
    (allGreyHelixWord h).head? = some Color.grey := by
  unfold allGreyHelixWord
  cases h with
  | zero => omega
  | succ k => rw [List.replicate_succ]; rfl

theorem greyThenBlackHelixWord_length (h : Nat) (hh : 1 ≤ h) :
    (greyThenBlackHelixWord h).length = h := by
  simp [greyThenBlackHelixWord]
  omega

theorem greyThenBlackHelixWord_head (h : Nat) (hh : 2 ≤ h) :
    (greyThenBlackHelixWord h).head? = some Color.grey := by
  unfold greyThenBlackHelixWord
  have hk : 0 < h - 1 := by omega
  cases hsub : h - 1 with
  | zero => omega
  | succ k => rw [List.head?_append_of_ne_nil, List.replicate_succ]
              · rfl
              · simp

theorem exitResidue_greyThenBlackHelixWord (eta : Parity) (h : Nat) :
    exitResidue eta (greyThenBlackHelixWord h) = eta.opposite := by
  unfold greyThenBlackHelixWord
  rw [exitResidue_append, exitResidue_replicate_grey]
  simp only [exitResidue, Color.deltaParity_black]
  exact Parity.add_one_eq_opposite eta

theorem closesNonGrey_greyThenBlackHelixWord (h : Nat) :
    ClosesNonGrey (greyThenBlackHelixWord h) := by
  refine ⟨Color.black, ?_, Color.black_nonGrey⟩
  simp [greyThenBlackHelixWord]

/-- Lemma 10 (long-helix transfer), in the local running-residue model.  The
first colour is fixed, every internal exposure is proper, every grey occurrence
has residue `eta`, the requested exit is reached, and an exit opposite to
`eta` closes non-grey. -/
def longHelixTransfer
    (h : Nat) (entry eta target : Parity) (first : Color)
    (hh : 3 ≤ h) (hadmissible : first.AdmissibleAt entry eta) :
    LocalTransfer h entry eta target first := by
  by_cases hnonGrey : first.NonGrey
  · by_cases hconstant : target = entry + (h : Parity)
    · exact {
        colors := constantHelixWord h first
        length_eq := constantHelixWord_length h first
        first_eq := constantHelixWord_head h first (by omega)
        internallyProper := internallyProper_replicate h first
        greysAtEta := greysAt_replicate_nonGrey eta entry h first hnonGrey
        exit_eq := (exitResidue_constantHelixWord entry h first hnonGrey).trans
          hconstant.symm
        closesNonGrey := fun _ =>
          closesNonGrey_replicate h first (by omega) hnonGrey }
    · have htargetOpposite :
          target = (entry + (h : Parity)).opposite :=
        Parity.eq_opposite_of_ne hconstant
      by_cases hsecondGrey : entry + first.deltaParity = eta
      · have hexit : exitResidue entry (oneGreyAtTwoWord h first) = target :=
          (exitResidue_oneGreyAtTwo_eq_constant_opposite entry h first
            (by omega) hnonGrey).trans <|
            (congrArg Parity.opposite
              (exitResidue_constantHelixWord entry h first hnonGrey)).trans <|
            htargetOpposite.symm
        exact {
          colors := oneGreyAtTwoWord h first
          length_eq := oneGreyAtTwoWord_length h first (by omega)
          first_eq := oneGreyAtTwoWord_head h first
          internallyProper := internallyProper_oneGreyAtTwo h first hnonGrey
          greysAtEta := greysAt_oneGreyAtTwo eta entry h first hnonGrey hsecondGrey
          exit_eq := hexit
          closesNonGrey := fun _ =>
            closesNonGrey_oneGreyAtTwo h first hh hnonGrey }
      · have hdelta : first.deltaParity = 1 :=
          (Color.deltaParity_eq_one_iff first).2 hnonGrey
        have hfirstResidue :
            entry + first.deltaParity = eta.opposite :=
          Parity.eq_opposite_of_ne hsecondGrey
        have hthirdGrey :
            entry + first.deltaParity + first.deltaParity = eta := by
          rw [hfirstResidue, hdelta]
          exact Parity.opposite_add_one eta
        have hexit : exitResidue entry (oneGreyAtThreeWord h first) = target :=
          (exitResidue_oneGreyAtThree_eq_constant_opposite entry h first
            hh hnonGrey).trans <|
            (congrArg Parity.opposite
              (exitResidue_constantHelixWord entry h first hnonGrey)).trans <|
            htargetOpposite.symm
        exact {
          colors := oneGreyAtThreeWord h first
          length_eq := oneGreyAtThreeWord_length h first hh
          first_eq := oneGreyAtThreeWord_head h first
          internallyProper := internallyProper_oneGreyAtThree h first hnonGrey
          greysAtEta := greysAt_oneGreyAtThree eta entry h first hnonGrey hthirdGrey
          exit_eq := hexit
          closesNonGrey := by
            intro htargetXi
            by_cases hfour : 4 ≤ h
            · exact closesNonGrey_oneGreyAtThree h first hfour hnonGrey
            · have heq : h = 3 := by omega
              have hexitEta :
                  exitResidue entry (oneGreyAtThreeWord h first) = eta := by
                rw [exitResidue_oneGreyAtThree entry h first hnonGrey]
                simpa only [heq, Nat.reduceSub, Nat.cast_zero,
                  Parity.add_zero] using hthirdGrey
              have htargetEta : target = eta := hexit.symm.trans hexitEta
              exact (eta.ne_opposite (htargetEta.symm.trans htargetXi)).elim }
  · have hfirstGrey : first = Color.grey := by
      cases first <;> simp_all [Color.NonGrey]
    subst first
    have hentry : entry = eta :=
      (Color.admissibleAt_grey_iff entry eta).1 hadmissible
    subst entry
    by_cases htargetEta : target = eta
    · exact {
        colors := allGreyHelixWord h
        length_eq := allGreyHelixWord_length h
        first_eq := allGreyHelixWord_head h (by omega)
        internallyProper := internallyProper_replicate h Color.grey
        greysAtEta := greysAt_replicate_grey eta h
        exit_eq := (exitResidue_replicate_grey eta h).trans htargetEta.symm
        closesNonGrey := by
          intro hop
          exact (eta.ne_opposite (htargetEta.symm.trans hop)).elim }
    · have htargetXi : target = eta.opposite :=
        Parity.eq_opposite_of_ne htargetEta
      have hk : 0 < h - 1 := by omega
      exact {
        colors := greyThenBlackHelixWord h
        length_eq := greyThenBlackHelixWord_length h (by omega)
        first_eq := greyThenBlackHelixWord_head h (by omega)
        internallyProper := internallyProper_greyThenBlack (h - 1) hk
        greysAtEta := greysAt_greyThenBlack eta (h - 1)
        exit_eq := (exitResidue_greyThenBlackHelixWord eta h).trans htargetXi.symm
        closesNonGrey := fun _ => closesNonGrey_greyThenBlackHelixWord h }

/-- A long helix satisfying `Safe` automatically satisfies the admissibility
premise of the transfer theorem; the short-only clause is irrelevant here. -/
def longHelixTransfer_of_safe
    (h : Nat) (entry eta target : Parity) (first : Color)
    (hh : 3 ≤ h) (hsafe : Safe h entry eta first) :
    LocalTransfer h entry eta target first :=
  longHelixTransfer h entry eta target first hh hsafe.admissible

/-- Proposition-valued wrapper for kernel-dependency auditing and for existence-style
structural induction in the future global construction. -/
theorem exists_longHelixTransfer
    (h : Nat) (entry eta target : Parity) (first : Color)
    (hh : 3 ≤ h) (hadmissible : first.AdmissibleAt entry eta) :
    Nonempty (LocalTransfer h entry eta target first) :=
  ⟨longHelixTransfer h entry eta target first hh hadmissible⟩

/-- The combined length-two consequence used by the safe allocation rule:
whenever the requested terminal residue is `eta`, the closing colour is grey,
independently of which of the two residues is the entry. -/
theorem safe_twoPair_target_eta_second_grey
    (xi eta entry : Parity) (pair : Color × Color)
    (hopposite : eta = xi.opposite)
    (hsafe : Safe 2 entry eta pair.1)
    (hvalid : ValidTwoPair entry eta eta pair) :
    pair.2 = Color.grey := by
  have hentry : entry = xi ∨ entry = eta := by
    rcases xi.eq_or_eq_opposite entry with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hopposite.symm)
  rcases hentry with hentry | hentry
  · rw [hentry] at hsafe hvalid
    exact xi_to_eta_second_grey xi eta pair hopposite hvalid
  · rw [hentry] at hsafe hvalid
    have hpair := safe_eta_to_eta_eq_grey_grey eta pair hsafe hvalid
    exact congrArg Prod.snd hpair

end RNA
