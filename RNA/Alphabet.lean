module

public import Mathlib.Data.Fintype.Pi

@[expose] public section

set_option autoImplicit false

/-!
# The four-letter Watson--Crick alphabet

Positions in the manuscript are numbered `1, ..., n`.  In this formalization a
position is an element of `Fin n`, and is therefore numbered `0, ..., n - 1`.
The translations are:

* manuscript position `k` becomes the `Fin n` value whose `.val` is `k - 1`;
* Lean position `i : Fin n` is manuscript position `i.val + 1`;
* manuscript arc `(i, j)` becomes the Lean arc with endpoint values
  `(i - 1, j - 1)`.

No nucleotide identities are attached to positions until a complete
`Sequence n` is chosen.
-/

namespace RNA

/-- The RNA alphabet in the Watson--Crick model of the manuscript. -/
inductive Nucleotide where
  | A
  | C
  | G
  | U
  deriving DecidableEq, Repr

instance instFintypeNucleotide : Fintype Nucleotide where
  elems := {Nucleotide.A, Nucleotide.C, Nucleotide.G, Nucleotide.U}
  complete := by
    intro x
    cases x <;> simp

namespace Nucleotide

/-- Watson--Crick complementation. -/
@[simp]
def comp : Nucleotide → Nucleotide
  | A => U
  | U => A
  | C => G
  | G => C

@[simp]
theorem comp_comp (x : Nucleotide) : comp (comp x) = x := by
  cases x <;> rfl

@[simp]
theorem comp_ne_self (x : Nucleotide) : comp x ≠ x := by
  cases x <;> decide

@[simp]
theorem self_ne_comp (x : Nucleotide) : x ≠ comp x := by
  exact Ne.symm (comp_ne_self x)

end Nucleotide

/-- Two letters are compatible exactly when the second is the unique
Watson--Crick complement of the first.  Thus the ordered compatible pairs are
exactly `A-U`, `U-A`, `C-G`, and `G-C`; in particular there is no `G-U` pair. -/
def Compatible (x y : Nucleotide) : Prop := y = x.comp

instance instDecidableCompatible (x y : Nucleotide) : Decidable (Compatible x y) :=
  by
    unfold Compatible
    infer_instance

@[simp]
theorem compatible_iff_eq_comp (x y : Nucleotide) : Compatible x y ↔ y = x.comp :=
  Iff.rfl

@[simp]
theorem compatible_comp (x : Nucleotide) : Compatible x x.comp :=
  rfl

@[simp]
theorem comp_compatible (x : Nucleotide) : Compatible x.comp x := by
  exact x.comp_comp.symm

theorem compatible_symm {x y : Nucleotide} (h : Compatible x y) : Compatible y x := by
  rw [compatible_iff_eq_comp] at h ⊢
  subst y
  exact x.comp_comp.symm

theorem compatible_comm (x y : Nucleotide) : Compatible x y ↔ Compatible y x :=
  ⟨compatible_symm, compatible_symm⟩

/-- Explicit enumeration of all and only the compatible ordered pairs. -/
theorem compatible_iff_four_pairs (x y : Nucleotide) :
    Compatible x y ↔
      (x = Nucleotide.A ∧ y = Nucleotide.U) ∨
      (x = Nucleotide.U ∧ y = Nucleotide.A) ∨
      (x = Nucleotide.C ∧ y = Nucleotide.G) ∨
      (x = Nucleotide.G ∧ y = Nucleotide.C) := by
  cases x <;> cases y <;> decide

@[simp]
theorem compatible_same_iff (x : Nucleotide) : ¬ Compatible x x := by
  exact x.self_ne_comp

/-- A complete RNA sequence of length `n`: every `Fin n` position receives one
of the four nucleotide letters. -/
abbrev Sequence (n : Nat) := Fin n → Nucleotide

namespace Sequence

@[ext]
theorem ext {n : Nat} {w v : Sequence n} (h : ∀ i, w i = v i) : w = v :=
  funext h

end Sequence

end RNA
