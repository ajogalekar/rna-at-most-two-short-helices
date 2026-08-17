module

public import Mathlib.Data.List.OfFn
public import RNA.Alphabet

@[expose] public section

set_option autoImplicit false

/-!
# Finite RNA words

Variable-length words are represented internally by lists.  The public
scientific sequence type remains `Sequence n = Fin n → Nucleotide`; the
conversions below retain every nucleotide at the same zero-based position.
-/

namespace RNA

/-- A finite, variable-length RNA word. -/
abbrev Word := List Nucleotide

namespace Word

/-- The empty RNA word. -/
def empty : Word := []

/-- Concatenation of finite RNA words. -/
def append (x y : Word) : Word := x ++ y

/-- Wrap a word between one nucleotide on each side. -/
def wrap (a b : Nucleotide) (z : Word) : Word := a :: z ++ [b]

/-- `x` is a (not necessarily proper) prefix of `z`. -/
def IsPrefix (x z : Word) : Prop := ∃ y : Word, z = x ++ y

/-- `y` is a (not necessarily proper) suffix of `z`. -/
def IsSuffix (y z : Word) : Prop := ∃ x : Word, z = x ++ y

/-- `x` is a proper prefix of `z`. -/
def IsProperPrefix (x z : Word) : Prop := IsPrefix x z ∧ x.length < z.length

/-- View a list word as the public complete sequence on its positions. -/
def toSequence (z : Word) : Sequence z.length := z.get

@[simp]
theorem length_empty : empty.length = 0 := rfl

@[simp]
theorem length_append (x y : Word) : (append x y).length = x.length + y.length := by
  simp [append]

@[simp]
theorem length_take (k : Nat) (z : Word) : (z.take k).length = min k z.length := by
  simp

@[simp]
theorem length_drop (k : Nat) (z : Word) : (z.drop k).length = z.length - k := by
  simp

@[simp]
theorem length_wrap (a b : Nucleotide) (z : Word) :
    (wrap a b z).length = z.length + 2 := by
  simp [wrap]

@[simp]
theorem take_zero (z : Word) : z.take 0 = empty := by
  simp [empty]

@[simp]
theorem drop_zero (z : Word) : z.drop 0 = z := by
  simp

@[simp]
theorem take_length (z : Word) : z.take z.length = z := by
  simp

@[simp]
theorem drop_length (z : Word) : z.drop z.length = empty := by
  simp [empty]

/-- Splitting at `k` and concatenating the two pieces recovers the word. -/
theorem take_append_drop (k : Nat) (z : Word) :
    z.take k ++ z.drop k = z := by
  exact List.take_append_drop k z

theorem take_isPrefix (k : Nat) (z : Word) : IsPrefix (z.take k) z := by
  exact ⟨z.drop k, (take_append_drop k z).symm⟩

theorem drop_isSuffix (k : Nat) (z : Word) : IsSuffix (z.drop k) z := by
  exact ⟨z.take k, (take_append_drop k z).symm⟩

@[simp]
theorem toSequence_apply (z : Word) (i : Fin z.length) :
    toSequence z i = z.get i := rfl

@[simp]
theorem toSequence_append_left (x y : Word) (i : Fin x.length) :
    toSequence (x ++ y)
      (Fin.cast (by simp) (Fin.castAdd y.length i)) =
        toSequence x i := by
  simp [toSequence]

@[simp]
theorem toSequence_append_right (x y : Word) (i : Fin y.length) :
    toSequence (x ++ y)
      (Fin.cast (by simp) (Fin.natAdd x.length i)) =
        toSequence y i := by
  simp [toSequence]

end Word

namespace Sequence

/-- Convert a public fixed-length sequence to its list of values in backbone
order. -/
def toWord {n : Nat} (w : Sequence n) : Word := List.ofFn w

@[simp]
theorem length_toWord {n : Nat} (w : Sequence n) : (toWord w).length = n := by
  simp [toWord]

/-- Conversion to a word preserves the value at every position, with only the
length equality cast required by the dependent `List.get` index. -/
@[simp]
theorem get_toWord {n : Nat} (w : Sequence n) (i : Fin (toWord w).length) :
    (toWord w).get i = w (Fin.cast (length_toWord w) i) := by
  simpa [toWord] using List.get_ofFn w i

/-- Converting a word to a sequence and back is exactly the original list. -/
@[simp]
theorem toWord_toSequence (z : Word) : toWord (Word.toSequence z) = z := by
  simpa [toWord, Word.toSequence] using List.ofFn_get z

/-- Converting a sequence to a word and reading the corresponding position
returns exactly the original nucleotide. -/
@[simp]
theorem toSequence_toWord_apply {n : Nat} (w : Sequence n) (i : Fin n) :
    Word.toSequence (toWord w) (Fin.cast (length_toWord w).symm i) = w i := by
  change (toWord w).get (Fin.cast (length_toWord w).symm i) = w i
  rw [get_toWord]
  simp

/-- The sequence obtained by transporting `Word.toSequence (toWord w)` back
along its proved length equality is exactly `w`. -/
theorem toSequence_toWord {n : Nat} (w : Sequence n) :
    (fun i : Fin n =>
      Word.toSequence (toWord w) (Fin.cast (length_toWord w).symm i)) = w := by
  funext i
  exact toSequence_toWord_apply w i

end Sequence

end RNA
