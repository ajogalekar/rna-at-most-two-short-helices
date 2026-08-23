inductive Nucleotide where
  | A
  | C
  | G
  | U
  deriving DecidableEq, Repr
def comp : Nucleotide → Nucleotide
  | A => U
  | U => A
  | C => G
  | G => C
def Compatible (x y : Nucleotide) : Prop := y = x.comp
abbrev Sequence (n : Nat) := Fin n → Nucleotide
structure Arc (n : Nat) where
  left : Fin n
  right : Fin n
  ordered : left < right
  deriving DecidableEq
def Crosses (a b : Arc n) : Prop :=
  (a.left < b.left ∧ b.left < a.right ∧ a.right < b.right) ∨
  (b.left < a.left ∧ a.left < b.right ∧ b.right < a.right)
def IsPartialMatching (P : Finset (Arc n)) : Prop :=
  ∀ {a : Arc n}, a ∈ P →
    ∀ {b : Arc n}, b ∈ P →
      a.ShareEndpoint b → a = b
def IsNoncrossing (P : Finset (Arc n)) : Prop :=
  ∀ {a : Arc n}, a ∈ P →
    ∀ {b : Arc n}, b ∈ P →
      ¬ a.Crosses b
structure SecondaryStructure (n : Nat) where
  arcs : Finset (Arc n)
  isPartialMatching : IsPartialMatching arcs
  isNoncrossing : IsNoncrossing arcs
def StructureCompatible (w : Sequence n) (S : SecondaryStructure n) : Prop :=
  ∀ a ∈ S.arcs, Compatible (w a.left) (w a.right)
def pairCount (S : SecondaryStructure n) : Nat := S.arcs.card
def UniqueDesigns (w : Sequence n) (T : SecondaryStructure n) : Prop :=
  StructureCompatible w T ∧
    ∀ S : SecondaryStructure n,
      StructureCompatible w S →
      S ≠ T →
      pairCount S < pairCount T
