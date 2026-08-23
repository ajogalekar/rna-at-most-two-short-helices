abbrev HelixCandidate (n : Nat) := Arc n × Fin (n + 1)
def outer (H : HelixCandidate n) : Arc n := H.1
def length (H : HelixCandidate n) : Nat := H.2.val
def HasStackOffset (T : SecondaryStructure n) (outer : Arc n) (k : Nat) : Prop :=
  ∃ a ∈ T.arcs, outer.StackOffset a k
def IsMaximalHelixRun (T : SecondaryStructure n) (outer : Arc n) (h : Nat) : Prop :=
  0 < h ∧
    outer ∈ T.arcs ∧
    (¬ ∃ a ∈ T.arcs, a.Stacked outer) ∧
    (∀ k : Fin h, HasStackOffset T outer k.val) ∧
    ¬ HasStackOffset T outer h
def IsMaximalHelix (T : SecondaryStructure n) (H : HelixCandidate n) : Prop :=
  IsMaximalHelixRun T H.outer H.length
abbrev MaximalHelix (T : SecondaryStructure n) :=
  {H : HelixCandidate n // IsMaximalHelix T H}
def outer {T : SecondaryStructure n} (H : MaximalHelix T) : Arc n := H.val.outer
def length {T : SecondaryStructure n} (H : MaximalHelix T) : Nat := H.val.length
def HasM5 : Prop :=
  ∃ p : PairedOrRootNode T, 4 < pairedDegree T p
def HasM3Dot : Prop :=
  ∃ p : PairedOrRootNode T,
    HasUnpairedChild T p ∧ 2 < pairedDegree T p
def lengthTwoHelices (T : SecondaryStructure n) : Finset (MaximalHelix T) :=
  maximalHelicesOfLength T 2
def shortHelixCount (T : SecondaryStructure n) : Nat :=
  (lengthTwoHelices T).card
def InTargetClassKLeTwo (T : SecondaryStructure n) : Prop :=
  shortHelixCount T ≤ 2 ∧
    (∀ H : MaximalHelix T, H.length ≠ 1) ∧
    (∀ H : MaximalHelix T, H.length ≠ 2 → 3 ≤ H.length) ∧
    ¬ HasM5 T ∧
    ¬ HasM3Dot T
