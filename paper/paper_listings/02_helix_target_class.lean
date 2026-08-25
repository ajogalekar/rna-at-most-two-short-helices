abbrev PairedNode := {a : Arc n // a ∈ T.arcs}
abbrev UnpairedPosition := {i : Fin n // ¬ T.positionPaired i}
abbrev NonRootNode := PairedNode T ⊕ UnpairedPosition T
abbrev PairedOrRootNode := Option (PairedNode T)
def StrictlyContains (p : PairedNode T) : NonRootNode T → Prop
  | Sum.inl q => p.val.left < q.val.left ∧ q.val.right < p.val.right
  | Sum.inr u => p.val.left < u.val ∧ u.val < p.val.right
def enclosingPairs (c : NonRootNode T) : Finset (PairedNode T) :=
  Finset.univ.filter (fun p => PairedNode.StrictlyContains T p c)
def parent (c : NonRootNode T) : PairedOrRootNode T :=
  if h : (enclosingPairs T c).Nonempty then
    some ((enclosingPairs T c).max' h)
  else
    none
def pairedChildren (p : PairedOrRootNode T) : Finset (PairedNode T) :=
  Finset.univ.filter (fun c => parent T (Sum.inl c) = p)
def unpairedChildren (p : PairedOrRootNode T) : Finset (UnpairedPosition T) :=
  Finset.univ.filter (fun c => parent T (Sum.inr c) = p)
def pairedChildCount (p : PairedOrRootNode T) : Nat :=
  (pairedChildren T p).card
def pairedDegree : PairedOrRootNode T → Nat
  | none => pairedChildCount T none
  | some p => 1 + pairedChildCount T (some p)
def Arc.StackOffset (outer inner : Arc n) (k : Nat) : Prop :=
  inner.left.val = outer.left.val + k ∧
    inner.right.val + k = outer.right.val
def Arc.Stacked (outer inner : Arc n) : Prop :=
  outer.StackOffset inner 1
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
def HasUnpairedChild (p : PairedOrRootNode T) : Prop :=
  (unpairedChildren T p).Nonempty
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
