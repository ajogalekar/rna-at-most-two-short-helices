module

public import RNA.SequenceCertificate

@[expose] public section

set_option autoImplicit false

/-!
# Prefix balances and exact tree levels

The boundary balance sums the first `k` backbone positions.  For a sequence
constructed from a proper coloring it is also the sum of `Color.delta` over
the target pairs open at that boundary.  The latter identity is proved from
the exact position-role equivalence, so completed target intervals cancel
without any informal traversal argument.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Signed `G`-minus-`C` contribution of one nucleotide. -/
@[simp]
def nucleotideWeight : Nucleotide → Int
  | .A => 0
  | .C => -1
  | .G => 1
  | .U => 0

@[simp]
theorem nucleotideWeight_comp (x : Nucleotide) :
    nucleotideWeight x.comp = -nucleotideWeight x := by
  cases x <;> rfl

/-- The boundary immediately before a zero-indexed position. -/
def boundaryBefore (i : Fin n) : Fin (n + 1) := Fin.castSucc i

/-- The boundary immediately after a zero-indexed position. -/
def boundaryAfter (i : Fin n) : Fin (n + 1) := Fin.succ i

@[simp]
theorem boundaryBefore_val (i : Fin n) :
    (boundaryBefore i).val = i.val := rfl

@[simp]
theorem boundaryAfter_val (i : Fin n) :
    (boundaryAfter i).val = i.val + 1 := rfl

/-- Backbone positions strictly before a boundary. -/
def positionsBeforeBoundary (k : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < k.val

/-- `G`-minus-`C` balance on an arbitrary finite set of positions. -/
def balanceOn (w : Sequence n) (s : Finset (Fin n)) : Int :=
  ∑ i ∈ s, nucleotideWeight (w i)

/-- Number of occurrences of one nucleotide in a finite position set. -/
def nucleotideCountIn (w : Sequence n) (s : Finset (Fin n))
    (x : Nucleotide) : Nat :=
  (s.filter fun i => w i = x).card

/-- Balance on any finite position set is exactly its integer `G` count minus
its integer `C` count. -/
theorem balanceOn_eq_count_G_sub_C (w : Sequence n) (s : Finset (Fin n)) :
    balanceOn w s =
      (nucleotideCountIn w s Nucleotide.G : Int) -
        (nucleotideCountIn w s Nucleotide.C : Int) := by
  rw [balanceOn, nucleotideCountIn, nucleotideCountIn,
    Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  cases w i <;> simp

/-- Balance of the first `k` positions, where `k` is a backbone boundary. -/
def prefixBalanceBoundary (w : Sequence n) (k : Fin (n + 1)) : Int :=
  balanceOn w (positionsBeforeBoundary k)

/-- Manuscript-style inclusive prefix balance at a backbone position. -/
def prefixBalanceAt (w : Sequence n) (i : Fin n) : Int :=
  prefixBalanceBoundary w (boundaryAfter i)

@[simp]
theorem prefixBalanceBoundary_zero (w : Sequence n) :
    prefixBalanceBoundary w ⟨0, Nat.zero_lt_succ n⟩ = 0 := by
  simp [prefixBalanceBoundary, balanceOn, positionsBeforeBoundary]

theorem prefixBalanceAt_eq_boundaryAfter (w : Sequence n) (i : Fin n) :
    prefixBalanceAt w i = prefixBalanceBoundary w (boundaryAfter i) := rfl

/-- Positions in the closed backbone interval `[a,b]`. -/
def closedIntervalPositions (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a ≤ i ∧ i ≤ b

/-- Positions in the strict backbone interval `(a,b)`. -/
def openIntervalPositions (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => a < i ∧ i < b

def closedIntervalBalance (w : Sequence n) (a b : Fin n) : Int :=
  balanceOn w (closedIntervalPositions a b)

def openIntervalBalance (w : Sequence n) (a b : Fin n) : Int :=
  balanceOn w (openIntervalPositions a b)

theorem openIntervalBalance_eq_count_G_sub_C
    (w : Sequence n) (a b : Fin n) :
    openIntervalBalance w a b =
      (nucleotideCountIn w (openIntervalPositions a b) Nucleotide.G : Int) -
        (nucleotideCountIn w (openIntervalPositions a b) Nucleotide.C : Int) := by
  exact balanceOn_eq_count_G_sub_C w (openIntervalPositions a b)

@[simp]
theorem closedIntervalBalance_self (w : Sequence n) (i : Fin n) :
    closedIntervalBalance w i i = nucleotideWeight (w i) := by
  have hset : closedIntervalPositions i i = {i} := by
    ext j
    simp only [closedIntervalPositions, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => by subst j; exact ⟨le_rfl, le_rfl⟩⟩
  rw [closedIntervalBalance, hset]
  simp [balanceOn]

/-- A closed interval is the difference between its after-right and
before-left boundary balances. -/
theorem closedIntervalBalance_eq_boundary_sub
    (w : Sequence n) {a b : Fin n} (hab : a ≤ b) :
    closedIntervalBalance w a b =
      prefixBalanceBoundary w (boundaryAfter b) -
        prefixBalanceBoundary w (boundaryBefore a) := by
  have hsub : positionsBeforeBoundary (boundaryBefore a) ⊆
      positionsBeforeBoundary (boundaryAfter b) := by
    intro i hi
    simp only [positionsBeforeBoundary, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi ⊢
    change i.val < a.val at hi
    change i.val < b.val + 1
    have habv : a.val ≤ b.val := hab
    omega
  have hdiff :
      positionsBeforeBoundary (boundaryAfter b) \
          positionsBeforeBoundary (boundaryBefore a) =
        closedIntervalPositions a b := by
    ext i
    simp only [positionsBeforeBoundary, closedIntervalPositions,
      Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt]
    change (i.val < b.val + 1 ∧ a.val ≤ i.val) ↔
      (a.val ≤ i.val ∧ i.val ≤ b.val)
    omega
  have hsum := Finset.sum_sdiff
    (f := fun i => nucleotideWeight (w i)) hsub
  rw [hdiff] at hsum
  change closedIntervalBalance w a b +
      prefixBalanceBoundary w (boundaryBefore a) =
        prefixBalanceBoundary w (boundaryAfter b) at hsum
  omega

/-- A strict interval is the difference between its before-right and
after-left boundary balances. -/
theorem openIntervalBalance_eq_boundary_sub
    (w : Sequence n) {a b : Fin n} (hab : a < b) :
    openIntervalBalance w a b =
      prefixBalanceBoundary w (boundaryBefore b) -
        prefixBalanceBoundary w (boundaryAfter a) := by
  have hsub : positionsBeforeBoundary (boundaryAfter a) ⊆
      positionsBeforeBoundary (boundaryBefore b) := by
    intro i hi
    simp only [positionsBeforeBoundary, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi ⊢
    change i.val < a.val + 1 at hi
    change i.val < b.val
    have habv : a.val < b.val := hab
    omega
  have hdiff :
      positionsBeforeBoundary (boundaryBefore b) \
          positionsBeforeBoundary (boundaryAfter a) =
        openIntervalPositions a b := by
    ext i
    simp only [positionsBeforeBoundary, openIntervalPositions,
      Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt]
    change (i.val < b.val ∧ a.val + 1 ≤ i.val) ↔
      (a.val < i.val ∧ i.val < b.val)
    omega
  have hsum := Finset.sum_sdiff
    (f := fun i => nucleotideWeight (w i)) hsub
  rw [hdiff] at hsum
  change openIntervalBalance w a b +
      prefixBalanceBoundary w (boundaryAfter a) =
        prefixBalanceBoundary w (boundaryBefore b) at hsum
  omega

/-- Crossing one position adds exactly that position's weight. -/
theorem prefixBalanceBoundary_after_eq_before_add
    (w : Sequence n) (i : Fin n) :
    prefixBalanceBoundary w (boundaryAfter i) =
      prefixBalanceBoundary w (boundaryBefore i) + nucleotideWeight (w i) := by
  have h := closedIntervalBalance_eq_boundary_sub w (a := i) (b := i)
    (le_refl i)
  rw [closedIntervalBalance_self] at h
  omega

/-- For a zero-weight right endpoint, inclusive endpoint-balance difference
is exactly the strict-interior balance. -/
theorem openIntervalBalance_eq_prefix_sub_of_right_weight_zero
    (w : Sequence n) {a b : Fin n} (hab : a < b)
    (hb : nucleotideWeight (w b) = 0) :
    openIntervalBalance w a b = prefixBalanceAt w b - prefixBalanceAt w a := by
  change openIntervalBalance w a b =
    prefixBalanceBoundary w (boundaryAfter b) -
      prefixBalanceBoundary w (boundaryAfter a)
  rw [openIntervalBalance_eq_boundary_sub w hab,
    prefixBalanceBoundary_after_eq_before_add w b, hb]
  omega

theorem prefixBalanceAt_sub_eq_openIntervalBalance_of_endpoint_weights_zero
    (w : Sequence n) {a b : Fin n} (hab : a < b)
    (_ha : nucleotideWeight (w a) = 0)
    (hb : nucleotideWeight (w b) = 0) :
    prefixBalanceAt w b - prefixBalanceAt w a =
      openIntervalBalance w a b :=
  (openIntervalBalance_eq_prefix_sub_of_right_weight_zero w hab hb).symm

/-- A target pair is open at `k` exactly after its left endpoint and through
the boundary immediately before its right endpoint. -/
def openTargetPairsAtBoundary (T : SecondaryStructure n) (k : Fin (n + 1)) :
    Finset (PairedNode T) :=
  Finset.univ.filter fun v =>
    v.val.left.val < k.val ∧ k.val ≤ v.val.right.val

/-- A constructed target-unpaired letter has zero balance weight. -/
@[simp]
theorem nucleotideWeight_sequence_unpaired
    (χ : Coloring T) (hProper : ProperColoring χ)
    (u : UnpairedPosition T) :
    nucleotideWeight (sequenceOfProperColoring χ hProper u.val) = 0 := by
  simp

/-- A target left endpoint has exactly its coloring delta as weight. -/
theorem nucleotideWeight_sequence_left
    (χ : Coloring T) (hProper : ProperColoring χ)
    (v : PairedNode T) :
    nucleotideWeight (sequenceOfProperColoring χ hProper v.val.left) =
      Color.delta (χ v) := by
  cases h : χ v with
  | black => simp [sequenceOfProperColoring_black_left χ hProper v h]
  | white => simp [sequenceOfProperColoring_white_left χ hProper v h]
  | grey =>
      rcases sequenceOfProperColoring_grey_left χ hProper v h with hv | hv <;>
        simp [hv]

/-- A target right endpoint has the negated coloring delta as weight. -/
theorem nucleotideWeight_sequence_right
    (χ : Coloring T) (hProper : ProperColoring χ)
    (v : PairedNode T) :
    nucleotideWeight (sequenceOfProperColoring χ hProper v.val.right) =
      -Color.delta (χ v) := by
  rw [sequenceOfProperColoring_right_eq_comp_left, nucleotideWeight_comp,
    nucleotideWeight_sequence_left]

/-- The two endpoints of every target pair have net balance zero. -/
theorem targetPair_endpointBalance
    (χ : Coloring T) (hProper : ProperColoring χ)
    (v : PairedNode T) :
    nucleotideWeight (sequenceOfProperColoring χ hProper v.val.left) +
      nucleotideWeight (sequenceOfProperColoring χ hProper v.val.right) = 0 := by
  rw [nucleotideWeight_sequence_left, nucleotideWeight_sequence_right]
  omega

theorem openPairs_boundaryAfter_left (v : PairedNode T) :
    openTargetPairsAtBoundary T (boundaryAfter v.val.left) =
      insert v (pairedAncestors v) := by
  ext q
  rw [show q ∈ openTargetPairsAtBoundary T (boundaryAfter v.val.left) ↔
      (q.val.left.val < (boundaryAfter v.val.left).val ∧
        (boundaryAfter v.val.left).val ≤ q.val.right.val) by
      simp [openTargetPairsAtBoundary]]
  rw [show q ∈ insert v (pairedAncestors v) ↔
      (q = v ∨ PairedNode.StrictlyContains T q (Sum.inl v)) by
      simp [pairedAncestors]]
  change
    (q.val.left.val < v.val.left.val + 1 ∧
      v.val.left.val + 1 ≤ q.val.right.val) ↔
    (q = v ∨ PairedNode.StrictlyContains T q (Sum.inl v))
  constructor
  · intro hq
    have hbounds : q.val.left.val ≤ v.val.left.val ∧
        v.val.left.val < q.val.right.val := by omega
    rcases pairedNode_laminar T q v with hEq | hBefore | hAfter |
        hContains | hvContains
    · exact Or.inl hEq
    · change q.val.right.val < v.val.left.val at hBefore
      omega
    · change v.val.right.val < q.val.left.val at hAfter
      have hvord := v.val.ordered
      change v.val.left.val < v.val.right.val at hvord
      omega
    · exact Or.inr hContains
    · change v.val.left.val < q.val.left.val ∧
          q.val.right.val < v.val.right.val at hvContains
      omega
  · intro hq
    rcases hq with hEq | hContains
    · subst q
      have hvord := v.val.ordered
      change v.val.left.val < v.val.right.val at hvord
      omega
    · change q.val.left.val < v.val.left.val ∧
          v.val.right.val < q.val.right.val at hContains
      have hvord := v.val.ordered
      change v.val.left.val < v.val.right.val at hvord
      omega

theorem openPairs_boundaryAfter_right (v : PairedNode T) :
    openTargetPairsAtBoundary T (boundaryAfter v.val.right) =
      pairedAncestors v := by
  ext q
  rw [show q ∈ openTargetPairsAtBoundary T (boundaryAfter v.val.right) ↔
      (q.val.left.val < (boundaryAfter v.val.right).val ∧
        (boundaryAfter v.val.right).val ≤ q.val.right.val) by
      simp [openTargetPairsAtBoundary]]
  rw [show q ∈ pairedAncestors v ↔
      PairedNode.StrictlyContains T q (Sum.inl v) by
      simp [pairedAncestors]]
  change
    (q.val.left.val < v.val.right.val + 1 ∧
      v.val.right.val + 1 ≤ q.val.right.val) ↔
    PairedNode.StrictlyContains T q (Sum.inl v)
  constructor
  · intro hq
    have hbounds : q.val.left.val ≤ v.val.right.val ∧
        v.val.right.val < q.val.right.val := by omega
    rcases pairedNode_laminar T q v with hEq | hBefore | hAfter |
        hContains | hvContains
    · subst q
      omega
    · change q.val.right.val < v.val.left.val at hBefore
      have hvord := v.val.ordered
      change v.val.left.val < v.val.right.val at hvord
      omega
    · change v.val.right.val < q.val.left.val at hAfter
      omega
    · exact hContains
    · change v.val.left.val < q.val.left.val ∧
          q.val.right.val < v.val.right.val at hvContains
      omega
  · intro hContains
    change q.val.left.val < v.val.left.val ∧
        v.val.right.val < q.val.right.val at hContains
    have hvord := v.val.ordered
    change v.val.left.val < v.val.right.val at hvord
    omega

theorem openPairs_boundaryBefore_left (v : PairedNode T) :
    openTargetPairsAtBoundary T (boundaryBefore v.val.left) =
      pairedAncestors v := by
  ext q
  rw [show q ∈ openTargetPairsAtBoundary T (boundaryBefore v.val.left) ↔
      (q.val.left.val < (boundaryBefore v.val.left).val ∧
        (boundaryBefore v.val.left).val ≤ q.val.right.val) by
      simp [openTargetPairsAtBoundary]]
  rw [show q ∈ pairedAncestors v ↔
      PairedNode.StrictlyContains T q (Sum.inl v) by
      simp [pairedAncestors]]
  change
    (q.val.left.val < v.val.left.val ∧
      v.val.left.val ≤ q.val.right.val) ↔
    PairedNode.StrictlyContains T q (Sum.inl v)
  constructor
  · intro hq
    rcases pairedNode_laminar T q v with hEq | hBefore | hAfter |
        hContains | hvContains
    · subst q
      omega
    · change q.val.right.val < v.val.left.val at hBefore
      omega
    · change v.val.right.val < q.val.left.val at hAfter
      have hvord := v.val.ordered
      change v.val.left.val < v.val.right.val at hvord
      omega
    · exact hContains
    · change v.val.left.val < q.val.left.val ∧
          q.val.right.val < v.val.right.val at hvContains
      omega
  · intro hContains
    change q.val.left.val < v.val.left.val ∧
        v.val.right.val < q.val.right.val at hContains
    have hvord := v.val.ordered
    change v.val.left.val < v.val.right.val at hvord
    omega

theorem openPairs_boundaryAfter_unpaired (u : UnpairedPosition T) :
    openTargetPairsAtBoundary T (boundaryAfter u.val) =
      enclosingPairs T (Sum.inr u) := by
  ext q
  rw [show q ∈ openTargetPairsAtBoundary T (boundaryAfter u.val) ↔
      (q.val.left.val < (boundaryAfter u.val).val ∧
        (boundaryAfter u.val).val ≤ q.val.right.val) by
      simp [openTargetPairsAtBoundary]]
  rw [show q ∈ enclosingPairs T (Sum.inr u) ↔
      PairedNode.StrictlyContains T q (Sum.inr u) by
      simp [enclosingPairs]]
  change
    (q.val.left.val < u.val.val + 1 ∧
      u.val.val + 1 ≤ q.val.right.val) ↔
    (q.val.left < u.val ∧ u.val < q.val.right)
  constructor
  · intro hq
    have hleftLe : q.val.left.val ≤ u.val.val := by omega
    have hleftNe : q.val.left ≠ u.val := by
      intro heq
      exact u.property ⟨q.val, q.property, Or.inl heq.symm⟩
    have hleft : q.val.left < u.val := lt_of_le_of_ne hleftLe hleftNe
    exact ⟨hleft, by omega⟩
  · intro hq
    change q.val.left.val < u.val.val ∧
      u.val.val < q.val.right.val at hq
    omega

/-- Boundary balance is exactly the sum of coloring deltas over the target
pairs open at that boundary. -/
theorem prefixBalanceBoundary_eq_openPairSum
    (χ : Coloring T) (hProper : ProperColoring χ) (k : Fin (n + 1)) :
    prefixBalanceBoundary (sequenceOfProperColoring χ hProper) k =
      ∑ v ∈ openTargetPairsAtBoundary T k, Color.delta (χ v) := by
  rw [prefixBalanceBoundary, balanceOn, positionsBeforeBoundary,
    Finset.sum_filter]
  let f : Fin n → Int := fun i =>
    if i.val < k.val then
      nucleotideWeight (sequenceOfProperColoring χ hProper i)
    else 0
  change (∑ i : Fin n, f i) = _
  have hRole :
      (∑ i : Fin n, f i) =
        ∑ r : PositionRole T, f (positionOfRole T r) := by
    exact (Fintype.sum_equiv (positionRoleEquiv T)
      (fun r => f (positionOfRole T r)) f (fun _ => rfl)).symm
  rw [hRole, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hUnpaired :
      (∑ u : UnpairedPosition T, f (positionOfRole T (Sum.inl u))) = 0 := by
    apply Finset.sum_eq_zero
    intro u _hu
    simp [f, positionOfRole]
  rw [hUnpaired, zero_add]
  have hSide (v : PairedNode T) :
      (∑ side : EndpointSide,
        f (positionOfRole T (Sum.inr (v, side)))) =
        (if v.val.left.val < k.val then Color.delta (χ v) else 0) +
          (if v.val.right.val < k.val then -Color.delta (χ v) else 0) := by
    rw [show (Finset.univ : Finset EndpointSide) =
        {EndpointSide.left, EndpointSide.right} by
      ext side
      cases side <;> simp]
    have hne : EndpointSide.left ∉
        ({EndpointSide.right} : Finset EndpointSide) := by simp
    rw [Finset.sum_insert hne, Finset.sum_singleton]
    change
      (if v.val.left.val < k.val then
        nucleotideWeight (sequenceOfProperColoring χ hProper v.val.left)
      else 0) +
      (if v.val.right.val < k.val then
        nucleotideWeight (sequenceOfProperColoring χ hProper v.val.right)
      else 0) = _
    rw [nucleotideWeight_sequence_left, nucleotideWeight_sequence_right]
  simp_rw [hSide]
  rw [openTargetPairsAtBoundary, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _hv
  have hvord := v.val.ordered
  change v.val.left.val < v.val.right.val at hvord
  by_cases hl : v.val.left.val < k.val
  · by_cases hr : v.val.right.val < k.val
    · have hnot : ¬ k.val ≤ v.val.right.val := Nat.not_le.mpr hr
      simp [hl, hr, hnot]
    · have hle : k.val ≤ v.val.right.val := Nat.le_of_not_gt hr
      simp [hl, hr, hle]
  · have hr : ¬ v.val.right.val < k.val := by
      intro hright
      exact hl (lt_trans hvord hright)
    simp [hl, hr]

/-- Every complete target interval-tree subtree has net balance zero.  The
boundary proof identifies the same strict ancestors immediately before its
left endpoint and immediately after its right endpoint. -/
theorem completeSubtreeBalance
    (χ : Coloring T) (hProper : ProperColoring χ) (v : PairedNode T) :
    closedIntervalBalance (sequenceOfProperColoring χ hProper)
      v.val.left v.val.right = 0 := by
  rw [closedIntervalBalance_eq_boundary_sub
      (sequenceOfProperColoring χ hProper) (le_of_lt v.val.ordered),
    prefixBalanceBoundary_eq_openPairSum,
    prefixBalanceBoundary_eq_openPairSum,
    openPairs_boundaryAfter_right, openPairs_boundaryBefore_left]
  omega

/-- In particular, a complete paired subtree preceding a sibling contributes
zero to the running prefix balance. -/
theorem completedSiblingBalance
    (χ : Coloring T) (hProper : ProperColoring χ)
    (p : PairedOrRootNode T) {earlier later : PairedNode T}
    (_hearlier : earlier ∈ pairedChildren T p)
    (_hlater : later ∈ pairedChildren T p)
    (_horder : earlier < later) :
    closedIntervalBalance (sequenceOfProperColoring χ hProper)
      earlier.val.left earlier.val.right = 0 :=
  completeSubtreeBalance χ hProper earlier

/-- Sum of deltas over every pair enclosing an unpaired position is exactly
the existing parent-based `unpairedLevel`. -/
theorem enclosingPairSum_eq_unpairedLevel
    (χ : Coloring T) (u : UnpairedPosition T) :
    (∑ p ∈ enclosingPairs T (Sum.inr u), Color.delta (χ p)) =
      unpairedLevel χ u := by
  cases hp : parent T (Sum.inr u) with
  | none =>
      have hempty : enclosingPairs T (Sum.inr u) = ∅ := by
        ext q
        rw [show q ∈ enclosingPairs T (Sum.inr u) ↔
            PairedNode.StrictlyContains T q (Sum.inr u) by
          simp [enclosingPairs]]
        constructor
        · intro hq
          exact False.elim
            (((parent_eq_root_iff T (Sum.inr u)).1 hp q) hq)
        · intro hq
          simp at hq
      rw [hempty]
      simp [unpairedLevel, interfaceLevel, hp]
  | some p =>
      have henclosing :
          enclosingPairs T (Sum.inr u) = insert p (pairedAncestors p) := by
        ext q
        rw [show q ∈ enclosingPairs T (Sum.inr u) ↔
            PairedNode.StrictlyContains T q (Sum.inr u) by
          simp [enclosingPairs]]
        rw [show q ∈ insert p (pairedAncestors p) ↔
            (q = p ∨ PairedNode.StrictlyContains T q (Sum.inl p)) by
          simp [pairedAncestors]]
        constructor
        · intro hq
          exact (parent_pair_smallest T hp).2 q hq
        · intro hq
          rcases hq with rfl | hq
          · exact parent_pair_contains T hp
          · have hpu := parent_pair_contains T hp
            simp only [PairedNode.StrictlyContains] at hq hpu ⊢
            omega
      have hpnot : p ∉ pairedAncestors p := by
        intro hmem
        have hstrict : PairedNode.StrictlyContains T p (Sum.inl p) := by
          simpa [pairedAncestors] using hmem
        simp only [PairedNode.StrictlyContains] at hstrict
        omega
      rw [henclosing, Finset.sum_insert hpnot]
      simp only [unpairedLevel, interfaceLevel, hp, pairedLevel, entryLevel]
      omega

/-- Manuscript Lemma 20 at a paired left endpoint. -/
theorem prefixBalanceAt_pairedLeft_eq_pairedLevel
    (χ : Coloring T) (hProper : ProperColoring χ) (v : PairedNode T) :
    prefixBalanceAt (sequenceOfProperColoring χ hProper) v.val.left =
      pairedLevel χ v := by
  rw [prefixBalanceAt, prefixBalanceBoundary_eq_openPairSum,
    openPairs_boundaryAfter_left]
  have hvnot : v ∉ pairedAncestors v := by
    intro hv
    have hs : PairedNode.StrictlyContains T v (Sum.inl v) := by
      simpa [pairedAncestors] using hv
    simp only [PairedNode.StrictlyContains] at hs
    omega
  rw [Finset.sum_insert hvnot]
  simp only [pairedLevel, entryLevel]
  omega

/-- Manuscript Lemma 20 at a target-unpaired position. -/
theorem prefixBalanceAt_unpaired_eq_unpairedLevel
    (χ : Coloring T) (hProper : ProperColoring χ)
    (u : UnpairedPosition T) :
    prefixBalanceAt (sequenceOfProperColoring χ hProper) u.val =
      unpairedLevel χ u := by
  rw [prefixBalanceAt, prefixBalanceBoundary_eq_openPairSum,
    openPairs_boundaryAfter_unpaired]
  exact enclosingPairSum_eq_unpairedLevel χ u

/-- At a grey pair, its right endpoint, left endpoint, and exact tree level all
have the same inclusive prefix balance. -/
theorem prefixBalanceAt_greyRight_eq
    (χ : Coloring T) (hProper : ProperColoring χ) (v : PairedNode T)
    (hv : χ v = Color.grey) :
    prefixBalanceAt (sequenceOfProperColoring χ hProper) v.val.right =
      prefixBalanceAt (sequenceOfProperColoring χ hProper) v.val.left ∧
    prefixBalanceAt (sequenceOfProperColoring χ hProper) v.val.left =
      pairedLevel χ v := by
  have hleft := prefixBalanceAt_pairedLeft_eq_pairedLevel χ hProper v
  have hright :
      prefixBalanceAt (sequenceOfProperColoring χ hProper) v.val.right =
        pairedLevel χ v := by
    rw [prefixBalanceAt, prefixBalanceBoundary_eq_openPairSum,
      openPairs_boundaryAfter_right]
    simp [pairedLevel, entryLevel, hv]
  exact ⟨hright.trans hleft.symm, hleft⟩

end RNA
