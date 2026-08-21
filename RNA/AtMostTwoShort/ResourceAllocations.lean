module

public import RNA.AtMostTwoShort.Interface
public import RNA.SubtreeConstruction

@[expose] public section

set_option autoImplicit false

/-!
# Resource-aware allocations on actual loop-child slots

The old exact-one allocation structures remain unchanged.  This module
installs the F/Q resource rows on the actual `Fin`-indexed child list.  A
two-positive row is installed by an explicit permutation sending the two
designated actual slots to table slots zero and one; no overwrite map is used.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-! ## Two designated actual slots -/

/-- A permutation sending `i` to slot zero and `j` to slot one. -/
def twoSlotPerm {d : Nat} (i j : Fin d) (_hij : i ≠ j) (hd : 2 ≤ d) :
    Equiv.Perm (Fin d) :=
  let zero : Fin d := ⟨0, by omega⟩
  let one : Fin d := ⟨1, by omega⟩
  let first := Equiv.swap i zero
  first.trans (Equiv.swap (first j) one)

theorem twoSlotPerm_left {d : Nat} (i j : Fin d) (hij : i ≠ j)
    (hd : 2 ≤ d) :
    twoSlotPerm i j hij hd i = ⟨0, by omega⟩ := by
  let zero : Fin d := ⟨0, by omega⟩
  let one : Fin d := ⟨1, by omega⟩
  let first := Equiv.swap i zero
  have hfirsti : first i = zero := Equiv.swap_apply_left i zero
  have hfirstij : first i ≠ first j := first.injective.ne hij
  have hzeroj : zero ≠ first j := by simpa [hfirsti] using hfirstij
  have hzeroone : zero ≠ one := Fin.ne_of_lt (by
    change 0 < 1
    omega)
  change (Equiv.swap (first j) one) (first i) = zero
  rw [hfirsti, Equiv.swap_apply_of_ne_of_ne hzeroj hzeroone]

theorem twoSlotPerm_right {d : Nat} (i j : Fin d) (hij : i ≠ j)
    (hd : 2 ≤ d) :
    twoSlotPerm i j hij hd j = ⟨1, by omega⟩ := by
  let zero : Fin d := ⟨0, by omega⟩
  let one : Fin d := ⟨1, by omega⟩
  let first := Equiv.swap i zero
  change (Equiv.swap (first j) one) (first j) = one
  exact Equiv.swap_apply_left (first j) one

/-- The `r = 2` M table: both positive slots are grey; at degree three the
remaining short-free slot receives the non-grey closing colour. -/
def twoPositiveMBasePorts (a : Color) :
    (d : MArity) → PortAssignment d.count
  | .two => ![Color.grey, Color.grey]
  | .three => ![Color.grey, Color.grey, a]

def twoPositiveMPortsAt (a : Color) (d : MArity)
    (i j : Fin d.count) (hij : i ≠ j) : PortAssignment d.count :=
  (twoPositiveMBasePorts a d).reindex
    (twoSlotPerm i j hij (by cases d <;> decide))

/-- Exact exposed row underlying the two-positive M allocation. -/
def twoPositiveMExposure : Color → MArity → Multiset Color
  | a, .two => {a.inv, Color.grey, Color.grey}
  | a, .three => {a.inv, Color.grey, Color.grey, a}

theorem twoPositiveMExposure_eq (a : Color) (d : MArity)
    (i j : Fin d.count) (hij : i ≠ j) :
    loopPortExposure a (twoPositiveMPortsAt a d i j hij) =
      twoPositiveMExposure a d := by
  unfold twoPositiveMPortsAt
  rw [loopPortExposure, portMultiset_reindex]
  cases a <;> cases d <;> decide

@[simp] theorem twoPositiveMPortsAt_left (a : Color) (d : MArity)
    (i j : Fin d.count) (hij : i ≠ j) :
    twoPositiveMPortsAt a d i j hij i = Color.grey := by
  change twoPositiveMBasePorts a d
    (twoSlotPerm i j hij (by cases d <;> decide) i) = Color.grey
  rw [twoSlotPerm_left]
  cases d <;> rfl

@[simp] theorem twoPositiveMPortsAt_right (a : Color) (d : MArity)
    (i j : Fin d.count) (hij : i ≠ j) :
    twoPositiveMPortsAt a d i j hij j = Color.grey := by
  change twoPositiveMBasePorts a d
    (twoSlotPerm i j hij (by cases d <;> decide) j) = Color.grey
  rw [twoSlotPerm_right]
  cases d <;> rfl

theorem twoPositiveMPortsAt_other_three (a : Color)
    (i j k : Fin MArity.three.count) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    twoPositiveMPortsAt a .three i j hij k = a := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all only [ne_eq, Fin.mk.injEq, one_ne_zero, zero_ne_one,
      not_false_eq_true, not_true_eq_false, twoPositiveMPortsAt,
      PortAssignment.reindex, twoPositiveMBasePorts, twoSlotPerm,
      Equiv.swap_self, Equiv.refl_apply, Equiv.refl_trans,
      Equiv.trans_refl, Equiv.coe_refl, Equiv.coe_trans,
      Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.swap_apply_def, reduceIte] <;>
    first | exact (hij (Fin.ext (by decide))).elim | rfl

theorem twoPositiveMExposure_proper (a : Color) (ha : a.NonGrey)
    (d : MArity) (i j : Fin d.count) (hij : i ≠ j) :
    ProperExposure (loopPortExposure a
      (twoPositiveMPortsAt a d i j hij)) := by
  unfold twoPositiveMPortsAt
  rw [loopPortExposure, portMultiset_reindex]
  rcases (Color.nonGrey_iff a).1 ha with rfl | rfl <;> cases d <;> decide

/-! ## Installation on the actual ordered children -/

noncomputable def onePositiveMActualPorts (T : SecondaryStructure n)
    (H : MaximalHelix T)
    (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some H.terminalNode) = d.count)
    (positive : Fin (pairedChildCount T (some H.terminalNode))) :
    ChildPortAssignment T (some H.terminalNode) :=
  installPortRow T (some H.terminalNode)
    (designatedMPortsAt a d (finCongr hcount positive)) hcount

@[simp] theorem onePositiveMActualPorts_positive
    (T : SecondaryStructure n) (H : MaximalHelix T)
    (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some H.terminalNode) = d.count)
    (positive : Fin (pairedChildCount T (some H.terminalNode))) :
    onePositiveMActualPorts T H a d hcount positive positive = Color.grey := by
  simp [onePositiveMActualPorts, installPortRow, PortAssignment.reindex]

theorem onePositiveMActualExposure_proper
    (T : SecondaryStructure n) (H : MaximalHelix T)
    (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some H.terminalNode) = d.count)
    (positive : Fin (pairedChildCount T (some H.terminalNode))) :
    ProperExposure (loopPortExposure a
      (onePositiveMActualPorts T H a d hcount positive)) := by
  unfold onePositiveMActualPorts
  rw [loopPortExposure, installPortRow_multiset]
  exact designatedMExposure_proper a d _

/-- The `r = 1` row installed on an actual positive-short child has exactly
the designated table exposure, independently of that child's ordered slot. -/
theorem onePositiveMActualExposure_eq
    (T : SecondaryStructure n) (H : MaximalHelix T)
    (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some H.terminalNode) = d.count)
    (positive : Fin (pairedChildCount T (some H.terminalNode))) :
    loopPortExposure a
      (onePositiveMActualPorts T H a d hcount positive) =
        designatedMExposure a d := by
  unfold onePositiveMActualPorts
  rw [loopPortExposure, installPortRow_multiset]
  exact designatedMExposure_eq a d _

noncomputable def twoPositiveMActualPorts (T : SecondaryStructure n)
    (H : MaximalHelix T)
    (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some H.terminalNode) = d.count)
    (i j : Fin (pairedChildCount T (some H.terminalNode))) (hij : i ≠ j) :
    ChildPortAssignment T (some H.terminalNode) :=
  installPortRow T (some H.terminalNode)
    (twoPositiveMPortsAt a d (finCongr hcount i) (finCongr hcount j)
      ((finCongr hcount).injective.ne hij)) hcount

@[simp] theorem twoPositiveMActualPorts_left
    (T : SecondaryStructure n) (H : MaximalHelix T)
    (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some H.terminalNode) = d.count)
    (i j : Fin (pairedChildCount T (some H.terminalNode))) (hij : i ≠ j) :
    twoPositiveMActualPorts T H a d hcount i j hij i = Color.grey := by
  simp [twoPositiveMActualPorts, installPortRow, PortAssignment.reindex]

@[simp] theorem twoPositiveMActualPorts_right
    (T : SecondaryStructure n) (H : MaximalHelix T)
    (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some H.terminalNode) = d.count)
    (i j : Fin (pairedChildCount T (some H.terminalNode))) (hij : i ≠ j) :
    twoPositiveMActualPorts T H a d hcount i j hij j = Color.grey := by
  simp [twoPositiveMActualPorts, installPortRow, PortAssignment.reindex]

theorem twoPositiveMActualExposure_proper
    (T : SecondaryStructure n) (H : MaximalHelix T)
    (a : Color) (ha : a.NonGrey) (d : MArity)
    (hcount : pairedChildCount T (some H.terminalNode) = d.count)
    (i j : Fin (pairedChildCount T (some H.terminalNode))) (hij : i ≠ j) :
    ProperExposure (loopPortExposure a
      (twoPositiveMActualPorts T H a d hcount i j hij)) := by
  unfold twoPositiveMActualPorts
  rw [loopPortExposure, installPortRow_multiset]
  exact twoPositiveMExposure_proper a ha d _ _ _

theorem twoPositiveMActualExposure_eq
    (T : SecondaryStructure n) (H : MaximalHelix T)
    (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some H.terminalNode) = d.count)
    (i j : Fin (pairedChildCount T (some H.terminalNode))) (hij : i ≠ j) :
    loopPortExposure a
      (twoPositiveMActualPorts T H a d hcount i j hij) =
        twoPositiveMExposure a d := by
  unfold twoPositiveMActualPorts
  rw [loopPortExposure, installPortRow_multiset]
  exact twoPositiveMExposure_eq a d _ _ _

theorem twoPositiveMActualPorts_other_three
    (T : SecondaryStructure n) (H : MaximalHelix T) (a : Color)
    (hcount : pairedChildCount T (some H.terminalNode) =
      MArity.three.count)
    (i j k : Fin (pairedChildCount T (some H.terminalNode))) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    twoPositiveMActualPorts T H a .three hcount i j hij k = a := by
  apply twoPositiveMPortsAt_other_three
  · exact (finCongr hcount).injective.ne hij
  · exact (finCongr hcount).injective.ne hki
  · exact (finCongr hcount).injective.ne hkj

/-! ## Proof-bearing complete allocation -/

/-- Resource-aware allocation at the terminal loop of `H`. -/
structure ResourceLoopAllocation (T : SecondaryStructure n)
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (e : EndpointType) (a : Color) (xi : Parity) where
  entry : Parity
  ports : ChildPortAssignment T (some H.terminalNode)
  proper : ProperExposure (loopPortExposure a ports)
  requiredOutgoing : ∀ i, RequiredInterface T (outgoingHelix T H i)
    xi entry (ports i)
  eEntry : e = .E → entry = xi
  lEntry : e = .L → entry = xi
  mEntry : e = .M → entry = xi.opposite
  supportCardLeTwo : (loopShortSupport T H).card ≤ 2
  positiveGreyAtM : e = .M → ∀ i ∈ loopShortSupport T H,
    ports i = Color.grey
  shortFreeInF : ∀ i ∉ loopShortSupport T H, InF xi entry (ports i)
  twoSupportClosingNonGrey : e = .M →
    (loopShortSupport T H).card = 2 → a.NonGrey
  twoSupportIncomingLong : (loopShortSupport T H).card = 2 → 3 ≤ H.length
  twoSupportExactExposure : e = .M →
    (loopShortSupport T H).card = 2 →
      (pairedChildCount T (some H.terminalNode) = 2 ∧
        loopPortExposure a ports = twoPositiveMExposure a .two) ∨
      (pairedChildCount T (some H.terminalNode) = 3 ∧
        loopPortExposure a ports = twoPositiveMExposure a .three)
  twoSupportThirdClosing : e = .M →
    (loopShortSupport T H).card = 2 →
    ∀ _hthree : pairedChildCount T (some H.terminalNode) = 3,
      ∀ i ∉ loopShortSupport T H, ports i = a

theorem requiredAtXi_of_nonGrey
    (H : MaximalHelix T) (xi : Parity) (first : Color)
    (hfirst : first.NonGrey) :
    RequiredInterface T H xi xi first := by
  by_cases hzero : shortHelixSubtreeCount T H = 0
  · exact (requiredInterface_of_count_eq_zero H xi xi first hzero).2
      ((inF_xi_iff_nonGrey xi first).2 hfirst)
  · exact (requiredInterface_of_count_ne_zero H xi xi first hzero).2
      ((inQ_xi_iff_nonGrey xi first).2 hfirst)

theorem support_card_le_childCount (H : MaximalHelix T) :
    (loopShortSupport T H).card ≤
      pairedChildCount T (some H.terminalNode) := by
  simpa using Finset.card_le_univ (loopShortSupport T H)

/-- Complete E/L/M allocation on actual outgoing slots.  The second closing
premise is exactly the strengthened-transfer fact needed only by the `M,r=2`
branch. -/
noncomputable def completeResourceLoopAllocation
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (e : EndpointType) (he : HasEndpointType H.terminalNode e)
    (a : Color) (xi : Parity)
    (hLclosing : e = .L → a.NonGrey)
    (hTwoClosing : e = .M →
      (loopShortSupport T H).card = 2 → a.NonGrey) :
    ResourceLoopAllocation T hK H e a xi := by
  have hsupportLe := loopShortSupport_card_le_two hK H
  have hlong := loopShortSupport_card_eq_two_length_at_least_three hK H
  cases e with
  | E =>
      change IsEEndpoint H.terminalNode at he
      have hzero : pairedChildCount T (some H.terminalNode) = 0 := he.2
      let A := installPortRow T (some H.terminalNode) noPorts hzero
      have hsupportZero : (loopShortSupport T H).card = 0 := by
        have hle := support_card_le_childCount H
        omega
      refine {
        entry := xi
        ports := A
        proper := ?_
        requiredOutgoing := ?_
        eEntry := fun _ => rfl
        lEntry := ?_
        mEntry := ?_
        supportCardLeTwo := hsupportLe
        positiveGreyAtM := ?_
        shortFreeInF := ?_
        twoSupportClosingNonGrey := hTwoClosing
        twoSupportIncomingLong := hlong
        twoSupportExactExposure := ?_
        twoSupportThirdClosing := ?_ }
      · unfold A
        rw [loopPortExposure, installPortRow_multiset]
        exact eExposure_proper a
      · intro i
        exact Fin.elim0 (finCongr hzero i)
      · intro h
        simp at h
      · intro h
        simp at h
      · intro h
        simp at h
      · intro i
        exact Fin.elim0 (finCongr hzero i)
      · intro _ hcard
        omega
      · intro _ hcard
        omega
  | L =>
      change IsLEndpoint H.terminalNode at he
      have ha : a.NonGrey := hLclosing rfl
      by_cases hzero : pairedChildCount T (some H.terminalNode) = 0
      · let A := installPortRow T (some H.terminalNode) noPorts hzero
        have hsupportZero : (loopShortSupport T H).card = 0 := by
          have hle := support_card_le_childCount H
          omega
        refine {
          entry := xi
          ports := A
          proper := ?_
          requiredOutgoing := ?_
          eEntry := ?_
          lEntry := fun _ => rfl
          mEntry := ?_
          supportCardLeTwo := hsupportLe
          positiveGreyAtM := ?_
          shortFreeInF := ?_
          twoSupportClosingNonGrey := hTwoClosing
          twoSupportIncomingLong := hlong
          twoSupportExactExposure := ?_
          twoSupportThirdClosing := ?_ }
        · unfold A
          rw [loopPortExposure, installPortRow_multiset]
          exact lZeroExposure_proper a ha
        · intro i
          exact Fin.elim0 (finCongr hzero i)
        · intro h
          simp at h
        · intro h
          simp at h
        · intro h
          simp at h
        · intro i
          exact Fin.elim0 (finCongr hzero i)
        · intro _ hcard
          omega
        · intro _ hcard
          omega
      · have hone : pairedChildCount T (some H.terminalNode) = 1 := by
          rcases he.2 with hz | ho
          · exact False.elim (hzero hz)
          · exact ho
        let A := installPortRow T (some H.terminalNode) (lOnePort a) hone
        have hport (i : Fin (pairedChildCount T (some H.terminalNode))) :
            A i = a := by
          have hi : finCongr hone i = (0 : Fin 1) := Subsingleton.elim _ _
          change lOnePort a (finCongr hone i) = a
          rw [hi]
          rfl
        refine {
          entry := xi
          ports := A
          proper := ?_
          requiredOutgoing := ?_
          eEntry := ?_
          lEntry := fun _ => rfl
          mEntry := ?_
          supportCardLeTwo := hsupportLe
          positiveGreyAtM := ?_
          shortFreeInF := ?_
          twoSupportClosingNonGrey := hTwoClosing
          twoSupportIncomingLong := hlong
          twoSupportExactExposure := ?_
          twoSupportThirdClosing := ?_ }
        · unfold A
          rw [loopPortExposure, installPortRow_multiset]
          exact lOneExposure_proper a ha
        · intro i
          rw [hport i]
          exact requiredAtXi_of_nonGrey (outgoingHelix T H i) xi a ha
        · intro h
          simp at h
        · intro h
          simp at h
        · intro h
          simp at h
        · intro i _
          rw [hport i]
          exact (inF_xi_iff_nonGrey xi a).2 ha
        · intro _ hcard
          have hle := support_card_le_childCount H
          omega
        · intro _ hcard
          have hle := support_card_le_childCount H
          omega
  | M =>
      change IsMEndpoint H.terminalNode at he
      have build (d : MArity)
          (hcount : pairedChildCount T (some H.terminalNode) = d.count) :
          ResourceLoopAllocation T hK H .M a xi := by
        let support := loopShortSupport T H
        by_cases hcardZero : support.card = 0
        · let A := ordinaryMActualPorts T H.terminalNode a d hcount
          have hsupportEmpty : support = ∅ := Finset.card_eq_zero.mp hcardZero
          refine {
            entry := xi.opposite
            ports := A
            proper := ordinaryMActualExposure_proper T H.terminalNode a d hcount
            requiredOutgoing := ?_
            eEntry := ?_
            lEntry := ?_
            mEntry := fun _ => rfl
            supportCardLeTwo := hsupportLe
            positiveGreyAtM := ?_
            shortFreeInF := ?_
            twoSupportClosingNonGrey := hTwoClosing
            twoSupportIncomingLong := hlong
            twoSupportExactExposure := ?_
            twoSupportThirdClosing := ?_ }
          · intro i
            have hzeroCount : shortHelixSubtreeCount T
                (outgoingHelix T H i) = 0 :=
              (not_mem_loopShortSupport_iff_count_eq_zero H i).1 (by
                simp [support, hsupportEmpty])
            exact (requiredInterface_of_count_eq_zero
              (outgoingHelix T H i) xi xi.opposite (A i) hzeroCount).2
                (inF_eta xi (A i))
          · intro h
            simp at h
          · intro h
            simp at h
          · intro _ i hi
            change i ∈ support at hi
            rw [hsupportEmpty] at hi
            simp at hi
          · intro i _
            exact inF_eta xi (A i)
          · intro _ hcard
            change support.card = 2 at hcard
            omega
          · intro _ hcard _ _ _
            change support.card = 2 at hcard
            omega
        · by_cases hcardOne : support.card = 1
          · let k : Fin (pairedChildCount T (some H.terminalNode)) :=
              Classical.choose (Finset.card_eq_one.mp hcardOne)
            have hsupport : support = {k} :=
              Classical.choose_spec (Finset.card_eq_one.mp hcardOne)
            let A := onePositiveMActualPorts T H a d hcount k
            have hpositive (i : Fin (pairedChildCount T
                (some H.terminalNode))) (hi : i ∈ support) : A i = Color.grey := by
              have hik : i = k := by simpa [hsupport] using hi
              subst i
              exact onePositiveMActualPorts_positive T H a d hcount k
            refine {
              entry := xi.opposite
              ports := A
              proper := onePositiveMActualExposure_proper T H a d hcount k
              requiredOutgoing := ?_
              eEntry := ?_
              lEntry := ?_
              mEntry := fun _ => rfl
              supportCardLeTwo := hsupportLe
              positiveGreyAtM := fun _ i hi => hpositive i hi
              shortFreeInF := ?_
              twoSupportClosingNonGrey := hTwoClosing
              twoSupportIncomingLong := hlong
              twoSupportExactExposure := ?_
              twoSupportThirdClosing := ?_ }
            · intro i
              by_cases hi : i ∈ support
              · have hpos := (mem_loopShortSupport_iff H i).1 hi
                rw [hpositive i hi]
                exact (requiredInterface_of_count_pos
                  (outgoingHelix T H i) xi xi.opposite Color.grey hpos).2
                    (inQ_eta_grey xi)
              · have hz :=
                  (not_mem_loopShortSupport_iff_count_eq_zero H i).1 hi
                exact (requiredInterface_of_count_eq_zero
                  (outgoingHelix T H i) xi xi.opposite (A i) hz).2
                    (inF_eta xi (A i))
            · intro h
              simp at h
            · intro h
              simp at h
            · intro i _
              exact inF_eta xi (A i)
            · intro _ hcard
              change support.card = 2 at hcard
              omega
            · intro _ hcard _ _ _
              change support.card = 2 at hcard
              omega
          · have hsupportLe' : support.card ≤ 2 := by
              simpa [support] using hsupportLe
            have hcardTwo : support.card = 2 := by omega
            let k : Fin (pairedChildCount T (some H.terminalNode)) :=
              Classical.choose (Finset.card_eq_two.mp hcardTwo)
            let l : Fin (pairedChildCount T (some H.terminalNode)) :=
              Classical.choose (Classical.choose_spec
                (Finset.card_eq_two.mp hcardTwo))
            have hkl : k ≠ l := (Classical.choose_spec (Classical.choose_spec
              (Finset.card_eq_two.mp hcardTwo))).1
            have hsupport : support = {k, l} :=
              (Classical.choose_spec (Classical.choose_spec
                (Finset.card_eq_two.mp hcardTwo))).2
            have ha : a.NonGrey := hTwoClosing rfl (by simpa [support])
            let A := twoPositiveMActualPorts T H a d hcount k l hkl
            have hpositive (i : Fin (pairedChildCount T
                (some H.terminalNode))) (hi : i ∈ support) : A i = Color.grey := by
              have hik : i = k ∨ i = l := by simpa [hsupport] using hi
              rcases hik with rfl | rfl
              · exact twoPositiveMActualPorts_left T H a d hcount k l hkl
              · exact twoPositiveMActualPorts_right T H a d hcount k l hkl
            refine {
              entry := xi.opposite
              ports := A
              proper := twoPositiveMActualExposure_proper T H a ha d hcount k l hkl
              requiredOutgoing := ?_
              eEntry := ?_
              lEntry := ?_
              mEntry := fun _ => rfl
              supportCardLeTwo := hsupportLe
              positiveGreyAtM := fun _ i hi => hpositive i hi
              shortFreeInF := ?_
              twoSupportClosingNonGrey := hTwoClosing
              twoSupportIncomingLong := hlong
              twoSupportExactExposure := ?_
              twoSupportThirdClosing := ?_ }
            · intro i
              by_cases hi : i ∈ support
              · have hpos := (mem_loopShortSupport_iff H i).1 hi
                rw [hpositive i hi]
                exact (requiredInterface_of_count_pos
                  (outgoingHelix T H i) xi xi.opposite Color.grey hpos).2
                    (inQ_eta_grey xi)
              · have hz :=
                  (not_mem_loopShortSupport_iff_count_eq_zero H i).1 hi
                exact (requiredInterface_of_count_eq_zero
                  (outgoingHelix T H i) xi xi.opposite (A i) hz).2
                    (inF_eta xi (A i))
            · intro h
              simp at h
            · intro h
              simp at h
            · intro i _
              exact inF_eta xi (A i)
            · intro _ _
              cases d with
              | two =>
                  exact Or.inl ⟨hcount,
                    twoPositiveMActualExposure_eq T H a .two hcount k l hkl⟩
              | three =>
                  exact Or.inr ⟨hcount,
                    twoPositiveMActualExposure_eq T H a .three hcount k l hkl⟩
            · intro _ _ hthree i hi
              have hik : i ≠ k := by
                intro hEq
                apply hi
                simp [support, hsupport, hEq]
              have hil : i ≠ l := by
                intro hEq
                apply hi
                simp [support, hsupport, hEq]
              cases d with
              | two =>
                  change pairedChildCount T (some H.terminalNode) = 2 at hcount
                  omega
              | three =>
                  exact twoPositiveMActualPorts_other_three T H a hcount
                    k l i hkl hik hil
      if htwo : pairedChildCount T (some H.terminalNode) = 2 then
        exact build .two (by
          change pairedChildCount T (some H.terminalNode) = 2
          exact htwo)
      else
        exact build .three (by
          change pairedChildCount T (some H.terminalNode) = 3
          rcases he.2 with htwo' | hthree
          · exact False.elim (htwo htwo')
          · exact hthree)

theorem ResourceLoopAllocation.entry_eq_requestedExit
    {hK : InTargetClassKLeTwo T} {H : MaximalHelix T}
    {e : EndpointType} {a : Color} {xi : Parity}
    (A : ResourceLoopAllocation T hK H e a xi) :
    A.entry = requestedExit xi xi.opposite e := by
  cases e with
  | E => exact A.eEntry rfl
  | L => exact A.lEntry rfl
  | M => exact A.mEntry rfl

/-- The local multiset proof is the actual exposure proof once the installed
closing colour and actual child-head ports are identified. -/
theorem ResourceLoopAllocation.properActualExposure
    {hK : InTargetClassKLeTwo T} {H : MaximalHelix T}
    {e : EndpointType} {a : Color} {xi : Parity}
    (A : ResourceLoopAllocation T hK H e a xi) (chi : Coloring T)
    (hclosing : chi H.terminalNode = a)
    (hports : ChildPortsInstalled chi (some H.terminalNode) A.ports) :
    ProperExposure (exposedMultiset chi (some H.terminalNode)) := by
  rw [exposedMultiset_paired, hclosing,
    childColorMultiset_eq_portMultiset_of_childPortsInstalled chi
      (some H.terminalNode) A.ports hports]
  exact A.proper

/-- The complete load-bearing `M,r=2` package.  It exposes the two actual
positive slots (rather than schematic table positions), the incoming-long
fact, the non-grey close, actual exposure properness, and the degree-three
remaining-slot colour. -/
theorem ResourceLoopAllocation.twoSupportActualFacts
    {hK : InTargetClassKLeTwo T} {H : MaximalHelix T}
    {e : EndpointType} {a : Color} {xi : Parity}
    (A : ResourceLoopAllocation T hK H e a xi)
    (heM : e = .M) (hcard : (loopShortSupport T H).card = 2)
    (chi : Coloring T) (hclosing : chi H.terminalNode = a)
    (hports : ChildPortsInstalled chi (some H.terminalNode) A.ports) :
    a.NonGrey ∧ 3 ≤ H.length ∧
      ((pairedChildCount T (some H.terminalNode) = 2 ∧
        loopPortExposure a A.ports = twoPositiveMExposure a .two) ∨
       (pairedChildCount T (some H.terminalNode) = 3 ∧
        loopPortExposure a A.ports = twoPositiveMExposure a .three)) ∧
      ∃ i j : Fin (pairedChildCount T (some H.terminalNode)),
        i ≠ j ∧ loopShortSupport T H = {i, j} ∧
        A.ports i = Color.grey ∧ A.ports j = Color.grey ∧
        ProperExposure (exposedMultiset chi (some H.terminalNode)) ∧
        (∀ _hthree : pairedChildCount T (some H.terminalNode) = 3,
          ∀ k ∉ loopShortSupport T H, A.ports k = a) := by
  refine ⟨A.twoSupportClosingNonGrey heM hcard,
    A.twoSupportIncomingLong hcard,
    A.twoSupportExactExposure heM hcard, ?_⟩
  obtain ⟨i, j, hij, hsupport⟩ := Finset.card_eq_two.mp hcard
  refine ⟨i, j, hij, hsupport, ?_, ?_,
    A.properActualExposure chi hclosing hports, ?_⟩
  · apply A.positiveGreyAtM heM i
    simp [hsupport]
  · apply A.positiveGreyAtM heM j
    simp [hsupport]
  · exact A.twoSupportThirdClosing heM hcard

/-- Constructor-specialized audit theorem for the two-support branch. -/
theorem completeResourceLoopAllocation_twoSupportActualFacts
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (e : EndpointType) (he : HasEndpointType H.terminalNode e)
    (a : Color) (xi : Parity)
    (hLclosing : e = .L → a.NonGrey)
    (hTwoClosing : e = .M →
      (loopShortSupport T H).card = 2 → a.NonGrey)
    (heM : e = .M) (hcard : (loopShortSupport T H).card = 2)
    (chi : Coloring T) (hclosing : chi H.terminalNode = a)
    (hports : ChildPortsInstalled chi (some H.terminalNode)
      (completeResourceLoopAllocation hK H e he a xi hLclosing
        hTwoClosing).ports) :
    let A := completeResourceLoopAllocation hK H e he a xi hLclosing
      hTwoClosing
    a.NonGrey ∧ 3 ≤ H.length ∧
      ((pairedChildCount T (some H.terminalNode) = 2 ∧
        loopPortExposure a A.ports = twoPositiveMExposure a .two) ∨
       (pairedChildCount T (some H.terminalNode) = 3 ∧
        loopPortExposure a A.ports = twoPositiveMExposure a .three)) ∧
      ∃ i j : Fin (pairedChildCount T (some H.terminalNode)),
        i ≠ j ∧ loopShortSupport T H = {i, j} ∧
        A.ports i = Color.grey ∧ A.ports j = Color.grey ∧
        ProperExposure (exposedMultiset chi (some H.terminalNode)) ∧
        (∀ _hthree : pairedChildCount T (some H.terminalNode) = 3,
          ∀ k ∉ loopShortSupport T H, A.ports k = a) := by
  exact (completeResourceLoopAllocation hK H e he a xi hLclosing
    hTwoClosing).twoSupportActualFacts heM hcard chi hclosing hports

end RNA
