module

public import RNA.AtMostTwoShort.ResourceAllocations

@[expose] public section

set_option autoImplicit false

/-!
# Resource-aware allocations at the virtual root

The root is handled separately from nonroot loops because its exposure has no
closing incidence.  Positive root degree uses actual ordered child slots and
the F/Q requirements.  Degree zero has a separate certificate and is consumed
by the global all-unpaired branch.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-! ## Two designated positive root slots -/

/-- The `r = 2` large-root rows.  The first two displayed slots are the two
positive-short children. -/
def twoPositiveRootBasePorts :
    (r : EtaRootRow) → PortAssignment r.count
  | .three => ![Color.grey, Color.grey, Color.black]
  | .four => ![Color.grey, Color.grey, Color.black, Color.white]

/-- Move the two displayed grey ports to two distinct actual slots. -/
def twoPositiveRootPortsAt (r : EtaRootRow)
    (i j : Fin r.count) (hij : i ≠ j) : PortAssignment r.count :=
  (twoPositiveRootBasePorts r).reindex
    (twoSlotPerm i j hij (by cases r <;> decide))

@[simp] theorem twoPositiveRootPortsAt_left (r : EtaRootRow)
    (i j : Fin r.count) (hij : i ≠ j) :
    twoPositiveRootPortsAt r i j hij i = Color.grey := by
  change twoPositiveRootBasePorts r
    (twoSlotPerm i j hij (by cases r <;> decide) i) = Color.grey
  rw [twoSlotPerm_left]
  cases r <;> rfl

@[simp] theorem twoPositiveRootPortsAt_right (r : EtaRootRow)
    (i j : Fin r.count) (hij : i ≠ j) :
    twoPositiveRootPortsAt r i j hij j = Color.grey := by
  change twoPositiveRootBasePorts r
    (twoSlotPerm i j hij (by cases r <;> decide) j) = Color.grey
  rw [twoSlotPerm_right]
  cases r <;> rfl

/-- In the degree-three `G,G,B` row, the unique remaining slot is black. -/
theorem twoPositiveRootPortsAt_other_three
    (i j k : Fin EtaRootRow.three.count) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    twoPositiveRootPortsAt .three i j hij k = Color.black := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all only [ne_eq, not_true_eq_false, not_false_eq_true,
      Fin.mk.injEq, one_ne_zero, zero_ne_one, twoPositiveRootPortsAt,
      PortAssignment.reindex, twoPositiveRootBasePorts, twoSlotPerm,
      Equiv.swap_self, Equiv.refl_apply, Equiv.refl_trans,
      Equiv.trans_refl, Equiv.coe_refl, Equiv.swap_apply_right,
      Equiv.swap_apply_left, Equiv.swap_apply_def, Equiv.coe_trans,
      ↓reduceIte] <;>
    first | exact (hij (Fin.ext (by decide))).elim | rfl

theorem twoPositiveRootExposure_proper (r : EtaRootRow)
    (i j : Fin r.count) (hij : i ≠ j) :
    ProperExposure (rootPortExposure
      (twoPositiveRootPortsAt r i j hij)) := by
  unfold twoPositiveRootPortsAt
  rw [rootPortExposure, portMultiset_reindex]
  cases r <;> decide

/-- Install an `r = 2` row on the actual ordered root children. -/
noncomputable def twoPositiveRootActualPorts (T : SecondaryStructure n)
    (r : EtaRootRow) (hcount : pairedChildCount T none = r.count)
    (i j : Fin (pairedChildCount T none)) (hij : i ≠ j) :
    ChildPortAssignment T none :=
  installPortRow T none
    (twoPositiveRootPortsAt r (finCongr hcount i) (finCongr hcount j)
      ((finCongr hcount).injective.ne hij)) hcount

@[simp] theorem twoPositiveRootActualPorts_left
    (T : SecondaryStructure n) (r : EtaRootRow)
    (hcount : pairedChildCount T none = r.count)
    (i j : Fin (pairedChildCount T none)) (hij : i ≠ j) :
    twoPositiveRootActualPorts T r hcount i j hij i = Color.grey := by
  simp [twoPositiveRootActualPorts, installPortRow,
    PortAssignment.reindex]

@[simp] theorem twoPositiveRootActualPorts_right
    (T : SecondaryStructure n) (r : EtaRootRow)
    (hcount : pairedChildCount T none = r.count)
    (i j : Fin (pairedChildCount T none)) (hij : i ≠ j) :
    twoPositiveRootActualPorts T r hcount i j hij j = Color.grey := by
  simp [twoPositiveRootActualPorts, installPortRow,
    PortAssignment.reindex]

theorem twoPositiveRootActualExposure_proper
    (T : SecondaryStructure n) (r : EtaRootRow)
    (hcount : pairedChildCount T none = r.count)
    (i j : Fin (pairedChildCount T none)) (hij : i ≠ j) :
    ProperExposure (rootPortExposure
      (twoPositiveRootActualPorts T r hcount i j hij)) := by
  unfold twoPositiveRootActualPorts
  rw [rootPortExposure, installPortRow_multiset]
  exact twoPositiveRootExposure_proper r _ _ _

theorem twoPositiveRootActualPorts_other_three
    (T : SecondaryStructure n)
    (hcount : pairedChildCount T none = EtaRootRow.three.count)
    (i j k : Fin (pairedChildCount T none)) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    twoPositiveRootActualPorts T .three hcount i j hij k = Color.black := by
  apply twoPositiveRootPortsAt_other_three
  · exact (finCongr hcount).injective.ne hij
  · exact (finCongr hcount).injective.ne hki
  · exact (finCongr hcount).injective.ne hkj

/-! ## Proof-bearing root allocations -/

/-- A complete root allocation on actual ordered child slots. -/
structure ResourceRootAllocation (T : SecondaryStructure n)
    (hK : InTargetClassKLeTwo T) where
  xi : Parity
  eta : Parity
  eta_eq_opposite : eta = xi.opposite
  entry : Parity
  ports : ChildPortAssignment T none
  proper : ProperExposure (rootPortExposure ports)
  requiredOutgoing : ∀ i, RequiredInterface T
    (outgoingHelixAtRootSlot T i) xi entry (ports i)
  supportCardLeTwo : (rootShortSupport T).card ≤ 2
  positiveGreyAtEta : entry = eta → ∀ i ∈ rootShortSupport T,
    ports i = Color.grey
  shortFreeInF : ∀ i ∉ rootShortSupport T, InF xi entry (ports i)
  entry_eq_xi_of_small : pairedChildCount T none ≤ 2 → entry = xi
  entry_eq_eta_of_large : 3 ≤ pairedChildCount T none → entry = eta
  xi_eq_zero_of_entry_xi : entry = xi → xi = 0
  eta_eq_zero_of_entry_eta : entry = eta → eta = 0
  twoSupportThirdBlack : (rootShortSupport T).card = 2 →
    ∀ _hthree : pairedChildCount T none = 3,
      ∀ i ∉ rootShortSupport T, ports i = Color.black

/-- Separate allocation-level certificate for the all-unpaired root base. -/
structure RootDegreeZeroCertificate (T : SecondaryStructure n)
    (hK : InTargetClassKLeTwo T) where
  rootCountZero : pairedChildCount T none = 0
  xi : Parity
  xi_eq_zero : xi = 0
  emptyRootExposureProper :
    ProperExposure (rootPortExposure (noPorts : PortAssignment 0))

/-- Canonical degree-zero root resource certificate. -/
def rootDegreeZeroCertificate (hK : InTargetClassKLeTwo T)
    (hzero : pairedChildCount T none = 0) :
    RootDegreeZeroCertificate T hK where
  rootCountZero := hzero
  xi := 0
  xi_eq_zero := rfl
  emptyRootExposureProper := by decide

theorem requiredRootAtXi_of_nonGrey
    (H : MaximalHelix T) (xi : Parity) (first : Color)
    (hfirst : first.NonGrey) :
    RequiredInterface T H xi xi first := by
  by_cases hzero : shortHelixSubtreeCount T H = 0
  · exact (requiredInterface_of_count_eq_zero H xi xi first hzero).2
      ((inF_xi_iff_nonGrey xi first).2 hfirst)
  · exact (requiredInterface_of_count_ne_zero H xi xi first hzero).2
      ((inQ_xi_iff_nonGrey xi first).2 hfirst)

theorem inF_one_zero (first : Color) :
    InF (1 : Parity) 0 first := by
  have h := inF_eta (1 : Parity) first
  rw [show (1 : Parity).opposite = 0 by decide] at h
  exact h

theorem inQ_one_zero_grey :
    InQ (1 : Parity) 0 Color.grey := by
  have h := inQ_eta_grey (1 : Parity)
  rw [show (1 : Parity).opposite = 0 by decide] at h
  exact h

private theorem rootShortSupport_card_le_childCount
    (T : SecondaryStructure n) :
    (rootShortSupport T).card ≤ pairedChildCount T none := by
  simpa using Finset.card_le_univ (rootShortSupport T)

/-- Complete allocation for every positive root degree.  The global short
budget is used directly in all four degree cases; there is no exact-zero,
exact-one, or exact-two designability case split. -/
noncomputable def completeResourceRootAllocation
    (hK : InTargetClassKLeTwo T)
    (hpositive : 0 < pairedChildCount T none) :
    ResourceRootAllocation T hK := by
  have hsupportLe : (rootShortSupport T).card ≤ 2 :=
    rootShortSupport_card_le_two hK
  have hdegreeLe : pairedChildCount T none ≤ 4 := by
    have hle := pairedDegree_le_four T
      (targetClassKLeTwo_motifFree hK) none
    simpa [pairedDegree] using hle
  have hcases : pairedChildCount T none = 1 ∨
      pairedChildCount T none = 2 ∨
      pairedChildCount T none = 3 ∨
      pairedChildCount T none = 4 := by
    omega
  have hrowExists : ∃ r : RootRow,
      pairedChildCount T none = r.count := by
    rcases hcases with h | h | h | h
    · exact ⟨.xiOne, h⟩
    · exact ⟨.xiTwo, h⟩
    · exact ⟨.etaThree, h⟩
    · exact ⟨.etaFour, h⟩
  let arity := Classical.choose hrowExists
  have hcount := Classical.choose_spec hrowExists
  change pairedChildCount T none = arity.count at hcount
  cases harity : arity <;> simp only [RootRow.count, harity] at hcount
  · let A := rootActualPorts T RootRow.xiOne hcount
    have hport (i : Fin (pairedChildCount T none)) :
        (A i).NonGrey := by
      exact rootActualPorts_xi_nonGrey T .xiOne (Or.inl rfl) hcount i
    refine {
      xi := 0
      eta := 1
      eta_eq_opposite := by decide
      entry := 0
      ports := A
      proper := rootActualPorts_proper T .xiOne hcount
      requiredOutgoing := ?_
      supportCardLeTwo := hsupportLe
      positiveGreyAtEta := ?_
      shortFreeInF := ?_
      entry_eq_xi_of_small := fun _ => rfl
      entry_eq_eta_of_large := ?_
      xi_eq_zero_of_entry_xi := fun _ => rfl
      eta_eq_zero_of_entry_eta := ?_
      twoSupportThirdBlack := ?_ }
    · intro i
      exact requiredRootAtXi_of_nonGrey
        (outgoingHelixAtRootSlot T i) 0 (A i) (hport i)
    · intro hbad
      simp at hbad
    · intro i _
      exact (inF_xi_iff_nonGrey 0 (A i)).2 (hport i)
    · intro hlarge
      omega
    · intro hbad
      simp at hbad
    · intro _ hcount
      omega
  · let A := rootActualPorts T RootRow.xiTwo hcount
    have hport (i : Fin (pairedChildCount T none)) :
        (A i).NonGrey := by
      exact rootActualPorts_xi_nonGrey T .xiTwo (Or.inr rfl) hcount i
    refine {
      xi := 0
      eta := 1
      eta_eq_opposite := by decide
      entry := 0
      ports := A
      proper := rootActualPorts_proper T .xiTwo hcount
      requiredOutgoing := ?_
      supportCardLeTwo := hsupportLe
      positiveGreyAtEta := ?_
      shortFreeInF := ?_
      entry_eq_xi_of_small := fun _ => rfl
      entry_eq_eta_of_large := ?_
      xi_eq_zero_of_entry_xi := fun _ => rfl
      eta_eq_zero_of_entry_eta := ?_
      twoSupportThirdBlack := ?_ }
    · intro i
      exact requiredRootAtXi_of_nonGrey
        (outgoingHelixAtRootSlot T i) 0 (A i) (hport i)
    · intro hbad
      simp at hbad
    · intro i _
      exact (inF_xi_iff_nonGrey 0 (A i)).2 (hport i)
    · intro hlarge
      omega
    · intro hbad
      simp at hbad
    · intro _ hcount
      omega
  · let build (r : EtaRootRow)
        (hcount : pairedChildCount T none = r.count) :
        ResourceRootAllocation T hK := by
      let support := rootShortSupport T
      by_cases hcardZero : support.card = 0
      · have hsupportEmpty : support = ∅ :=
          Finset.card_eq_zero.mp hcardZero
        let row : RootRow := match r with
          | .three => .etaThree
          | .four => .etaFour
        have hrowCount : pairedChildCount T none = row.count := by
          cases r <;> simpa [row, EtaRootRow.count, RootRow.count] using hcount
        let A := rootActualPorts T row hrowCount
        refine {
          xi := 1
          eta := 0
          eta_eq_opposite := by decide
          entry := 0
          ports := A
          proper := rootActualPorts_proper T row hrowCount
          requiredOutgoing := ?_
          supportCardLeTwo := hsupportLe
          positiveGreyAtEta := ?_
          shortFreeInF := ?_
          entry_eq_xi_of_small := ?_
          entry_eq_eta_of_large := fun _ => rfl
          xi_eq_zero_of_entry_xi := ?_
          eta_eq_zero_of_entry_eta := fun _ => rfl
          twoSupportThirdBlack := ?_ }
        · intro i
          have hi : i ∉ rootShortSupport T := by
            simp [support, hsupportEmpty]
          have hzeroCount : shortHelixSubtreeCount T
              (outgoingHelixAtRootSlot T i) = 0 :=
            (not_mem_rootShortSupport_iff_count_eq_zero T i).1 hi
          exact (requiredInterface_of_count_eq_zero
            (outgoingHelixAtRootSlot T i) 1 0 (A i) hzeroCount).2
              (inF_one_zero (A i))
        · intro _ i hi
          have : i ∈ support := by simpa [support] using hi
          rw [hsupportEmpty] at this
          simp at this
        · intro i _
          exact inF_one_zero (A i)
        · intro hsmall
          cases r <;> simp [EtaRootRow.count] at hcount <;> omega
        · intro hbad
          simp at hbad
        · intro hcard
          have : support.card = 2 := by simpa [support] using hcard
          omega
      · by_cases hcardOne : support.card = 1
        · let hwitness := Finset.card_eq_one.mp hcardOne
          let k := Classical.choose hwitness
          have hsupport : support = {k} := Classical.choose_spec hwitness
          let A := etaRootActualPortsAt T r hcount k
          have hpositivePort (i : Fin (pairedChildCount T none))
              (hi : i ∈ support) : A i = Color.grey := by
            have hik : i = k := by simpa [hsupport] using hi
            subst i
            exact etaRootActualPortsAt_short T r hcount k
          refine {
            xi := 1
            eta := 0
            eta_eq_opposite := by decide
            entry := 0
            ports := A
            proper := etaRootActualPortsAt_proper T r hcount k
            requiredOutgoing := ?_
            supportCardLeTwo := hsupportLe
            positiveGreyAtEta := ?_
            shortFreeInF := ?_
            entry_eq_xi_of_small := ?_
            entry_eq_eta_of_large := fun _ => rfl
            xi_eq_zero_of_entry_xi := ?_
            eta_eq_zero_of_entry_eta := fun _ => rfl
            twoSupportThirdBlack := ?_ }
          · intro i
            by_cases hi : i ∈ support
            · have hpos := (mem_rootShortSupport_iff T i).1
                (by simpa [support] using hi)
              rw [hpositivePort i hi]
              exact (requiredInterface_of_count_pos
                (outgoingHelixAtRootSlot T i) 1 0 Color.grey hpos).2
                  inQ_one_zero_grey
            · have hzeroCount : shortHelixSubtreeCount T
                  (outgoingHelixAtRootSlot T i) = 0 :=
                (not_mem_rootShortSupport_iff_count_eq_zero T i).1
                  (by simpa [support] using hi)
              exact (requiredInterface_of_count_eq_zero
                (outgoingHelixAtRootSlot T i) 1 0 (A i) hzeroCount).2
                  (inF_one_zero (A i))
          · intro _ i hi
            exact hpositivePort i (by simpa [support] using hi)
          · intro i _
            exact inF_one_zero (A i)
          · intro hsmall
            cases r <;> simp [EtaRootRow.count] at hcount <;> omega
          · intro hbad
            simp at hbad
          · intro hcard
            have : support.card = 2 := by simpa [support] using hcard
            omega
        · have hcardTwo : support.card = 2 := by
            have hs : support.card ≤ 2 := by simpa [support] using hsupportLe
            omega
          let hwitness := Finset.card_eq_two.mp hcardTwo
          let k := Classical.choose hwitness
          let hwitness' := Classical.choose_spec hwitness
          let l := Classical.choose hwitness'
          have hspec := Classical.choose_spec hwitness'
          have hkl : k ≠ l := hspec.1
          have hsupport : support = {k, l} := hspec.2
          let A := twoPositiveRootActualPorts T r hcount k l hkl
          have hpositivePort (i : Fin (pairedChildCount T none))
              (hi : i ∈ support) : A i = Color.grey := by
            have hik : i = k ∨ i = l := by simpa [hsupport] using hi
            rcases hik with rfl | rfl
            · exact twoPositiveRootActualPorts_left T r hcount k l hkl
            · exact twoPositiveRootActualPorts_right T r hcount k l hkl
          refine {
            xi := 1
            eta := 0
            eta_eq_opposite := by decide
            entry := 0
            ports := A
            proper := twoPositiveRootActualExposure_proper
              T r hcount k l hkl
            requiredOutgoing := ?_
            supportCardLeTwo := hsupportLe
            positiveGreyAtEta := ?_
            shortFreeInF := ?_
            entry_eq_xi_of_small := ?_
            entry_eq_eta_of_large := fun _ => rfl
            xi_eq_zero_of_entry_xi := ?_
            eta_eq_zero_of_entry_eta := fun _ => rfl
            twoSupportThirdBlack := ?_ }
          · intro i
            by_cases hi : i ∈ support
            · have hpos := (mem_rootShortSupport_iff T i).1
                (by simpa [support] using hi)
              rw [hpositivePort i hi]
              exact (requiredInterface_of_count_pos
                (outgoingHelixAtRootSlot T i) 1 0 Color.grey hpos).2
                  inQ_one_zero_grey
            · have hzeroCount : shortHelixSubtreeCount T
                  (outgoingHelixAtRootSlot T i) = 0 :=
                (not_mem_rootShortSupport_iff_count_eq_zero T i).1
                  (by simpa [support] using hi)
              exact (requiredInterface_of_count_eq_zero
                (outgoingHelixAtRootSlot T i) 1 0 (A i) hzeroCount).2
                  (inF_one_zero (A i))
          · intro _ i hi
            exact hpositivePort i (by simpa [support] using hi)
          · intro i _
            exact inF_one_zero (A i)
          · intro hsmall
            cases r <;> simp [EtaRootRow.count] at hcount <;> omega
          · intro hbad
            simp at hbad
          · intro _ hcountThree i hi
            have hik : i ≠ k := by
              intro hEq
              apply hi
              simp [support, hsupport, hEq]
            have hil : i ≠ l := by
              intro hEq
              apply hi
              simp [support, hsupport, hEq]
            cases r with
            | three =>
                exact twoPositiveRootActualPorts_other_three T hcount
                  k l i hkl hik hil
            | four =>
                change pairedChildCount T none = 4 at hcount
                omega
    exact build .three (by
      change pairedChildCount T none = 3
      exact hcount)
  · let build (r : EtaRootRow)
        (hcount : pairedChildCount T none = r.count) :
        ResourceRootAllocation T hK := by
      -- The proof is definitionally identical for degrees three and four.
      -- Reuse the preceding degree-three builder by reconstructing its local
      -- body through the same support split.
      let support := rootShortSupport T
      by_cases hcardZero : support.card = 0
      · have hsupportEmpty : support = ∅ := Finset.card_eq_zero.mp hcardZero
        let row : RootRow := match r with
          | .three => .etaThree
          | .four => .etaFour
        have hrowCount : pairedChildCount T none = row.count := by
          cases r <;> simpa [row, EtaRootRow.count, RootRow.count] using hcount
        let A := rootActualPorts T row hrowCount
        refine {
          xi := 1, eta := 0, eta_eq_opposite := by decide, entry := 0
          ports := A
          proper := rootActualPorts_proper T row hrowCount
          requiredOutgoing := ?_
          supportCardLeTwo := hsupportLe
          positiveGreyAtEta := ?_
          shortFreeInF := ?_
          entry_eq_xi_of_small := ?_
          entry_eq_eta_of_large := fun _ => rfl
          xi_eq_zero_of_entry_xi := ?_
          eta_eq_zero_of_entry_eta := fun _ => rfl
          twoSupportThirdBlack := ?_ }
        · intro i
          have hi : i ∉ rootShortSupport T := by
            simp [support, hsupportEmpty]
          have hz := (not_mem_rootShortSupport_iff_count_eq_zero T i).1 hi
          exact (requiredInterface_of_count_eq_zero
            (outgoingHelixAtRootSlot T i) 1 0 (A i) hz).2
              (inF_one_zero (A i))
        · intro _ i hi
          have : i ∈ support := by simpa [support] using hi
          rw [hsupportEmpty] at this
          simp at this
        · intro i _
          exact inF_one_zero (A i)
        · intro hsmall
          cases r <;> simp [EtaRootRow.count] at hcount <;> omega
        · intro hbad
          simp at hbad
        · intro hcard
          have : support.card = 2 := by simpa [support] using hcard
          omega
      · by_cases hcardOne : support.card = 1
        · let hwitness := Finset.card_eq_one.mp hcardOne
          let k := Classical.choose hwitness
          have hsupport : support = {k} := Classical.choose_spec hwitness
          let A := etaRootActualPortsAt T r hcount k
          have hpositivePort (i : Fin (pairedChildCount T none))
              (hi : i ∈ support) : A i = Color.grey := by
            have hik : i = k := by simpa [hsupport] using hi
            subst i
            exact etaRootActualPortsAt_short T r hcount k
          refine {
            xi := 1, eta := 0, eta_eq_opposite := by decide, entry := 0
            ports := A
            proper := etaRootActualPortsAt_proper T r hcount k
            requiredOutgoing := ?_
            supportCardLeTwo := hsupportLe
            positiveGreyAtEta := ?_
            shortFreeInF := ?_
            entry_eq_xi_of_small := ?_
            entry_eq_eta_of_large := fun _ => rfl
            xi_eq_zero_of_entry_xi := ?_
            eta_eq_zero_of_entry_eta := fun _ => rfl
            twoSupportThirdBlack := ?_ }
          · intro i
            by_cases hi : i ∈ support
            · have hp := (mem_rootShortSupport_iff T i).1
                (by simpa [support] using hi)
              rw [hpositivePort i hi]
              exact (requiredInterface_of_count_pos
                (outgoingHelixAtRootSlot T i) 1 0 Color.grey hp).2
                  inQ_one_zero_grey
            · have hz := (not_mem_rootShortSupport_iff_count_eq_zero T i).1
                (by simpa [support] using hi)
              exact (requiredInterface_of_count_eq_zero
                (outgoingHelixAtRootSlot T i) 1 0 (A i) hz).2
                  (inF_one_zero (A i))
          · intro _ i hi
            exact hpositivePort i (by simpa [support] using hi)
          · intro i _
            exact inF_one_zero (A i)
          · intro hsmall
            cases r <;> simp [EtaRootRow.count] at hcount <;> omega
          · intro hbad
            simp at hbad
          · intro hcard
            have : support.card = 2 := by simpa [support] using hcard
            omega
        · have hcardTwo : support.card = 2 := by
            have hs : support.card ≤ 2 := by simpa [support] using hsupportLe
            omega
          let hwitness := Finset.card_eq_two.mp hcardTwo
          let k := Classical.choose hwitness
          let hwitness' := Classical.choose_spec hwitness
          let l := Classical.choose hwitness'
          have hspec := Classical.choose_spec hwitness'
          have hkl : k ≠ l := hspec.1
          have hsupport : support = {k, l} := hspec.2
          let A := twoPositiveRootActualPorts T r hcount k l hkl
          have hpositivePort (i : Fin (pairedChildCount T none))
              (hi : i ∈ support) : A i = Color.grey := by
            have hik : i = k ∨ i = l := by simpa [hsupport] using hi
            rcases hik with rfl | rfl
            · exact twoPositiveRootActualPorts_left T r hcount k l hkl
            · exact twoPositiveRootActualPorts_right T r hcount k l hkl
          refine {
            xi := 1, eta := 0, eta_eq_opposite := by decide, entry := 0
            ports := A
            proper := twoPositiveRootActualExposure_proper T r hcount k l hkl
            requiredOutgoing := ?_
            supportCardLeTwo := hsupportLe
            positiveGreyAtEta := ?_
            shortFreeInF := ?_
            entry_eq_xi_of_small := ?_
            entry_eq_eta_of_large := fun _ => rfl
            xi_eq_zero_of_entry_xi := ?_
            eta_eq_zero_of_entry_eta := fun _ => rfl
            twoSupportThirdBlack := ?_ }
          · intro i
            by_cases hi : i ∈ support
            · have hp := (mem_rootShortSupport_iff T i).1
                (by simpa [support] using hi)
              rw [hpositivePort i hi]
              exact (requiredInterface_of_count_pos
                (outgoingHelixAtRootSlot T i) 1 0 Color.grey hp).2
                  inQ_one_zero_grey
            · have hz := (not_mem_rootShortSupport_iff_count_eq_zero T i).1
                (by simpa [support] using hi)
              exact (requiredInterface_of_count_eq_zero
                (outgoingHelixAtRootSlot T i) 1 0 (A i) hz).2
                  (inF_one_zero (A i))
          · intro _ i hi
            exact hpositivePort i (by simpa [support] using hi)
          · intro i _
            exact inF_one_zero (A i)
          · intro hsmall
            cases r <;> simp [EtaRootRow.count] at hcount <;> omega
          · intro hbad
            simp at hbad
          · intro _ hcountThree i hi
            have hik : i ≠ k := by
              intro hEq
              apply hi
              simp [support, hsupport, hEq]
            have hil : i ≠ l := by
              intro hEq
              apply hi
              simp [support, hsupport, hEq]
            cases r with
            | three =>
                exact twoPositiveRootActualPorts_other_three T hcount
                  k l i hkl hik hil
            | four =>
                change pairedChildCount T none = 4 at hcount
                omega
    exact build .four (by
      change pairedChildCount T none = 4
      exact hcount)

/-- Audit-facing form of the deterministic two-demand root row.  Every
positive-short root child is gray; at degree three the unique remaining
short-free child is black, giving the actual `G,G,B` row up to slot order. -/
theorem completeResourceRootAllocation_twoSupport_certificate
    (hK : InTargetClassKLeTwo T)
    (hpositive : 0 < pairedChildCount T none)
    (hcard : (rootShortSupport T).card = 2)
    (hlarge : 3 ≤ pairedChildCount T none) :
    let A := completeResourceRootAllocation hK hpositive
    (∀ i ∈ rootShortSupport T, A.ports i = Color.grey) ∧
      (∀ _hthree : pairedChildCount T none = 3,
        ∀ i ∉ rootShortSupport T, A.ports i = Color.black) := by
  let A := completeResourceRootAllocation hK hpositive
  have hentry : A.entry = A.eta := A.entry_eq_eta_of_large hlarge
  exact ⟨A.positiveGreyAtEta hentry, A.twoSupportThirdBlack hcard⟩

end RNA
