module

public import RNA.AtMostTwoShort.Interface
public import RNA.Milestone3Local

@[expose] public section

set_option autoImplicit false

/-!
# Resource-aware local helix transfers

This file is additive to the completed one-short development.  It supplies a
dispatcher requiring only the local allowed-length disjunction, plus a
strengthened long transfer from Q whose requested `eta` exit nevertheless
closes non-grey.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- The additive allowed-length dispatcher.  It has no target-class premise:
the caller supplies exactly the local fact that the helix has length two or is
long. -/
def allowedLengthTransfer
    (h : Nat) (xi entry target : Parity) (first : Color)
    (hallowed : h = 2 ∨ 3 ≤ h)
    (hsafe : Safe h entry xi.opposite first) :
    LocalTransfer h entry xi.opposite target first := by
  by_cases htwo : h = 2
  · subst h
    exact twoPairTransferOfSafe xi xi.opposite entry target first rfl hsafe
  · exact longHelixTransfer_of_safe h entry xi.opposite target first
      (hallowed.resolve_left htwo) hsafe

/-- Maximal-helix form of `allowedLengthTransfer`. -/
def allowedHelixTransfer
    (H : MaximalHelix T) (xi entry target : Parity) (first : Color)
    (hallowed : H.length = 2 ∨ 3 ≤ H.length)
    (hsafe : Safe H.length entry xi.opposite first) :
    LocalTransfer H.length entry xi.opposite target first :=
  allowedLengthTransfer H.length xi entry target first hallowed hsafe

/-! ## The four explicit strengthened word families -/

/-- `G a^(h-1)`, used for a grey eta-entry and odd `h`. -/
def greyThenRepeatWord (h : Nat) (a : Color) : List Color :=
  Color.grey :: List.replicate (h - 1) a

/-- `G G a^(h-2)`, used for a grey eta-entry and even `h`. -/
def twoGreysThenRepeatWord (h : Nat) (a : Color) : List Color :=
  Color.grey :: Color.grey :: List.replicate (h - 2) a

@[simp] theorem greyThenRepeatWord_length (h : Nat) (a : Color)
    (hh : 1 ≤ h) :
    (greyThenRepeatWord h a).length = h := by
  simp [greyThenRepeatWord]
  omega

@[simp] theorem twoGreysThenRepeatWord_length (h : Nat) (a : Color)
    (hh : 2 ≤ h) :
    (twoGreysThenRepeatWord h a).length = h := by
  simp [twoGreysThenRepeatWord]
  omega

@[simp] theorem greyThenRepeatWord_head (h : Nat) (a : Color) :
    (greyThenRepeatWord h a).head? = some Color.grey := by
  rfl

@[simp] theorem twoGreysThenRepeatWord_head (h : Nat) (a : Color) :
    (twoGreysThenRepeatWord h a).head? = some Color.grey := by
  rfl

theorem internallyProper_greyThenRepeatWord
    (h : Nat) (a : Color) (hh : 2 ≤ h) (ha : a.NonGrey) :
    InternallyProper (greyThenRepeatWord h a) := by
  have hk : 0 < h - 1 := by omega
  cases hkrep : h - 1 with
  | zero => omega
  | succ k =>
      unfold greyThenRepeatWord
      rw [hkrep, List.replicate_succ]
      simp only [InternallyProper]
      refine ⟨?_, ?_⟩
      · rcases (Color.nonGrey_iff a).1 ha with rfl | rfl <;> decide
      · simpa [List.replicate_succ] using
          internallyProper_replicate (k + 1) a

theorem internallyProper_twoGreysThenRepeatWord
    (h : Nat) (a : Color) (hh : 3 ≤ h) (ha : a.NonGrey) :
    InternallyProper (twoGreysThenRepeatWord h a) := by
  have hk : 0 < h - 2 := by omega
  cases hkrep : h - 2 with
  | zero => omega
  | succ k =>
      unfold twoGreysThenRepeatWord
      rw [hkrep, List.replicate_succ]
      simp only [InternallyProper]
      refine ⟨by decide, ?_, ?_⟩
      · rcases (Color.nonGrey_iff a).1 ha with rfl | rfl <;> decide
      · simpa [List.replicate_succ] using
          internallyProper_replicate (k + 1) a

theorem greysAt_greyThenRepeatWord
    (eta : Parity) (h : Nat) (a : Color) (ha : a.NonGrey) :
    GreysAt eta eta (greyThenRepeatWord h a) := by
  unfold greyThenRepeatWord
  simp only [GreysAt, Color.deltaParity_grey, Parity.add_zero]
  exact ⟨fun _ => trivial,
    greysAt_replicate_nonGrey eta eta (h - 1) a ha⟩

theorem greysAt_twoGreysThenRepeatWord
    (eta : Parity) (h : Nat) (a : Color) (ha : a.NonGrey) :
    GreysAt eta eta (twoGreysThenRepeatWord h a) := by
  unfold twoGreysThenRepeatWord
  simp only [GreysAt, Color.deltaParity_grey, Parity.add_zero]
  exact ⟨fun _ => trivial, fun _ => trivial,
    greysAt_replicate_nonGrey eta eta (h - 2) a ha⟩

theorem exitResidue_greyThenRepeatWord
    (eta : Parity) (h : Nat) (a : Color) (ha : a.NonGrey) :
    exitResidue eta (greyThenRepeatWord h a) =
      eta + (h - 1 : Nat) := by
  unfold greyThenRepeatWord
  simp only [exitResidue, Color.deltaParity_grey, Parity.add_zero]
  exact exitResidue_replicate_nonGrey eta (h - 1) a ha

theorem exitResidue_twoGreysThenRepeatWord
    (eta : Parity) (h : Nat) (a : Color) (ha : a.NonGrey) :
    exitResidue eta (twoGreysThenRepeatWord h a) =
      eta + (h - 2 : Nat) := by
  unfold twoGreysThenRepeatWord
  simp only [exitResidue, Color.deltaParity_grey, Parity.add_zero]
  exact exitResidue_replicate_nonGrey eta (h - 2) a ha

theorem closesNonGrey_greyThenRepeatWord
    (h : Nat) (a : Color) (hh : 2 ≤ h) (ha : a.NonGrey) :
    ClosesNonGrey (greyThenRepeatWord h a) := by
  refine ⟨a, ?_, ha⟩
  unfold greyThenRepeatWord
  rw [List.getLast?_cons, List.getLast?_replicate]
  simp [show h - 1 ≠ 0 by omega]

theorem closesNonGrey_twoGreysThenRepeatWord
    (h : Nat) (a : Color) (hh : 3 ≤ h) (ha : a.NonGrey) :
    ClosesNonGrey (twoGreysThenRepeatWord h a) := by
  refine ⟨a, ?_, ha⟩
  unfold twoGreysThenRepeatWord
  rw [List.getLast?_cons, List.getLast?_cons, List.getLast?_replicate]
  simp [show h - 2 ≠ 0 by omega]

theorem parity_cast_eq_one_of_ne_zero (h : Nat)
    (hne : (h : Parity) ≠ 0) : (h : Parity) = 1 := by
  rcases Parity.eq_or_eq_opposite 0 (h : Parity) with hzero | hone
  · exact (hne hzero).elim
  · simpa [Parity.opposite] using hone

theorem cast_sub_one_eq_zero_of_cast_eq_one
    (h : Nat) (hh : 1 ≤ h) (hcast : (h : Parity) = 1) :
    ((h - 1 : Nat) : Parity) = 0 := by
  have hnat : h - 1 + 1 = h := Nat.sub_add_cancel hh
  have hpar := congrArg (fun k : Nat => (k : Parity)) hnat
  rw [Nat.cast_add, show ((1 : Nat) : Parity) = 1 by decide, hcast] at hpar
  apply add_right_cancel (b := (1 : Parity))
  simpa only [Parity.zero_add] using hpar

theorem cast_sub_two_eq_zero_of_cast_eq_zero
    (h : Nat) (hh : 2 ≤ h) (hcast : (h : Parity) = 0) :
    ((h - 2 : Nat) : Parity) = 0 := by
  have hnat : h - 2 + 2 = h := Nat.sub_add_cancel hh
  have hpar := congrArg (fun k : Nat => (k : Parity)) hnat
  rw [Nat.cast_add, show ((2 : Nat) : Parity) = 0 by decide,
    Parity.add_zero, hcast] at hpar
  exact hpar

/-- `a^h`: the xi-entry, odd-length strengthened word. -/
def xiOddEtaTransfer
    (h : Nat) (xi : Parity) (a : Color)
    (hh : 3 ≤ h) (ha : a.NonGrey) (hodd : (h : Parity) = 1) :
    LocalTransfer h xi xi.opposite xi.opposite a := {
  colors := constantHelixWord h a
  length_eq := constantHelixWord_length h a
  first_eq := constantHelixWord_head h a (by omega)
  internallyProper := internallyProper_replicate h a
  greysAtEta := greysAt_replicate_nonGrey xi.opposite xi h a ha
  exit_eq := by
    rw [exitResidue_constantHelixWord xi h a ha, hodd]
    exact Parity.add_one_eq_opposite xi
  closesNonGrey := by
    intro hbad
    exact (xi.opposite.ne_opposite hbad).elim }

/-- `a G a^(h-2)`: the xi-entry, even-length strengthened word.  This
includes the exceptional boundary `h=4` directly. -/
def xiEvenEtaTransfer
    (h : Nat) (xi : Parity) (a : Color)
    (hh : 3 ≤ h) (ha : a.NonGrey) (heven : (h : Parity) = 0) :
    LocalTransfer h xi xi.opposite xi.opposite a := {
  colors := oneGreyAtTwoWord h a
  length_eq := oneGreyAtTwoWord_length h a (by omega)
  first_eq := oneGreyAtTwoWord_head h a
  internallyProper := internallyProper_oneGreyAtTwo h a ha
  greysAtEta := greysAt_oneGreyAtTwo xi.opposite xi h a ha (by
    rw [(Color.deltaParity_eq_one_iff a).2 ha]
    exact Parity.add_one_eq_opposite xi)
  exit_eq := by
    rw [exitResidue_oneGreyAtTwo_eq_constant_opposite xi h a (by omega) ha,
      exitResidue_constantHelixWord xi h a ha, heven, Parity.add_zero]
  closesNonGrey := by
    intro hbad
    exact (xi.opposite.ne_opposite hbad).elim }

/-- `G a^(h-1)`: the eta-entry, odd-length strengthened word. -/
def etaGreyOddEtaTransfer
    (h : Nat) (xi : Parity) (a : Color)
    (hh : 3 ≤ h) (ha : a.NonGrey) (hodd : (h : Parity) = 1) :
    LocalTransfer h xi.opposite xi.opposite xi.opposite Color.grey := {
  colors := greyThenRepeatWord h a
  length_eq := greyThenRepeatWord_length h a (by omega)
  first_eq := greyThenRepeatWord_head h a
  internallyProper := internallyProper_greyThenRepeatWord h a (by omega) ha
  greysAtEta := greysAt_greyThenRepeatWord xi.opposite h a ha
  exit_eq := by
    rw [exitResidue_greyThenRepeatWord xi.opposite h a ha,
      cast_sub_one_eq_zero_of_cast_eq_one h (by omega) hodd,
      Parity.add_zero]
  closesNonGrey := by
    intro hbad
    exact (xi.opposite.ne_opposite hbad).elim }

/-- `G G a^(h-2)`: the eta-entry, even-length strengthened word.  This
includes the exceptional boundary `h=4` directly. -/
def etaGreyEvenEtaTransfer
    (h : Nat) (xi : Parity) (a : Color)
    (hh : 3 ≤ h) (ha : a.NonGrey) (heven : (h : Parity) = 0) :
    LocalTransfer h xi.opposite xi.opposite xi.opposite Color.grey := {
  colors := twoGreysThenRepeatWord h a
  length_eq := twoGreysThenRepeatWord_length h a (by omega)
  first_eq := twoGreysThenRepeatWord_head h a
  internallyProper := internallyProper_twoGreysThenRepeatWord h a hh ha
  greysAtEta := greysAt_twoGreysThenRepeatWord xi.opposite h a ha
  exit_eq := by
    rw [exitResidue_twoGreysThenRepeatWord xi.opposite h a ha,
      cast_sub_two_eq_zero_of_cast_eq_zero h (by omega) heven,
      Parity.add_zero]
  closesNonGrey := by
    intro hbad
    exact (xi.opposite.ne_opposite hbad).elim }

/-- A long eta-exit transfer bundled with the extra non-grey-close fact that
is not part of `LocalTransfer`'s eta-exit postcondition. -/
abbrev LongEtaTransfer
    (h : Nat) (xi entry : Parity) (first : Color) :=
  {tr : LocalTransfer h entry xi.opposite xi.opposite first //
    ClosesNonGrey tr.colors}

/-- Strengthened Q transfer.  The branch words are exactly

* `a^h` at xi for odd `h`;
* `a G a^(h-2)` at xi for even `h`;
* `G B^(h-1)` at eta for odd `h`;
* `G G B^(h-2)` at eta for even `h`.

Thus `h=3` and `h=4` are constructed directly, rather than inferred from a
stabilized transition table. -/
def longTransfer_eta_closesNonGrey_of_Q
    (h : Nat) (xi entry : Parity) (first : Color)
    (hh : 3 ≤ h) (hQ : InQ xi entry first) :
    LongEtaTransfer h xi entry first := by
  by_cases hentry : entry = xi
  · have hfirst : first.NonGrey := by
      rw [hentry] at hQ
      exact (inQ_xi_iff_nonGrey xi first).1 hQ
    subst entry
    by_cases heven : (h : Parity) = 0
    · let tr := xiEvenEtaTransfer h xi first hh hfirst heven
      exact ⟨tr, closesNonGrey_oneGreyAtTwo h first hh hfirst⟩
    · have hodd := parity_cast_eq_one_of_ne_zero h heven
      let tr := xiOddEtaTransfer h xi first hh hfirst hodd
      exact ⟨tr, closesNonGrey_replicate h first (by omega) hfirst⟩
  · have hentryEta : entry = xi.opposite := by
      rcases hQ with ⟨hbad, _⟩ | ⟨heta, _⟩
      · exact (hentry hbad).elim
      · exact heta
    have hfirstGrey : first = Color.grey := by
      rw [hentryEta] at hQ
      exact (inQ_eta_iff_grey xi first).1 hQ
    subst entry
    subst first
    by_cases heven : (h : Parity) = 0
    · let tr := etaGreyEvenEtaTransfer h xi Color.black hh
        Color.black_nonGrey heven
      exact ⟨tr, closesNonGrey_twoGreysThenRepeatWord h Color.black hh
        Color.black_nonGrey⟩
    · have hodd := parity_cast_eq_one_of_ne_zero h heven
      let tr := etaGreyOddEtaTransfer h xi Color.black hh
        Color.black_nonGrey hodd
      exact ⟨tr, closesNonGrey_greyThenRepeatWord h Color.black (by omega)
        Color.black_nonGrey⟩

/-- Unbundled transfer projection for construction code. -/
def longEtaTransferOfQ
    (h : Nat) (xi entry : Parity) (first : Color)
    (hh : 3 ≤ h) (hQ : InQ xi entry first) :
    LocalTransfer h entry xi.opposite xi.opposite first :=
  (longTransfer_eta_closesNonGrey_of_Q h xi entry first hh hQ).1

theorem longEtaTransferOfQ_closesNonGrey
    (h : Nat) (xi entry : Parity) (first : Color)
    (hh : 3 ≤ h) (hQ : InQ xi entry first) :
    ClosesNonGrey (longEtaTransferOfQ h xi entry first hh hQ).colors :=
  (longTransfer_eta_closesNonGrey_of_Q h xi entry first hh hQ).2

namespace LongEtaTransfer

/-- The strengthened close fact expressed using the construction-facing named
closing colour. -/
theorem closingColor_nonGrey
    {h : Nat} {xi entry : Parity} {first : Color}
    (tr : LongEtaTransfer h xi entry first) (hpos : 0 < h) :
    (tr.1.closingColor hpos).NonGrey := by
  obtain ⟨c, hlast, hc⟩ := tr.2
  rw [tr.1.getLast?_eq_some_closingColor hpos] at hlast
  have heq : tr.1.closingColor hpos = c := Option.some.inj hlast
  simpa [heq] using hc

end LongEtaTransfer

/-! ## Concrete boundary witnesses -/

def gbbTransfer (xi : Parity) :
    LocalTransfer 3 xi.opposite xi.opposite xi.opposite Color.grey :=
  etaGreyOddEtaTransfer 3 xi Color.black (by omega) Color.black_nonGrey
    (by decide)

@[simp] theorem gbbTransfer_colors (xi : Parity) :
    (gbbTransfer xi).colors = [Color.grey, Color.black, Color.black] := by
  rfl

def gwwTransfer (xi : Parity) :
    LocalTransfer 3 xi.opposite xi.opposite xi.opposite Color.grey :=
  etaGreyOddEtaTransfer 3 xi Color.white (by omega) Color.white_nonGrey
    (by decide)

@[simp] theorem gwwTransfer_colors (xi : Parity) :
    (gwwTransfer xi).colors = [Color.grey, Color.white, Color.white] := by
  rfl

def etaEvenFourTransfer (xi : Parity) :
    LocalTransfer 4 xi.opposite xi.opposite xi.opposite Color.grey :=
  etaGreyEvenEtaTransfer 4 xi Color.black (by omega) Color.black_nonGrey
    (by decide)

@[simp] theorem etaEvenFourTransfer_colors (xi : Parity) :
    (etaEvenFourTransfer xi).colors =
      [Color.grey, Color.grey, Color.black, Color.black] := by
  rfl

def xiOddThreeTransfer (xi : Parity) :
    LocalTransfer 3 xi xi.opposite xi.opposite Color.black :=
  xiOddEtaTransfer 3 xi Color.black (by omega) Color.black_nonGrey (by decide)

@[simp] theorem xiOddThreeTransfer_colors (xi : Parity) :
    (xiOddThreeTransfer xi).colors =
      [Color.black, Color.black, Color.black] := by
  rfl

def xiEvenFourTransfer (xi : Parity) :
    LocalTransfer 4 xi xi.opposite xi.opposite Color.black :=
  xiEvenEtaTransfer 4 xi Color.black (by omega) Color.black_nonGrey (by decide)

@[simp] theorem xiEvenFourTransfer_colors (xi : Parity) :
    (xiEvenFourTransfer xi).colors =
      [Color.black, Color.grey, Color.black, Color.black] := by
  rfl

/-! ## Installed global bridges -/

namespace LongEtaTransfer

theorem installed_headColor
    (χ : Coloring T) (H : MaximalHelix T)
    {xi entry : Parity} {first : Color}
    (tr : LongEtaTransfer H.length xi entry first)
    (hinstalled : HelixWordInstalled χ H tr.1.colors) :
    χ H.headNode = first :=
  installedLocalTransfer_headColor χ H tr.1 hinstalled

theorem installed_terminalLevel
    (χ : Coloring T) (H : MaximalHelix T)
    {xi entry : Parity} {first : Color}
    (tr : LongEtaTransfer H.length xi entry first)
    (hinstalled : HelixWordInstalled χ H tr.1.colors)
    (hentry : entry = levelParity (entryLevel χ H.headNode)) :
    levelParity (pairedLevel χ H.terminalNode) = xi.opposite :=
  installedLocalTransfer_terminalLevel χ H tr.1 hinstalled hentry

theorem installed_terminalColor_nonGrey
    (χ : Coloring T) (H : MaximalHelix T)
    {xi entry : Parity} {first : Color}
    (tr : LongEtaTransfer H.length xi entry first)
    (hinstalled : HelixWordInstalled χ H tr.1.colors) :
    (χ H.terminalNode).NonGrey := by
  rw [installedLocalTransfer_terminalColor_eq_closingColor χ H tr.1 hinstalled]
  exact tr.closingColor_nonGrey H.positive

theorem installed_internalExposure
    (χ : Coloring T) (H : MaximalHelix T)
    {xi entry : Parity} {first : Color}
    (tr : LongEtaTransfer H.length xi entry first)
    (hinstalled : HelixWordInstalled χ H tr.1.colors)
    (k : Nat) (hk : k + 1 < H.length) :
    ProperExposure
      (exposedMultiset χ (some (H.offsetNode ⟨k, by omega⟩))) :=
  installedLocalTransfer_internalExposure χ H tr.1 hinstalled k hk

theorem installed_globalGreysAt
    (χ : Coloring T) (H : MaximalHelix T)
    {xi entry : Parity} {first : Color}
    (tr : LongEtaTransfer H.length xi entry first)
    (hinstalled : HelixWordInstalled χ H tr.1.colors)
    (hentry : entry = levelParity (entryLevel χ H.headNode)) :
    GlobalHelixGreysAt χ H xi.opposite :=
  installedLocalTransfer_globalGreysAt χ H tr.1 hinstalled hentry

end LongEtaTransfer

/-- The ordinary allowed dispatcher has the same installed global facts when
its requested target is xi; then its standard `LocalTransfer` close clause is
applicable because xi is opposite the grey residue. -/
theorem installed_allowedHelixTransfer_headColor
    (χ : Coloring T) (H : MaximalHelix T)
    (xi entry target : Parity) (first : Color)
    (hallowed : H.length = 2 ∨ 3 ≤ H.length)
    (hsafe : Safe H.length entry xi.opposite first)
    (hinstalled : HelixWordInstalled χ H
      (allowedHelixTransfer H xi entry target first hallowed hsafe).colors) :
    χ H.headNode = first :=
  installedLocalTransfer_headColor χ H
    (allowedHelixTransfer H xi entry target first hallowed hsafe) hinstalled

theorem installed_allowedHelixTransfer_terminalLevel
    (χ : Coloring T) (H : MaximalHelix T)
    (xi entry target : Parity) (first : Color)
    (hallowed : H.length = 2 ∨ 3 ≤ H.length)
    (hsafe : Safe H.length entry xi.opposite first)
    (hinstalled : HelixWordInstalled χ H
      (allowedHelixTransfer H xi entry target first hallowed hsafe).colors)
    (hentry : entry = levelParity (entryLevel χ H.headNode)) :
    levelParity (pairedLevel χ H.terminalNode) = target :=
  installedLocalTransfer_terminalLevel χ H
    (allowedHelixTransfer H xi entry target first hallowed hsafe)
    hinstalled hentry

theorem installed_allowedHelixTransfer_internalExposure
    (χ : Coloring T) (H : MaximalHelix T)
    (xi entry target : Parity) (first : Color)
    (hallowed : H.length = 2 ∨ 3 ≤ H.length)
    (hsafe : Safe H.length entry xi.opposite first)
    (hinstalled : HelixWordInstalled χ H
      (allowedHelixTransfer H xi entry target first hallowed hsafe).colors)
    (k : Nat) (hk : k + 1 < H.length) :
    ProperExposure
      (exposedMultiset χ (some (H.offsetNode ⟨k, by omega⟩))) :=
  installedLocalTransfer_internalExposure χ H
    (allowedHelixTransfer H xi entry target first hallowed hsafe)
    hinstalled k hk

theorem installed_allowedHelixTransfer_globalGreysAt
    (χ : Coloring T) (H : MaximalHelix T)
    (xi entry target : Parity) (first : Color)
    (hallowed : H.length = 2 ∨ 3 ≤ H.length)
    (hsafe : Safe H.length entry xi.opposite first)
    (hinstalled : HelixWordInstalled χ H
      (allowedHelixTransfer H xi entry target first hallowed hsafe).colors)
    (hentry : entry = levelParity (entryLevel χ H.headNode)) :
    GlobalHelixGreysAt χ H xi.opposite :=
  installedLocalTransfer_globalGreysAt χ H
    (allowedHelixTransfer H xi entry target first hallowed hsafe)
    hinstalled hentry

theorem installed_allowedHelixTransfer_terminalColor_nonGrey
    (χ : Coloring T) (H : MaximalHelix T)
    (xi entry target : Parity) (first : Color)
    (hallowed : H.length = 2 ∨ 3 ≤ H.length)
    (hsafe : Safe H.length entry xi.opposite first)
    (hinstalled : HelixWordInstalled χ H
      (allowedHelixTransfer H xi entry target first hallowed hsafe).colors)
    (htarget : target = xi) :
    (χ H.terminalNode).NonGrey := by
  apply installedLocalTransfer_terminalColor_nonGrey χ H
    (allowedHelixTransfer H xi entry target first hallowed hsafe) hinstalled
  rw [htarget]
  exact (Parity.opposite_opposite xi).symm

end RNA
