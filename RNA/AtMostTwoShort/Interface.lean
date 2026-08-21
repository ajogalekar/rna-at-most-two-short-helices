module

public import RNA.HelixTransfer
public import RNA.AtMostTwoShort.ShortCount

@[expose] public section

set_option autoImplicit false

/-!
# Interface resources for at most two short helices

The residue `xi.opposite` is the distinguished grey residue.  `InF` is the
full admissible interface, while `InQ` is the smaller resource used by a
subtree containing a short helix.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- The full five-interface resource
`{xi-B, xi-W, eta-B, eta-W, eta-G}`, where `eta = xi.opposite`. -/
def InF (xi entry : Parity) (first : Color) : Prop :=
  first.AdmissibleAt entry xi.opposite

/-- The restricted three-interface resource
`{xi-B, xi-W, eta-G}`, where `eta = xi.opposite`. -/
def InQ (xi entry : Parity) (first : Color) : Prop :=
  (entry = xi ∧ first.NonGrey) ∨
    (entry = xi.opposite ∧ first = Color.grey)

instance (xi entry : Parity) (first : Color) : Decidable (InF xi entry first) :=
  inferInstanceAs (Decidable (first.AdmissibleAt entry xi.opposite))

instance (xi entry : Parity) (first : Color) : Decidable (InQ xi entry first) := by
  unfold InQ
  infer_instance

theorem inQ_implies_inF {xi entry : Parity} {first : Color}
    (hQ : InQ xi entry first) : InF xi entry first := by
  rcases hQ with ⟨rfl, hfirst⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hfirst
  · exact (Color.admissibleAt_grey_iff xi.opposite xi.opposite).2 rfl

theorem inF_xi_iff_nonGrey (xi : Parity) (first : Color) :
    InF xi xi first ↔ first.NonGrey := by
  constructor
  · rintro (hfirst | ⟨_, hbad⟩)
    · exact hfirst
    · exact (xi.ne_opposite hbad).elim
  · exact Or.inl

theorem inQ_xi_iff_nonGrey (xi : Parity) (first : Color) :
    InQ xi xi first ↔ first.NonGrey := by
  constructor
  · rintro (⟨_, hfirst⟩ | ⟨hbad, _⟩)
    · exact hfirst
    · exact (xi.ne_opposite hbad).elim
  · exact fun hfirst => Or.inl ⟨rfl, hfirst⟩

theorem not_inF_xi_grey (xi : Parity) : ¬ InF xi xi Color.grey := by
  rw [inF_xi_iff_nonGrey]
  exact Color.not_grey_nonGrey

theorem not_inQ_xi_grey (xi : Parity) : ¬ InQ xi xi Color.grey := by
  rw [inQ_xi_iff_nonGrey]
  exact Color.not_grey_nonGrey

theorem inF_xi_black (xi : Parity) : InF xi xi Color.black := by
  exact (inF_xi_iff_nonGrey xi Color.black).2 Color.black_nonGrey

theorem inF_xi_white (xi : Parity) : InF xi xi Color.white := by
  exact (inF_xi_iff_nonGrey xi Color.white).2 Color.white_nonGrey

theorem inQ_xi_black (xi : Parity) : InQ xi xi Color.black := by
  exact (inQ_xi_iff_nonGrey xi Color.black).2 Color.black_nonGrey

theorem inQ_xi_white (xi : Parity) : InQ xi xi Color.white := by
  exact (inQ_xi_iff_nonGrey xi Color.white).2 Color.white_nonGrey

theorem inF_eta (xi : Parity) (first : Color) :
    InF xi xi.opposite first := by
  cases first <;> simp [InF, Color.AdmissibleAt, Color.NonGrey]

theorem inF_eta_black (xi : Parity) : InF xi xi.opposite Color.black :=
  inF_eta xi Color.black

theorem inF_eta_white (xi : Parity) : InF xi xi.opposite Color.white :=
  inF_eta xi Color.white

theorem inF_eta_grey (xi : Parity) : InF xi xi.opposite Color.grey :=
  inF_eta xi Color.grey

theorem inQ_eta_iff_grey (xi : Parity) (first : Color) :
    InQ xi xi.opposite first ↔ first = Color.grey := by
  constructor
  · rintro (⟨hbad, _⟩ | ⟨_, hfirst⟩)
    · exact (xi.opposite_ne hbad).elim
    · exact hfirst
  · exact fun hfirst => Or.inr ⟨rfl, hfirst⟩

theorem inQ_eta_grey (xi : Parity) : InQ xi xi.opposite Color.grey := by
  exact (inQ_eta_iff_grey xi Color.grey).2 rfl

theorem not_inQ_eta_black (xi : Parity) :
    ¬ InQ xi xi.opposite Color.black := by
  rw [inQ_eta_iff_grey]
  decide

theorem not_inQ_eta_white (xi : Parity) :
    ¬ InQ xi xi.opposite Color.white := by
  rw [inQ_eta_iff_grey]
  decide

/-- Q is precisely safe for a length-two helix.  This is stronger than the
plain admissibility implication and is the reason Q is the short-subtree
resource. -/
theorem inQ_safe (h : Nat) {xi entry : Parity} {first : Color}
    (hQ : InQ xi entry first) : Safe h entry xi.opposite first := by
  refine ⟨(inQ_implies_inF hQ), ?_⟩
  rintro ⟨_, hentry⟩
  rcases hQ with ⟨hxi, _⟩ | ⟨_, hfirst⟩
  · exact (xi.ne_opposite (hxi.symm.trans hentry)).elim
  · exact hfirst

/-- Every F interface is safe on a long helix; the extra clause in `Safe`
only constrains length two. -/
theorem inF_safe_of_long {h : Nat} {xi entry : Parity} {first : Color}
    (hF : InF xi entry first) (hlong : 3 ≤ h) :
    Safe h entry xi.opposite first :=
  safe_of_admissible_of_ne_two hF (by omega)

/-! ## Subtree-indexed resource requirement -/

/-- A short-free subtree receives F; a subtree containing at least one short
helix receives Q.  The ambient induction separately maintains the global
upper bound of two resources. -/
def RequiredInterface (T : SecondaryStructure n) (H : MaximalHelix T)
    (xi entry : Parity) (first : Color) : Prop :=
  if shortHelixSubtreeCount T H = 0 then
    InF xi entry first
  else
    InQ xi entry first

instance (T : SecondaryStructure n) (H : MaximalHelix T)
    (xi entry : Parity) (first : Color) :
    Decidable (RequiredInterface T H xi entry first) := by
  unfold RequiredInterface
  infer_instance

@[simp] theorem requiredInterface_of_count_eq_zero
    (H : MaximalHelix T) (xi entry : Parity) (first : Color)
    (hzero : shortHelixSubtreeCount T H = 0) :
    RequiredInterface T H xi entry first ↔ InF xi entry first := by
  simp [RequiredInterface, hzero]

@[simp] theorem requiredInterface_of_count_ne_zero
    (H : MaximalHelix T) (xi entry : Parity) (first : Color)
    (hne : shortHelixSubtreeCount T H ≠ 0) :
    RequiredInterface T H xi entry first ↔ InQ xi entry first := by
  simp [RequiredInterface, hne]

@[simp] theorem requiredInterface_of_count_pos
    (H : MaximalHelix T) (xi entry : Parity) (first : Color)
    (hpos : 0 < shortHelixSubtreeCount T H) :
    RequiredInterface T H xi entry first ↔ InQ xi entry first := by
  exact requiredInterface_of_count_ne_zero H xi entry first (Nat.ne_of_gt hpos)

theorem requiredInterface_inF_of_count_eq_zero
    {H : MaximalHelix T} {xi entry : Parity} {first : Color}
    (hzero : shortHelixSubtreeCount T H = 0)
    (hrequired : RequiredInterface T H xi entry first) :
    InF xi entry first :=
  (requiredInterface_of_count_eq_zero H xi entry first hzero).1 hrequired

theorem requiredInterface_inQ_of_count_pos
    {H : MaximalHelix T} {xi entry : Parity} {first : Color}
    (hpos : 0 < shortHelixSubtreeCount T H)
    (hrequired : RequiredInterface T H xi entry first) :
    InQ xi entry first :=
  (requiredInterface_of_count_pos H xi entry first hpos).1 hrequired

theorem shortHelixSubtreeCount_eq_zero_implies_long
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    (hzero : shortHelixSubtreeCount T H = 0) :
    3 ≤ H.length := by
  exact targetClassKLeTwo_nonshort_length_at_least_three hK H
    (length_ne_two_of_shortHelixSubtreeCount_eq_zero H hzero)

/-- Every required interface is locally safe.  In the zero-resource branch,
the current helix cannot have length two and the class hypothesis excludes
length one, so it is long.  In the positive branch, Q supplies the stronger
length-two-safe condition directly. -/
theorem requiredInterface_safe
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    {xi entry : Parity} {first : Color}
    (hrequired : RequiredInterface T H xi entry first) :
    Safe H.length entry xi.opposite first := by
  by_cases hzero : shortHelixSubtreeCount T H = 0
  · exact inF_safe_of_long
      (requiredInterface_inF_of_count_eq_zero hzero hrequired)
      (shortHelixSubtreeCount_eq_zero_implies_long hK H hzero)
  · exact inQ_safe H.length
      ((requiredInterface_of_count_ne_zero H xi entry first hzero).1 hrequired)

theorem RequiredInterface.safe
    (hK : InTargetClassKLeTwo T) (H : MaximalHelix T)
    {xi entry : Parity} {first : Color}
    (hrequired : RequiredInterface T H xi entry first) :
    Safe H.length entry xi.opposite first :=
  requiredInterface_safe hK H hrequired

end RNA
