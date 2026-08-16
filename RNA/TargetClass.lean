module

public import RNA.Helix
public import RNA.Motifs

@[expose] public section

set_option autoImplicit false

/-!
# The exact target class K

All five manuscript clauses appear explicitly.  In particular, the first
clause selects a length-two maximal helix and proves every length-two maximal
helix equals it; this is "exactly one", not "at most one".
-/

namespace RNA

variable {n : Nat}

/-- Targets with exactly one maximal helix of length two, no length-one helix,
all other maximal helices of length at least three, and neither forbidden
motif. -/
def InTargetClassK (T : SecondaryStructure n) : Prop :=
  ∃ h₂ : MaximalHelix T,
    h₂.length = 2 ∧
      (∀ h : MaximalHelix T, h.length = 2 → h = h₂) ∧
      (∀ h : MaximalHelix T, h.length ≠ 1) ∧
      (∀ h : MaximalHelix T, h ≠ h₂ → 3 ≤ h.length) ∧
      ¬ HasM5 T ∧
      ¬ HasM3Dot T

instance instDecidableInTargetClassK (T : SecondaryStructure n) :
    Decidable (InTargetClassK T) := by
  unfold InTargetClassK
  infer_instance

theorem targetClass_has_unique_length_two {T : SecondaryStructure n}
    (hK : InTargetClassK T) :
    ∃ h₂ : MaximalHelix T,
      h₂.length = 2 ∧
        ∀ h : MaximalHelix T, h.length = 2 → h = h₂ := by
  obtain ⟨h₂, hlen, hunique, _⟩ := hK
  exact ⟨h₂, hlen, hunique⟩

theorem targetClass_no_length_one {T : SecondaryStructure n}
    (hK : InTargetClassK T) (h : MaximalHelix T) :
    h.length ≠ 1 := by
  obtain ⟨_, _, _, hnone, _⟩ := hK
  exact hnone h

theorem targetClass_other_length_at_least_three {T : SecondaryStructure n}
    (hK : InTargetClassK T) {h₂ h : MaximalHelix T}
    (hlen : h₂.length = 2) (hne : h ≠ h₂) :
    3 ≤ h.length := by
  obtain ⟨selected, _, hunique, _, hlong, _⟩ := hK
  have hselected : selected = h₂ := by
    exact (hunique h₂ hlen).symm
  apply hlong h
  intro heq
  apply hne
  exact heq.trans hselected

theorem targetClass_motifFree {T : SecondaryStructure n}
    (hK : InTargetClassK T) : MotifFree T := by
  obtain ⟨_, _, _, _, _, hm5, hm3⟩ := hK
  exact ⟨hm5, hm3⟩

end RNA
