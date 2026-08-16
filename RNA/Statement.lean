module

public import RNA.TargetClass

@[expose] public section

set_option autoImplicit false

/-!
# Exact final proposition

Milestone 1 defines and type-checks this proposition without asserting or
proving it; the colouring and no-tie arguments belong to later milestones.
-/

namespace RNA

/-- Every matching-based target in the exact class `K` has one complete
four-letter sequence that uniquely designs it against every compatible
noncrossing partial matching on that same sequence. -/
def OneShortHelixDesignabilityStatement : Prop :=
  ∀ {n : Nat} (T : SecondaryStructure n),
    InTargetClassK T →
      ∃ w : Sequence n, UniqueDesigns w T

#check OneShortHelixDesignabilityStatement

end RNA
