module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import RNA.Alphabet

@[expose] public section

set_option autoImplicit false

/-!
# Matching-based RNA secondary structures

The public representation in this file is the manuscript's representation:
an arbitrary finite set of normalized arcs, together with proofs that it is a
partial matching and is noncrossing.  It is not an inductively generated tree
language and imposes no minimum hairpin length, so adjacent positions may pair.
-/

namespace RNA

variable {n : Nat}

/-- A normalized arc on a length-`n` backbone.  `ordered` implies that the two
endpoints are distinct. -/
structure Arc (n : Nat) where
  left : Fin n
  right : Fin n
  ordered : left < right
  deriving DecidableEq

namespace Arc

/-- The finite subtype of ordered endpoint pairs used to enumerate arcs. -/
abbrev EndpointPair (n : Nat) :=
  {p : Fin n × Fin n // p.1 < p.2}

def toEndpointPair (a : Arc n) : EndpointPair n :=
  ⟨(a.left, a.right), a.ordered⟩

def ofEndpointPair (p : EndpointPair n) : Arc n where
  left := p.1.1
  right := p.1.2
  ordered := p.2

def equivEndpointPair (n : Nat) : EndpointPair n ≃ Arc n where
  toFun := ofEndpointPair
  invFun := toEndpointPair
  left_inv := by intro p; cases p; rfl
  right_inv := by intro a; cases a; rfl

instance instFintypeArc : Fintype (Arc n) :=
  Fintype.ofEquiv (EndpointPair n) (equivEndpointPair n)

@[ext]
theorem ext {a b : Arc n} (hleft : a.left = b.left) (hright : a.right = b.right) : a = b := by
  cases a
  cases b
  simp_all

@[simp]
theorem left_ne_right (a : Arc n) : a.left ≠ a.right :=
  ne_of_lt a.ordered

@[simp]
theorem right_ne_left (a : Arc n) : a.right ≠ a.left :=
  (a.left_ne_right).symm

/-- `p` is one of the two endpoints of `a`. -/
def Incident (a : Arc n) (p : Fin n) : Prop := p = a.left ∨ p = a.right

/-- Lower-case alias for endpoint membership, convenient in derived modules. -/
abbrev memEndpoint (a : Arc n) (p : Fin n) : Prop := a.Incident p

instance instDecidableIncident (a : Arc n) (p : Fin n) : Decidable (a.Incident p) :=
  by
    unfold Incident
    infer_instance

@[simp]
theorem incident_left (a : Arc n) : a.Incident a.left :=
  Or.inl rfl

@[simp]
theorem incident_right (a : Arc n) : a.Incident a.right :=
  Or.inr rfl

/-- Two arcs share an endpoint. -/
def ShareEndpoint (a b : Arc n) : Prop :=
  ∃ p : Fin n, a.Incident p ∧ b.Incident p

/-- Verb-form alias for `ShareEndpoint`. -/
abbrev SharesEndpoint (a b : Arc n) : Prop := ShareEndpoint a b

instance instDecidableShareEndpoint (a b : Arc n) : Decidable (ShareEndpoint a b) :=
  by
    unfold ShareEndpoint
    infer_instance

theorem shareEndpoint_symm {a b : Arc n} : ShareEndpoint a b ↔ ShareEndpoint b a := by
  constructor
  · rintro ⟨p, hap, hbp⟩
    exact ⟨p, hbp, hap⟩
  · rintro ⟨p, hbp, hap⟩
    exact ⟨p, hap, hbp⟩

@[simp]
theorem shareEndpoint_self (a : Arc n) : ShareEndpoint a a :=
  ⟨a.left, a.incident_left, a.incident_left⟩

/-- Strict interleaving of normalized arcs.  Nested and disjoint arcs do not
cross. -/
def Crosses (a b : Arc n) : Prop :=
  (a.left < b.left ∧ b.left < a.right ∧ a.right < b.right) ∨
  (b.left < a.left ∧ a.left < b.right ∧ b.right < a.right)

instance instDecidableCrosses (a b : Arc n) : Decidable (a.Crosses b) :=
  by
    unfold Crosses
    infer_instance

theorem crosses_symm {a b : Arc n} : a.Crosses b ↔ b.Crosses a := by
  exact or_comm

@[simp]
theorem not_crosses_self (a : Arc n) : ¬ a.Crosses a := by
  simp [Crosses]

end Arc

/-- Every backbone position is incident to at most one member of `P`. -/
def IsPartialMatching (P : Finset (Arc n)) : Prop :=
  ∀ {a : Arc n}, a ∈ P →
    ∀ {b : Arc n}, b ∈ P →
      a.ShareEndpoint b → a = b

/-- No two arcs in `P` strictly interleave. -/
def IsNoncrossing (P : Finset (Arc n)) : Prop :=
  ∀ {a : Arc n}, a ∈ P →
    ∀ {b : Arc n}, b ∈ P →
      ¬ a.Crosses b

instance instDecidableIsPartialMatching (P : Finset (Arc n)) : Decidable (IsPartialMatching P) := by
  unfold IsPartialMatching
  infer_instance

instance instDecidableIsNoncrossing (P : Finset (Arc n)) : Decidable (IsNoncrossing P) := by
  unfold IsNoncrossing
  infer_instance

/-- An arbitrary pseudoknot-free partial matching on the ordered backbone. -/
structure SecondaryStructure (n : Nat) where
  arcs : Finset (Arc n)
  isPartialMatching : IsPartialMatching arcs
  isNoncrossing : IsNoncrossing arcs

namespace SecondaryStructure

@[ext]
theorem ext {S T : SecondaryStructure n} (h : S.arcs = T.arcs) : S = T := by
  cases S
  cases T
  simp_all

instance instDecidableEqSecondaryStructure : DecidableEq (SecondaryStructure n) :=
  fun S T =>
    if h : S.arcs = T.arcs then
      isTrue (SecondaryStructure.ext h)
    else
      isFalse (fun hST => h (congrArg arcs hST))

/-- Membership of an arc in a structure. -/
instance instMembershipArc : Membership (Arc n) (SecondaryStructure n) where
  mem S a := a ∈ S.arcs

@[simp]
theorem mem_arcs {a : Arc n} {S : SecondaryStructure n} : a ∈ S.arcs ↔ a ∈ S :=
  Iff.rfl

theorem eq_of_mem_of_shareEndpoint {S : SecondaryStructure n} {a b : Arc n}
    (ha : a ∈ S.arcs) (hb : b ∈ S.arcs) (hshare : a.ShareEndpoint b) : a = b :=
  S.isPartialMatching ha hb hshare

/-- Verb-form alias for downstream interval-tree developments. -/
theorem eq_of_mem_of_sharesEndpoint {S : SecondaryStructure n} {a b : Arc n}
    (ha : a ∈ S.arcs) (hb : b ∈ S.arcs) (hshare : a.SharesEndpoint b) : a = b :=
  S.eq_of_mem_of_shareEndpoint ha hb hshare

theorem eq_of_mem_of_incident {S : SecondaryStructure n} {a b : Arc n} {p : Fin n}
    (ha : a ∈ S.arcs) (hb : b ∈ S.arcs) (hap : a.Incident p) (hbp : b.Incident p) : a = b :=
  S.eq_of_mem_of_shareEndpoint ha hb ⟨p, hap, hbp⟩

theorem not_crossing {S : SecondaryStructure n} {a b : Arc n}
    (ha : a ∈ S.arcs) (hb : b ∈ S.arcs) : ¬ a.Crosses b :=
  S.isNoncrossing ha hb

/-- The empty secondary structure. -/
def empty (n : Nat) : SecondaryStructure n where
  arcs := ∅
  isPartialMatching := by simp [IsPartialMatching]
  isNoncrossing := by simp [IsNoncrossing]

/-- Whether a position is paired in the structure. -/
def positionPaired (S : SecondaryStructure n) (p : Fin n) : Prop :=
  ∃ a ∈ S.arcs, a.Incident p

instance instDecidablePositionPaired (S : SecondaryStructure n) (p : Fin n) :
    Decidable (S.positionPaired p) :=
  by
    unfold positionPaired
    infer_instance

/-- Forget the validity proofs, retaining them in a subtype.  This provides a
computable finite enumeration of all structures on a fixed finite backbone. -/
abbrev ValidArcSet (n : Nat) :=
  {P : Finset (Arc n) // IsPartialMatching P ∧ IsNoncrossing P}

def toValidArcSet (S : SecondaryStructure n) : ValidArcSet n :=
  ⟨S.arcs, S.isPartialMatching, S.isNoncrossing⟩

def ofValidArcSet (P : ValidArcSet n) : SecondaryStructure n where
  arcs := P.1
  isPartialMatching := P.2.1
  isNoncrossing := P.2.2

def equivValidArcSet (n : Nat) : ValidArcSet n ≃ SecondaryStructure n where
  toFun := ofValidArcSet
  invFun := toValidArcSet
  left_inv := by intro P; cases P; rfl
  right_inv := by intro S; cases S; rfl

instance instFintypeSecondaryStructure : Fintype (SecondaryStructure n) :=
  Fintype.ofEquiv (ValidArcSet n) (equivValidArcSet n)

end SecondaryStructure

/-- A structure is compatible with a complete sequence when every one of its
arcs joins complementary letters. -/
def StructureCompatible (w : Sequence n) (S : SecondaryStructure n) : Prop :=
  ∀ a ∈ S.arcs, Compatible (w a.left) (w a.right)

/-- Readable alias used by some derived modules. -/
abbrev CompatibleStructure (w : Sequence n) (S : SecondaryStructure n) : Prop :=
  StructureCompatible w S

instance instDecidableStructureCompatible (w : Sequence n) (S : SecondaryStructure n) :
    Decidable (StructureCompatible w S) := by
  unfold StructureCompatible
  infer_instance

/-- Number of base pairs in a structure. -/
def pairCount (S : SecondaryStructure n) : Nat := S.arcs.card

/-- Nussinov--Jacobson energy in the exact convention of the manuscript. -/
def energy (_w : Sequence n) (S : SecondaryStructure n) : Int :=
  -(pairCount S : Int)

theorem energy_lt_iff_pairCount_gt (w : Sequence n) (S T : SecondaryStructure n) :
    energy w S < energy w T ↔ pairCount T < pairCount S := by
  simp [energy]

theorem energy_le_iff_pairCount_ge (w : Sequence n) (S T : SecondaryStructure n) :
    energy w S ≤ energy w T ↔ pairCount T ≤ pairCount S := by
  simp [energy]

theorem energy_eq_iff_pairCount_eq (w : Sequence n) (S T : SecondaryStructure n) :
    energy w S = energy w T ↔ pairCount S = pairCount T := by
  simp only [energy, neg_inj, Int.natCast_inj]

/-- `w` uniquely designs `T`: the target is compatible, and every distinct
compatible noncrossing partial matching on the same complete sequence has
strictly fewer pairs. -/
def UniqueDesigns (w : Sequence n) (T : SecondaryStructure n) : Prop :=
  StructureCompatible w T ∧
    ∀ S : SecondaryStructure n,
      StructureCompatible w S →
      S ≠ T →
      pairCount S < pairCount T

/-- A target is designable when one complete sequence uniquely designs it. -/
def Designable (T : SecondaryStructure n) : Prop :=
  ∃ w : Sequence n, UniqueDesigns w T

instance instDecidableUniqueDesigns (w : Sequence n) (T : SecondaryStructure n) :
    Decidable (UniqueDesigns w T) := by
  unfold UniqueDesigns
  infer_instance

instance instDecidableDesignable (T : SecondaryStructure n) : Decidable (Designable T) := by
  unfold Designable
  infer_instance

/-- Maximum pair count among every compatible structure on the same sequence. -/
def IsMaximumCompatible (w : Sequence n) (T : SecondaryStructure n) : Prop :=
  ∀ S : SecondaryStructure n,
    StructureCompatible w S → pairCount S ≤ pairCount T

/-- A compatible structure tying the target's pair count must be the target. -/
def IsUniqueMaximumPairCount (w : Sequence n) (T : SecondaryStructure n) : Prop :=
  ∀ S : SecondaryStructure n,
    StructureCompatible w S → pairCount S = pairCount T → S = T

instance instDecidableIsMaximumCompatible (w : Sequence n) (T : SecondaryStructure n) :
    Decidable (IsMaximumCompatible w T) := by
  unfold IsMaximumCompatible
  infer_instance

instance instDecidableIsUniqueMaximumPairCount (w : Sequence n) (T : SecondaryStructure n) :
    Decidable (IsUniqueMaximumPairCount w T) := by
  unfold IsUniqueMaximumPairCount
  infer_instance

/-- The strict-competitor definition says exactly that the compatible target is
maximum-cardinality and is the only compatible structure attaining that
cardinality. -/
theorem uniqueDesigns_iff_maximum_and_unique_count (w : Sequence n) (T : SecondaryStructure n) :
    UniqueDesigns w T ↔
      StructureCompatible w T ∧
      IsMaximumCompatible w T ∧
      IsUniqueMaximumPairCount w T := by
  constructor
  · rintro ⟨hT, hstrict⟩
    refine ⟨hT, ?_, ?_⟩
    · intro S hS
      by_cases hST : S = T
      · subst S
        exact Nat.le_refl _
      · exact Nat.le_of_lt (hstrict S hS hST)
    · intro S hS hcount
      by_contra hST
      have hlt := hstrict S hS hST
      exact (Nat.ne_of_lt hlt) hcount
  · rintro ⟨hT, hmax, hunique⟩
    refine ⟨hT, ?_⟩
    intro S hS hST
    have hle := hmax S hS
    have hne : pairCount S ≠ pairCount T := by
      intro heq
      exact hST (hunique S hS heq)
    exact lt_of_le_of_ne hle hne

/-- Unique minimization of the integer energy over all compatible structures
on the same complete sequence. -/
def UniqueMinimumEnergy (w : Sequence n) (T : SecondaryStructure n) : Prop :=
  StructureCompatible w T ∧
    ∀ S : SecondaryStructure n,
      StructureCompatible w S →
      S ≠ T →
      energy w T < energy w S

instance instDecidableUniqueMinimumEnergy (w : Sequence n) (T : SecondaryStructure n) :
    Decidable (UniqueMinimumEnergy w T) := by
  unfold UniqueMinimumEnergy
  infer_instance

theorem uniqueDesigns_iff_uniqueMinimumEnergy (w : Sequence n) (T : SecondaryStructure n) :
    UniqueDesigns w T ↔ UniqueMinimumEnergy w T := by
  constructor <;> rintro ⟨hT, h⟩ <;> refine ⟨hT, ?_⟩
  · intro S hS hST
    exact (energy_lt_iff_pairCount_gt w T S).2 (h S hS hST)
  · intro S hS hST
    exact (energy_lt_iff_pairCount_gt w T S).1 (h S hS hST)

/-- Unique minimum energy is exactly compatible unique maximum pair count. -/
theorem uniqueMinimumEnergy_iff_maximum_and_unique_count
    (w : Sequence n) (T : SecondaryStructure n) :
    UniqueMinimumEnergy w T ↔
      StructureCompatible w T ∧
      IsMaximumCompatible w T ∧
      IsUniqueMaximumPairCount w T :=
  (uniqueDesigns_iff_uniqueMinimumEnergy w T).symm.trans
    (uniqueDesigns_iff_maximum_and_unique_count w T)

end RNA
