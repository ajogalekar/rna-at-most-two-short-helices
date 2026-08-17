module

public import RNA.LevelImbalance

@[expose] public section

set_option autoImplicit false

/-!
# Global Milestone-4 sequence certificate

The certificate retains one Milestone-3 coloring and one sequence computed
from that exact coloring.  Every inventory, prefix, maximum, and obstruction
field refers to the same stored sequence witness.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Exact four-letter counts for an assigned sequence. -/
structure AssignedNucleotideCounts
    (T : SecondaryStructure n) (χ : Coloring T) (w : Sequence n) : Prop where
  countU : nucleotideCount w Nucleotide.U = greyPairCount χ
  countG : nucleotideCount w Nucleotide.G = nonGreyPairCount χ
  countC : nucleotideCount w Nucleotide.C = nonGreyPairCount χ
  countA : nucleotideCount w Nucleotide.A =
    greyPairCount χ + targetUnpairedCount T

/-- Exact counts of the canonical sequence from a proper coloring. -/
theorem assignedNucleotideCounts_sequenceOfProperColoring
    (χ : Coloring T) (hProper : ProperColoring χ) :
    AssignedNucleotideCounts T χ (sequenceOfProperColoring χ hProper) where
  countU := nucleotideCount_U_sequenceOfProperColoring χ hProper
  countG := nucleotideCount_G_sequenceOfProperColoring χ hProper
  countC := nucleotideCount_C_sequenceOfProperColoring χ hProper
  countA := nucleotideCount_A_sequenceOfProperColoring χ hProper

/-- Ordinary exact-integer separation retained by a global coloring
certificate. -/
theorem GlobalColoringCertificate.separated
    {hK : InTargetClassK T}
    (C : GlobalColoringCertificate T hK) : Separated C.coloring :=
  strongTwoSeparated_implies_separated C.coloring
    ((strongTwoSeparated_iff_exists_with C.coloring).2
      ⟨C.allocation.row.xi, C.strong⟩)

/-- One complete sequence together with every universal result established in
Milestone 4. -/
structure GlobalSequenceCertificate
    (T : SecondaryStructure n) (hK : InTargetClassK T) where
  coloringCertificate : GlobalColoringCertificate T hK
  leftLetter : PairedNode T → Nucleotide
  leftLetter_eq : leftLetter =
    leftLetterOfProperColoring coloringCertificate.coloring
      coloringCertificate.proper
  sequence : Sequence n
  sequence_eq : sequence =
    sequenceOfProperColoring coloringCertificate.coloring
      coloringCertificate.proper
  targetCompatible : StructureCompatible sequence T
  localDistinctness : LocallyDistinct T sequence
  greyLeftLetter : ∀ v : PairedNode T,
    coloringCertificate.coloring v = Color.grey →
      leftLetter v = Nucleotide.A ∨ leftLetter v = Nucleotide.U
  greyChildCopies : ∀ p v : PairedNode T,
    coloringCertificate.coloring v = Color.grey →
    parent T (Sum.inl v) = some p →
    coloringCertificate.coloring p = Color.grey →
      leftLetter v = leftLetter p
  nucleotideCounts : AssignedNucleotideCounts T
    coloringCertificate.coloring sequence
  pairCount_le : ∀ S : SecondaryStructure n,
    StructureCompatible sequence S → pairCount S ≤ pairCount T
  equalityUsesAllLimiting : ∀ S : SecondaryStructure n,
    StructureCompatible sequence S → pairCount S = pairCount T →
      (∀ i : Fin n, sequence i = Nucleotide.U → S.positionPaired i) ∧
      (∀ i : Fin n, sequence i = Nucleotide.C → S.positionPaired i) ∧
      (∀ i : Fin n, sequence i = Nucleotide.G → S.positionPaired i)
  pairedPrefixBalance : ∀ v : PairedNode T,
    prefixBalanceAt sequence v.val.left =
      pairedLevel coloringCertificate.coloring v
  unpairedPrefixBalance : ∀ u : UnpairedPosition T,
    prefixBalanceAt sequence u.val =
      unpairedLevel coloringCertificate.coloring u
  greyRightPrefixBalance : ∀ v : PairedNode T,
    coloringCertificate.coloring v = Color.grey →
      prefixBalanceAt sequence v.val.right =
          prefixBalanceAt sequence v.val.left ∧
        prefixBalanceAt sequence v.val.left =
          pairedLevel coloringCertificate.coloring v
  targetUnpairedPairingObstruction : ∀ S : SecondaryStructure n,
    StructureCompatible sequence S →
    ∀ (u : UnpairedPosition T) (j : Fin n),
      PositionPartner S u.val j →
        ∃ k : Fin n,
          (sequence k = Nucleotide.G ∨ sequence k = Nucleotide.C) ∧
            ¬ S.positionPaired k

/-- Canonical class-K Milestone-4 certificate, retaining the exact
`globalColoringCertificate` witness and its single derived sequence. -/
noncomputable def globalSequenceCertificate
    (hK : InTargetClassK T) : GlobalSequenceCertificate T hK := by
  let C := globalColoringCertificate hK
  let w := sequenceOfProperColoring C.coloring C.proper
  refine {
    coloringCertificate := C
    leftLetter := leftLetterOfProperColoring C.coloring C.proper
    leftLetter_eq := rfl
    sequence := w
    sequence_eq := rfl
    targetCompatible := structureCompatible_sequenceOfProperColoring
      C.coloring C.proper
    localDistinctness := locallyDistinct_sequenceOfProperColoring
      C.coloring C.proper
    greyLeftLetter := ?_
    greyChildCopies := ?_
    nucleotideCounts := assignedNucleotideCounts_sequenceOfProperColoring
      C.coloring C.proper
    pairCount_le := ?_
    equalityUsesAllLimiting := ?_
    pairedPrefixBalance := ?_
    unpairedPrefixBalance := ?_
    greyRightPrefixBalance := ?_
    targetUnpairedPairingObstruction := ?_ }
  · intro v hv
    exact leftLetter_grey_mem_AU C.coloring C.proper v hv
  · intro p v hv hp hpGrey
    exact leftLetter_grey_child_of_grey_parent
      C.coloring C.proper p v hv hp hpGrey
  · intro S hS
    exact pairCount_le_sequenceOfProperColoring C.coloring C.proper S hS
  · intro S hS hEq
    exact equality_uses_all_limiting_nucleotides
      C.coloring C.proper S hS hEq
  · intro v
    exact prefixBalanceAt_pairedLeft_eq_pairedLevel C.coloring C.proper v
  · intro u
    exact prefixBalanceAt_unpaired_eq_unpairedLevel C.coloring C.proper u
  · intro v hv
    exact prefixBalanceAt_greyRight_eq C.coloring C.proper v hv
  · intro S hS u j hPartner
    exact targetUnpaired_pairing_obstruction
      C.coloring C.proper C.separated S hS u j hPartner

end RNA
