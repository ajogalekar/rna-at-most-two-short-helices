module

public import RNA.Coloring
public import RNA.Endpoint
public import RNA.HelixPartition
public import RNA.HelixTransfer
public import Mathlib.Data.Fin.Tuple.Take

@[expose] public section

set_option autoImplicit false

/-!
# Global/local transfer along a maximal helix

This module identifies the local running-residue model with the exact global
integer levels of a colouring restricted to the canonical outside-to-inside
ordering of a maximal helix.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- The actual colour word on a maximal helix, ordered from its head to its
terminal pair. -/
noncomputable def helixColorWord (χ : Coloring T) (H : MaximalHelix T) :
    List Color :=
  List.ofFn (fun k : Fin H.length => χ (H.offsetNode k))

/-- A locally constructed colour word has been installed on exactly the nodes
of `H` when it is the actual restriction of the global colouring. -/
def HelixWordInstalled (χ : Coloring T) (H : MaximalHelix T)
    (colors : List Color) : Prop :=
  colors = helixColorWord χ H

private theorem exists_pair_of_length_eq_two (colors : List Color)
    (hlength : colors.length = 2) :
    ∃ first second : Color, colors = [first, second] := by
  cases colors with
  | nil => simp at hlength
  | cons first rest =>
      cases rest with
      | nil => simp at hlength
      | cons second tail =>
          cases tail with
          | nil => exact ⟨first, second, rfl⟩
          | cons third tail => simp at hlength

@[simp]
theorem helixColorWord_length (χ : Coloring T) (H : MaximalHelix T) :
    (helixColorWord χ H).length = H.length := by
  simp [helixColorWord]

@[simp]
theorem helixColorWord_get (χ : Coloring T) (H : MaximalHelix T)
    (k : Fin (helixColorWord χ H).length) :
    (helixColorWord χ H).get k =
      χ (H.offsetNode ⟨k.val, by simpa using k.isLt⟩) := by
  unfold helixColorWord at k ⊢
  rw [List.get_ofFn]
  congr

theorem MaximalHelix.headNode_eq_offsetNode_zero (H : MaximalHelix T) :
    H.headNode = H.offsetNode ⟨0, H.positive⟩ := by
  apply Subtype.ext
  exact H.head_eq_offsetArc_zero

@[simp]
theorem helixColorWord_head (χ : Coloring T) (H : MaximalHelix T) :
    (helixColorWord χ H).head? = some (χ H.headNode) := by
  rw [H.headNode_eq_offsetNode_zero]
  rw [List.head?_eq_getElem?]
  simp [helixColorWord, H.positive]

@[simp]
theorem helixColorWord_getLast? (χ : Coloring T) (H : MaximalHelix T) :
    (helixColorWord χ H).getLast? = some (χ H.terminalNode) := by
  have hne : helixColorWord χ H ≠ [] := by
    intro hnil
    have hzero : H.length = 0 := by
      simpa only [helixColorWord_length, List.length_nil] using
        congrArg List.length hnil
    exact (Nat.ne_of_gt H.positive) hzero
  rw [List.getLast?_eq_getLast_of_ne_nil hne]
  apply congrArg some
  rw [List.getLast_eq_getElem]
  change (helixColorWord χ H).get
      ⟨(helixColorWord χ H).length - 1, by
        rw [helixColorWord_length]
        have := H.positive
        omega⟩ = χ H.terminalNode
  rw [helixColorWord_get]
  simp [MaximalHelix.terminalNode]

/-- The first `k+1` actual colours of a maximal helix.  The explicit bound is
kept so every indexed node is constructively known to belong to the helix. -/
noncomputable def helixColorPrefix (χ : Coloring T) (H : MaximalHelix T)
    (k : Nat) (hk : k < H.length) : List Color :=
  List.ofFn (fun j : Fin (k + 1) =>
    χ (H.offsetNode ⟨j.val, by omega⟩))

@[simp]
theorem helixColorPrefix_length (χ : Coloring T) (H : MaximalHelix T)
    (k : Nat) (hk : k < H.length) :
    (helixColorPrefix χ H k hk).length = k + 1 := by
  simp [helixColorPrefix]

theorem helixColorPrefix_succ (χ : Coloring T) (H : MaximalHelix T)
    (k : Nat) (hk : k + 1 < H.length) :
    helixColorPrefix χ H (k + 1) hk =
      helixColorPrefix χ H k (by omega) ++
        [χ (H.offsetNode ⟨k + 1, hk⟩)] := by
  unfold helixColorPrefix
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append]
  congr

/-- The explicit prefix is exactly the corresponding `take` of the actual
helix word. -/
theorem helixColorPrefix_eq_take (χ : Coloring T) (H : MaximalHelix T)
    (k : Nat) (hk : k < H.length) :
    helixColorPrefix χ H k hk =
      (helixColorWord χ H).take (k + 1) := by
  unfold helixColorPrefix helixColorWord
  rw [← Fin.ofFn_take_eq_take_ofFn (Nat.succ_le_of_lt hk)]
  congr

/-- The local inclusive residue at offset `k`, computed by walking the actual
prefix of the helix colour word from the head entry residue. -/
noncomputable def helixRunningResidue (χ : Coloring T) (H : MaximalHelix T)
    (entry : Parity) (k : Nat) (hk : k < H.length) : Parity :=
  exitResidue entry (helixColorPrefix χ H k hk)

theorem helixRunningResidue_succ (χ : Coloring T) (H : MaximalHelix T)
    (entry : Parity) (k : Nat) (hk : k + 1 < H.length) :
    helixRunningResidue χ H entry (k + 1) hk =
      helixRunningResidue χ H entry k (by omega) +
        (χ (H.offsetNode ⟨k + 1, hk⟩)).deltaParity := by
  rw [helixRunningResidue, helixColorPrefix_succ, exitResidue_append]
  rfl

/-- Pointwise global/local identification: the running residue through every
actual helix prefix is the parity of the global inclusive paired level. -/
theorem helixRunningResidue_eq_levelParity_pairedLevel
    (χ : Coloring T) (H : MaximalHelix T) (k : Nat) (hk : k < H.length) :
    helixRunningResidue χ H (levelParity (entryLevel χ H.headNode)) k hk =
      levelParity (pairedLevel χ (H.offsetNode ⟨k, hk⟩)) := by
  induction k with
  | zero =>
      simp only [helixRunningResidue, helixColorPrefix, List.ofFn_succ,
        List.ofFn_zero, exitResidue, H.headNode_eq_offsetNode_zero,
        pairedLevel_eq_entry_add_delta]
      simp [levelParity, Color.deltaParity]
  | succ k ih =>
      rw [helixRunningResidue_succ]
      rw [ih (by omega)]
      have hentry := entryLevel_of_mem_pairedChildren χ
        (H.offsetNode_succ_mem_pairedChildren k hk)
      rw [← hentry]
      simp [pairedLevel, levelParity, Color.deltaParity]

/-- Direct `take` formulation of the pointwise bridge. -/
theorem exitResidue_take_helixColorWord_eq_levelParity_pairedLevel
    (χ : Coloring T) (H : MaximalHelix T) (k : Nat) (hk : k < H.length) :
    exitResidue (levelParity (entryLevel χ H.headNode))
        ((helixColorWord χ H).take (k + 1)) =
      levelParity (pairedLevel χ (H.offsetNode ⟨k, hk⟩)) := by
  rw [← helixColorPrefix_eq_take χ H k hk]
  exact helixRunningResidue_eq_levelParity_pairedLevel χ H k hk

/-- Walking the complete actual helix word reaches exactly the parity of the
global level at its terminal pair. -/
theorem exitResidue_helixColorWord_eq_terminalLevelParity
    (χ : Coloring T) (H : MaximalHelix T) :
    exitResidue (levelParity (entryLevel χ H.headNode))
        (helixColorWord χ H) =
      levelParity (pairedLevel χ H.terminalNode) := by
  have hlast : H.length - 1 < H.length := by
    have := H.positive
    omega
  have hpoint :=
    exitResidue_take_helixColorWord_eq_levelParity_pairedLevel χ H
      (H.length - 1) hlast
  have htake : (helixColorWord χ H).take (H.length - 1 + 1) =
      helixColorWord χ H := by
    rw [show H.length - 1 + 1 = H.length by omega]
    simp
  rw [htake] at hpoint
  simpa [MaximalHelix.terminalNode] using hpoint

/-- Exact global grey-location condition restricted to one maximal helix. -/
def GlobalHelixGreysAt (χ : Coloring T) (H : MaximalHelix T)
    (eta : Parity) : Prop :=
  ∀ k : Fin H.length,
    χ (H.offsetNode k) = Color.grey →
      levelParity (pairedLevel χ (H.offsetNode k)) = eta

/-- The local `GreysAt` invariant on the actual restricted word is equivalent
to the corresponding global paired-level statement. -/
theorem greysAt_helixColorWord_iff_global
    (χ : Coloring T) (H : MaximalHelix T) (eta : Parity) :
    GreysAt eta (levelParity (entryLevel χ H.headNode))
        (helixColorWord χ H) ↔
      GlobalHelixGreysAt χ H eta := by
  constructor
  · intro hgreys k hkgrey
    let i : Fin (helixColorWord χ H).length :=
      ⟨k.val, by rw [helixColorWord_length]; exact k.isLt⟩
    have hiGrey : (helixColorWord χ H).get i = Color.grey := by
      rw [helixColorWord_get]
      simpa [i] using hkgrey
    have hlocal :=
      (greysAt_iff_get_inclusiveResidueAt eta
        (levelParity (entryLevel χ H.headNode)) (helixColorWord χ H)).1
        hgreys i hiGrey
    have hbridge :=
      exitResidue_take_helixColorWord_eq_levelParity_pairedLevel χ H
        k.val k.isLt
    exact hbridge.symm.trans (by
      simpa [inclusiveResidueAt, i] using hlocal)
  · intro hglobal
    apply (greysAt_iff_get_inclusiveResidueAt eta
      (levelParity (entryLevel χ H.headNode)) (helixColorWord χ H)).2
    intro i hiGrey
    let k : Fin H.length := ⟨i.val, by simpa using i.isLt⟩
    have hkGrey : χ (H.offsetNode k) = Color.grey := by
      rw [helixColorWord_get] at hiGrey
      simpa [k] using hiGrey
    have hglobalAt := hglobal k hkGrey
    have hbridge :=
      exitResidue_take_helixColorWord_eq_levelParity_pairedLevel χ H
        k.val k.isLt
    simpa [inclusiveResidueAt, k] using hbridge.trans hglobalAt

/-- Pointwise bridge for an arbitrary local transfer after its word has been
installed on the actual maximal helix. -/
theorem installedLocalTransfer_pointwise
    (χ : Coloring T) (H : MaximalHelix T)
    {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer H.length entry eta target first)
    (hinstalled : HelixWordInstalled χ H tr.colors)
    (hentry : entry = levelParity (entryLevel χ H.headNode))
    (k : Nat) (hk : k < H.length) :
    exitResidue entry (tr.colors.take (k + 1)) =
      levelParity (pairedLevel χ (H.offsetNode ⟨k, hk⟩)) := by
  rw [hinstalled, hentry]
  exact exitResidue_take_helixColorWord_eq_levelParity_pairedLevel χ H k hk

/-- Terminal form of the installed-word bridge: the requested local exit is
the actual global terminal paired-level residue. -/
theorem installedLocalTransfer_terminalLevel
    (χ : Coloring T) (H : MaximalHelix T)
    {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer H.length entry eta target first)
    (hinstalled : HelixWordInstalled χ H tr.colors)
    (hentry : entry = levelParity (entryLevel χ H.headNode)) :
    levelParity (pairedLevel χ H.terminalNode) = target := by
  calc
    levelParity (pairedLevel χ H.terminalNode) =
        exitResidue (levelParity (entryLevel χ H.headNode))
          (helixColorWord χ H) :=
      (exitResidue_helixColorWord_eq_terminalLevelParity χ H).symm
    _ = exitResidue entry tr.colors := by rw [hinstalled, hentry]
    _ = target := tr.exit_eq

/-- A transfer word installed on the helix carries its local grey invariant to
the exact global paired levels. -/
theorem installedLocalTransfer_globalGreysAt
    (χ : Coloring T) (H : MaximalHelix T)
    {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer H.length entry eta target first)
    (hinstalled : HelixWordInstalled χ H tr.colors)
    (hentry : entry = levelParity (entryLevel χ H.headNode)) :
    GlobalHelixGreysAt χ H eta := by
  apply (greysAt_helixColorWord_iff_global χ H eta).1
  rw [← hinstalled, ← hentry]
  exact tr.greysAtEta

/-- If an installed transfer requests the residue opposite `eta`, its local
non-grey closing guarantee is the actual terminal colour guarantee. -/
theorem installedLocalTransfer_terminalColor_nonGrey
    (χ : Coloring T) (H : MaximalHelix T)
    {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer H.length entry eta target first)
    (hinstalled : HelixWordInstalled χ H tr.colors)
    (htarget : target = eta.opposite) :
    (χ H.terminalNode).NonGrey := by
  obtain ⟨c, hlast, hc⟩ := tr.closesNonGrey htarget
  rw [hinstalled, helixColorWord_getLast?] at hlast
  have hceq : c = χ H.terminalNode := by
    exact Option.some.inj hlast.symm
  simpa [hceq] using hc

/-- Global properness controls each internal adjacency of a maximal helix. -/
theorem properAdjacent_offsetNode_succ
    (χ : Coloring T) (H : MaximalHelix T) (hproper : ProperColoring χ)
    (k : Nat) (hk : k + 1 < H.length) :
    ProperAdjacent
      (χ (H.offsetNode ⟨k, by omega⟩))
      (χ (H.offsetNode ⟨k + 1, hk⟩)) := by
  let outer : PairedNode T := H.offsetNode ⟨k, by omega⟩
  let inner : PairedNode T := H.offsetNode ⟨k + 1, hk⟩
  have hchild : inner ∈ pairedChildren T (some outer) := by
    simpa [outer, inner] using H.offsetNode_succ_mem_pairedChildren k hk
  have hmem : χ inner ∈ childColorMultiset χ (some outer) :=
    (mem_childColorMultiset_iff χ (some outer) (χ inner)).2
      ⟨inner, hchild, rfl⟩
  apply ProperExposure.mono (Y := exposedMultiset χ (some outer))
  · change (Color.inv (χ outer) ::ₘ {χ inner}) ≤
      (Color.inv (χ outer) ::ₘ childColorMultiset χ (some outer))
    exact Multiset.cons_le_cons _ (Multiset.singleton_le.mpr hmem)
  · exact hproper (some outer)

/-- Restricting a proper global colouring to an actual maximal helix gives the
local internal-properness predicate used by the transfer lemmas. -/
theorem internallyProper_helixColorWord
    (χ : Coloring T) (H : MaximalHelix T) (hproper : ProperColoring χ) :
    InternallyProper (helixColorWord χ H) := by
  apply internallyProper_of_get_succ
  intro k hk
  have hkH : k + 1 < H.length := by
    simpa using hk
  rw [helixColorWord_get, helixColorWord_get]
  simpa using properAdjacent_offsetNode_succ χ H hproper k hkH

/-- Installed-word form of the previous corollary. -/
theorem internallyProper_of_installed_of_properColoring
    (χ : Coloring T) (H : MaximalHelix T) (colors : List Color)
    (hinstalled : HelixWordInstalled χ H colors)
    (hproper : ProperColoring χ) :
    InternallyProper colors := by
  rw [hinstalled]
  exact internallyProper_helixColorWord χ H hproper

/-- Actual length-two M-terminal consequence.  Strong separation and
properness force the terminal residue to `xi.opposite`; the safe two-pair
bridge then forces the installed closing colour itself to be grey. -/
theorem safe_installed_twoPair_mEndpoint_closes_grey
    (χ : Coloring T) (H : MaximalHelix T) (xi entry : Parity)
    (pair : Color × Color)
    (hlength : H.length = 2)
    (hproper : ProperColoring χ)
    (hsep : StrongTwoSeparatedWith χ xi)
    (hM : IsMEndpoint H.terminalNode)
    (hsafe : Safe H.length entry xi.opposite pair.1)
    (hvalid : ValidTwoPair entry xi.opposite
      (levelParity (pairedLevel χ H.terminalNode)) pair)
    (hinstalled : HelixWordInstalled χ H [pair.1, pair.2]) :
    χ H.terminalNode = Color.grey := by
  have hterminal :=
    mEndpoint_level_residue χ xi hproper hsep H.terminalNode hM
  have hsafeTwo : Safe 2 entry xi.opposite pair.1 := by
    simpa [hlength] using hsafe
  rw [hterminal] at hvalid
  have hsecond := safe_twoPair_target_eta_second_grey
    xi xi.opposite entry pair rfl hsafeTwo hvalid
  have hlast := congrArg List.getLast? hinstalled
  have hactual : pair.2 = χ H.terminalNode := by
    simpa using hlast
  exact hactual.symm.trans hsecond

/-- Transfer-record form of the actual M-terminal consequence.  No separate
pair needs to be supplied: a length-two installed transfer is decomposed into
its two colours and discharged by the complete two-pair bridge. -/
theorem safe_installed_lengthTwoTransfer_mEndpoint_closes_grey
    (χ : Coloring T) (H : MaximalHelix T) (xi entry target : Parity)
    (first : Color)
    (hlength : H.length = 2)
    (hproper : ProperColoring χ)
    (hsep : StrongTwoSeparatedWith χ xi)
    (hM : IsMEndpoint H.terminalNode)
    (hsafe : Safe H.length entry xi.opposite first)
    (tr : LocalTransfer H.length entry xi.opposite target first)
    (hinstalled : HelixWordInstalled χ H tr.colors)
    (hentry : entry = levelParity (entryLevel χ H.headNode)) :
    χ H.terminalNode = Color.grey := by
  have hcolorsLength : tr.colors.length = 2 := tr.length_eq.trans hlength
  obtain ⟨a, b, hcolors⟩ := exists_pair_of_length_eq_two tr.colors hcolorsLength
  have hfirst : a = first := by
    have hhead := tr.first_eq
    rw [hcolors] at hhead
    exact Option.some.inj hhead
  have hinternal := tr.internallyProper
  have hgreys := tr.greysAtEta
  have hexit := tr.exit_eq
  rw [hcolors] at hinternal hgreys hexit
  have hterminal := installedLocalTransfer_terminalLevel χ H tr hinstalled hentry
  have hvalid : ValidTwoPair entry xi.opposite
      (levelParity (pairedLevel χ H.terminalNode)) (a, b) :=
    ⟨hinternal, hgreys, hexit.trans hterminal.symm⟩
  have hsafePair : Safe H.length entry xi.opposite a := by
    simpa [hfirst] using hsafe
  apply safe_installed_twoPair_mEndpoint_closes_grey χ H xi entry (a, b)
    hlength hproper hsep hM hsafePair hvalid
  exact hcolors.symm.trans hinstalled

end RNA
