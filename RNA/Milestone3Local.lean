module

public import RNA.HelixTransferBridge
public import RNA.LocalAllocations

@[expose] public section

set_option autoImplicit false

/-!
# Milestone 3 local construction and exposure bridges

This module supplies the construction-facing API missing after Milestone 2:
the deterministic two-pair transfer, the class-K transfer dispatch, a named
closing colour, and reverse bridges from installed local data to actual
exposures.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-- Deterministic length-two transfer using the four construction rows
`[first, first]`, `[first, grey]`, `[grey, black]`, and `[grey, grey]`. -/
def twoPairTransferOfSafe
    (xi eta entry target : Parity) (first : Color)
    (hopposite : eta = xi.opposite)
    (hsafe : Safe 2 entry eta first) :
    LocalTransfer 2 entry eta target first := by
  have hxi_ne_eta : xi ≠ eta := by
    rw [hopposite]
    exact xi.ne_opposite
  by_cases hentryXi : entry = xi
  · subst entry
    by_cases htargetXi : target = xi
    · subst target
      have hfirst : first.NonGrey := by
        rcases hsafe.admissible with h | ⟨_, hbad⟩
        · exact h
        · exact False.elim (hxi_ne_eta hbad)
      refine {
        colors := [first, first]
        length_eq := by simp
        first_eq := by simp
        internallyProper := ?_
        greysAtEta := ?_
        exit_eq := ?_
        closesNonGrey := ?_ }
      · cases first <;> simp_all [InternallyProper, ProperAdjacent,
          adjacentExposure, ProperExposure, Color.NonGrey]
      · cases first <;> simp_all [GreysAt, Color.NonGrey]
      · cases first <;> simp_all [exitResidue, Color.NonGrey]
      · intro _
        exact ⟨first, by simp, hfirst⟩
    · have htargetEta : target = eta := by
        rcases xi.eq_or_eq_opposite target with h | h
        · exact False.elim (htargetXi h)
        · exact h.trans hopposite.symm
      subst target
      have hfirst : first.NonGrey := by
        rcases hsafe.admissible with h | ⟨_, hbad⟩
        · exact h
        · exact False.elim (hxi_ne_eta hbad)
      refine {
        colors := [first, Color.grey]
        length_eq := by simp
        first_eq := by simp
        internallyProper := ?_
        greysAtEta := ?_
        exit_eq := ?_
        closesNonGrey := ?_ }
      · cases first <;> simp_all [InternallyProper, ProperAdjacent,
          adjacentExposure, ProperExposure, Color.NonGrey]
      · cases first <;> simp_all [GreysAt, Color.NonGrey,
          Parity.opposite]
      · cases first <;> simp_all [exitResidue, Color.NonGrey,
          Parity.opposite]
      · intro hbad
        exact False.elim (eta.ne_opposite hbad)
  · have hentryEta : entry = eta := by
      rcases xi.eq_or_eq_opposite entry with h | h
      · exact False.elim (hentryXi h)
      · exact h.trans hopposite.symm
    subst entry
    by_cases htargetXi : target = xi
    · subst target
      have hfirst : first = Color.grey := hsafe.short_eta_first_grey rfl
      subst first
      refine {
        colors := [Color.grey, Color.black]
        length_eq := by simp
        first_eq := by simp
        internallyProper := ?_
        greysAtEta := ?_
        exit_eq := ?_
        closesNonGrey := ?_ }
      · simp [InternallyProper, ProperAdjacent, adjacentExposure, ProperExposure]
      · simp [GreysAt]
      · simp [exitResidue, hopposite, Parity.opposite]
      · intro _
        exact ⟨Color.black, by simp, Color.black_nonGrey⟩
    · have htargetEta : target = eta := by
        rcases xi.eq_or_eq_opposite target with h | h
        · exact False.elim (htargetXi h)
        · exact h.trans hopposite.symm
      subst target
      have hfirst : first = Color.grey := hsafe.short_eta_first_grey rfl
      subst first
      refine {
        colors := [Color.grey, Color.grey]
        length_eq := by simp
        first_eq := by simp
        internallyProper := ?_
        greysAtEta := ?_
        exit_eq := ?_
        closesNonGrey := ?_ }
      · simp [InternallyProper, ProperAdjacent, adjacentExposure, ProperExposure]
      · simp [GreysAt]
      · simp [exitResidue]
      · intro hbad
        exact False.elim (eta.ne_opposite hbad)

/-- Unified local transfer for a class-K maximal helix. -/
def transferForClassKHelix
    (hK : InTargetClassK T) (H : MaximalHelix T)
    (entry eta target : Parity) (first : Color)
    (hsafe : Safe H.length entry eta first) :
    LocalTransfer H.length entry eta target first := by
  by_cases htwo : H.length = 2
  · rw [htwo] at hsafe ⊢
    exact twoPairTransferOfSafe eta.opposite eta entry target first
      (Parity.opposite_opposite eta).symm hsafe
  · have hone := targetClass_no_length_one hK H
    have hlong : 3 ≤ H.length := by
      have hpos := H.positive
      omega
    exact longHelixTransfer_of_safe H.length entry eta target first hlong hsafe

@[simp] theorem twoPairTransferOfSafe_colors_xi_xi
    (xi eta : Parity) (first : Color)
    (hopposite : eta = xi.opposite)
    (hsafe : Safe 2 xi eta first) :
    (twoPairTransferOfSafe xi eta xi xi first hopposite hsafe).colors =
      [first, first] := by
  simp [twoPairTransferOfSafe]

@[simp] theorem twoPairTransferOfSafe_colors_xi_eta
    (xi eta : Parity) (first : Color)
    (hopposite : eta = xi.opposite)
    (hsafe : Safe 2 xi eta first) :
    (twoPairTransferOfSafe xi eta xi eta first hopposite hsafe).colors =
      [first, Color.grey] := by
  simp [twoPairTransferOfSafe, hopposite]

@[simp] theorem twoPairTransferOfSafe_colors_eta_xi
    (xi eta : Parity) (first : Color)
    (hopposite : eta = xi.opposite)
    (hsafe : Safe 2 eta eta first) :
    (twoPairTransferOfSafe xi eta eta xi first hopposite hsafe).colors =
      [Color.grey, Color.black] := by
  have hfirst : first = Color.grey := hsafe.short_eta_first_grey rfl
  subst first
  simp [twoPairTransferOfSafe, hopposite]

@[simp] theorem twoPairTransferOfSafe_colors_eta_eta
    (xi eta : Parity) (first : Color)
    (hopposite : eta = xi.opposite)
    (hsafe : Safe 2 eta eta first) :
    (twoPairTransferOfSafe xi eta eta eta first hopposite hsafe).colors =
      [Color.grey, Color.grey] := by
  have hfirst : first = Color.grey := hsafe.short_eta_first_grey rfl
  subst first
  simp [twoPairTransferOfSafe, hopposite]

namespace LocalTransfer

/-- Last colour of a positive-length transfer. -/
def closingColor {h : Nat} {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer h entry eta target first) (hpos : 0 < h) : Color :=
  tr.colors.getLast (by
    intro hempty
    have hzero : tr.colors.length = 0 := by simp [hempty]
    rw [tr.length_eq] at hzero
    omega)

/-- `closingColor` is the actual last list element. -/
@[simp] theorem getLast?_eq_some_closingColor
    {h : Nat} {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer h entry eta target first) (hpos : 0 < h) :
    tr.colors.getLast? = some (tr.closingColor hpos) := by
  let hne : tr.colors ≠ [] := by
    intro hempty
    have hzero : tr.colors.length = 0 := by simp [hempty]
    rw [tr.length_eq] at hzero
    omega
  rw [List.getLast?_eq_getLast_of_ne_nil hne]
  rfl

/-- An opposite-of-grey exit has a non-grey named closing colour. -/
theorem closingColor_nonGrey
    {h : Nat} {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer h entry eta target first) (hpos : 0 < h)
    (htarget : target = eta.opposite) :
    (tr.closingColor hpos).NonGrey := by
  obtain ⟨c, hlast, hc⟩ := tr.closesNonGrey htarget
  rw [tr.getLast?_eq_some_closingColor hpos] at hlast
  have heq : tr.closingColor hpos = c := Option.some.inj hlast
  simpa [heq] using hc

end LocalTransfer

/-- Installation identifies the named closing colour with the actual terminal
node colour. -/
theorem installedLocalTransfer_terminalColor_eq_closingColor
    (χ : Coloring T) (H : MaximalHelix T)
    {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer H.length entry eta target first)
    (hinstalled : HelixWordInstalled χ H tr.colors) :
    χ H.terminalNode = tr.closingColor H.positive := by
  have hlast := congrArg List.getLast? hinstalled
  rw [tr.getLast?_eq_some_closingColor H.positive,
    helixColorWord_getLast?] at hlast
  exact Option.some.inj hlast.symm

/-- Installation identifies the fixed first colour with the actual head. -/
theorem installedLocalTransfer_headColor
    (χ : Coloring T) (H : MaximalHelix T)
    {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer H.length entry eta target first)
    (hinstalled : HelixWordInstalled χ H tr.colors) :
    χ H.headNode = first := by
  have hhead := tr.first_eq
  rw [hinstalled, helixColorWord_head] at hhead
  exact Option.some.inj hhead

/-- Extract pointwise adjacent properness from the recursive word predicate. -/
theorem internallyProper_get_succ
    (colors : List Color) (hproper : InternallyProper colors)
    (k : Nat) (hk : k + 1 < colors.length) :
    ProperAdjacent
      (colors.get ⟨k, by omega⟩)
      (colors.get ⟨k + 1, hk⟩) := by
  induction k generalizing colors with
  | zero =>
      cases colors with
      | nil => simp at hk
      | cons a rest =>
          cases rest with
          | nil => simp at hk
          | cons b tail =>
              exact hproper.1
  | succ k ih =>
      cases colors with
      | nil => simp at hk
      | cons a rest =>
          cases rest with
          | nil => simp at hk
          | cons b tail =>
              have hk' : k + 1 < (b :: tail).length := by
                simpa [Nat.add_assoc] using hk
              simpa using ih (b :: tail) hproper.2 hk'

/-- A nonterminal helix member has exactly the adjacent local exposure: the
next helix pair is its unique paired child and it has no unpaired child. -/
theorem exposedMultiset_offsetNode_eq_adjacentExposure
    (χ : Coloring T) (H : MaximalHelix T)
    (k : Nat) (hk : k + 1 < H.length) :
    exposedMultiset χ (some (H.offsetNode ⟨k, by omega⟩)) =
      adjacentExposure
        (χ (H.offsetNode ⟨k, by omega⟩))
        (χ (H.offsetNode ⟨k + 1, hk⟩)) := by
  have hshape := maximalHelix_consecutive_tree_shape H k hk
  rw [exposedMultiset_paired]
  unfold childColorMultiset adjacentExposure
  rw [hshape.1]
  simp

theorem properAdjacent_offsetNode_succ_of_installed_of_internallyProper
    (χ : Coloring T) (H : MaximalHelix T) (colors : List Color)
    (hinstalled : HelixWordInstalled χ H colors)
    (hproper : InternallyProper colors)
    (k : Nat) (hk : k + 1 < H.length) :
    ProperAdjacent
      (χ (H.offsetNode ⟨k, by omega⟩))
      (χ (H.offsetNode ⟨k + 1, hk⟩)) := by
  unfold HelixWordInstalled at hinstalled
  subst colors
  have hlocal := internallyProper_get_succ (helixColorWord χ H) hproper k (by
    rw [helixColorWord_length]
    exact hk)
  rw [helixColorWord_get, helixColorWord_get] at hlocal
  simpa using hlocal

/-- Construction-direction internal exposure bridge for an installed proper
word. -/
theorem properExposure_internalHelix_of_installed
    (χ : Coloring T) (H : MaximalHelix T) (colors : List Color)
    (hinstalled : HelixWordInstalled χ H colors)
    (hproper : InternallyProper colors)
    (k : Nat) (hk : k + 1 < H.length) :
    ProperExposure
      (exposedMultiset χ (some (H.offsetNode ⟨k, by omega⟩))) := by
  rw [exposedMultiset_offsetNode_eq_adjacentExposure χ H k hk]
  exact properAdjacent_offsetNode_succ_of_installed_of_internallyProper
    χ H colors hinstalled hproper k hk

theorem installedLocalTransfer_internalExposure
    (χ : Coloring T) (H : MaximalHelix T)
    {entry eta target : Parity} {first : Color}
    (tr : LocalTransfer H.length entry eta target first)
    (hinstalled : HelixWordInstalled χ H tr.colors)
    (k : Nat) (hk : k + 1 < H.length) :
    ProperExposure
      (exposedMultiset χ (some (H.offsetNode ⟨k, by omega⟩))) :=
  properExposure_internalHelix_of_installed χ H tr.colors hinstalled
    tr.internallyProper k hk

/-- Membership-form internal exposure bridge: every nonterminal member of an
installed internally proper helix has a proper actual exposure. -/
theorem properExposure_nonterminalHelixMember_of_installed
    (χ : Coloring T) (H : MaximalHelix T) (colors : List Color)
    (hinstalled : HelixWordInstalled χ H colors)
    (hproper : InternallyProper colors)
    (p : PairedNode T) (hp : p.val ∈ helixMembers T H)
    (hne : p ≠ H.terminalNode) :
    ProperExposure (exposedMultiset χ (some p)) := by
  rw [H.helixMembers_eq_offset_image] at hp
  obtain ⟨k, _hk, hkp⟩ := Finset.mem_map.mp hp
  have hpnode : H.offsetNode k = p := by
    apply Subtype.ext
    exact hkp
  have hsucc : k.val + 1 < H.length := by
    by_contra hnot
    have hlast : k.val = H.length - 1 := by omega
    apply hne
    rw [← hpnode]
    apply congrArg H.offsetNode
    apply Fin.ext
    exact hlast
  rw [← hpnode]
  exact properExposure_internalHelix_of_installed χ H colors hinstalled
    hproper k.val hsucc

/-- Pointwise statement that an actual colouring installs an indexed child
port assignment. -/
def ChildPortsInstalled (χ : Coloring T) (p : PairedOrRootNode T)
    (A : ChildPortAssignment T p) : Prop :=
  ∀ i, χ (orderedPairedChild T p i) = A i

/-- Installed pointwise ports have exactly the displayed child-colour
multiset. -/
theorem childColorMultiset_eq_portMultiset_of_childPortsInstalled
    (χ : Coloring T) (p : PairedOrRootNode T)
    (A : ChildPortAssignment T p)
    (hinstalled : ChildPortsInstalled χ p A) :
    childColorMultiset χ p = portMultiset A := by
  let childEmbedding : Fin (pairedChildCount T p) ↪ PairedNode T :=
    ⟨orderedPairedChild T p, orderedPairedChild_injective T p⟩
  have hchildren : Finset.univ.map childEmbedding = pairedChildren T p := by
    ext c
    constructor
    · intro hc
      obtain ⟨i, _hi, hic⟩ := Finset.mem_map.mp hc
      rw [← hic]
      exact orderedPairedChild_mem T p i
    · intro hc
      apply Finset.mem_map.mpr
      refine ⟨pairedChildIndex T p c hc, Finset.mem_univ _, ?_⟩
      exact orderedPairedChild_pairedChildIndex T p c hc
  calc
    childColorMultiset χ p = (pairedChildren T p).val.map χ := rfl
    _ = (Finset.univ.map childEmbedding).val.map χ := by rw [hchildren]
    _ = Finset.univ.val.map (χ ∘ childEmbedding) := by
      rw [Finset.map_val, Multiset.map_map]
    _ = Finset.univ.val.map A := by
      congr 1
      funext i
      exact hinstalled i
    _ = portMultiset A := rfl

/-- Construction-direction terminal exposure bridge. -/
theorem LoopAllocation.properActualExposure
    {hK : InTargetClassK T} {p : PairedNode T} {e : EndpointType}
    {a : Color} {xi : Parity}
    (A : LoopAllocation T hK p e a xi) (χ : Coloring T)
    (hclosing : χ p = a)
    (hports : ChildPortsInstalled χ (some p) A.ports) :
    ProperExposure (exposedMultiset χ (some p)) := by
  rw [exposedMultiset_paired, hclosing,
    childColorMultiset_eq_portMultiset_of_childPortsInstalled χ (some p)
      A.ports hports]
  exact A.proper

/-- Construction-direction root exposure bridge. -/
theorem RootAllocation.properActualExposure
    {hK : InTargetClassK T}
    (A : RootAllocation T hK) (χ : Coloring T)
    (hports : ChildPortsInstalled χ none A.ports) :
    ProperExposure (exposedMultiset χ none) := by
  rw [exposedMultiset_root,
    childColorMultiset_eq_portMultiset_of_childPortsInstalled χ none
      A.ports hports]
  exact A.proper

end RNA
