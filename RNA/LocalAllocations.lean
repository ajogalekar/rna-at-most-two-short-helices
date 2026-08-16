module

public import RNA.Endpoint
public import RNA.HelixTransfer

@[expose] public section

set_option autoImplicit false

/-!
# Root and loop port allocations

A port is the colour of the first pair in an outgoing maximal helix.  The
finite tables below are executable assignments, not merely multisets.  A
`PortAssignment d` assigns one colour to every slot in an ordered family of
`d` actual children; `assignedChildPorts` pairs those slots with the canonical
backbone ordering of a node's paired children.
-/

namespace RNA

variable {n : Nat} {T : SecondaryStructure n}

/-! ## Assignment algebra -/

/-- One port colour for every one of `d` ordered outgoing children. -/
abbrev PortAssignment (d : Nat) := Fin d → Color

/-- The multiset underlying an indexed port assignment. -/
def portMultiset {d : Nat} (A : PortAssignment d) : Multiset Color :=
  Finset.univ.val.map A

/-- Reindex an assignment along an equivalence of its ordered slots. -/
def PortAssignment.reindex {d e : Nat} (A : PortAssignment d)
    (σ : Fin e ≃ Fin d) : PortAssignment e :=
  A ∘ σ

@[simp]
theorem portMultiset_reindex {d e : Nat} (A : PortAssignment d)
    (σ : Fin e ≃ Fin d) :
    portMultiset (A.reindex σ) = portMultiset A := by
  change Multiset.map (A ∘ σ) (Finset.univ : Finset (Fin e)).val =
    Multiset.map A (Finset.univ : Finset (Fin d)).val
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- The exposed multiset at a nonroot loop with closing colour `a`. -/
def loopPortExposure {d : Nat} (a : Color) (A : PortAssignment d) :
    Multiset Color :=
  {a.inv} + portMultiset A

/-- The root exposure has no closing incidence. -/
def rootPortExposure {d : Nat} (A : PortAssignment d) : Multiset Color :=
  portMultiset A

/-- Every colour is admissible when a helix enters at the grey residue. -/
theorem Color.admissibleAt_self (c : Color) (eta : Parity) :
    c.AdmissibleAt eta eta := by
  cases c <;> simp [Color.AdmissibleAt]

/-! ## Root rows -/

/-- The four displayed root rows (the two hypotheses leading to the same
one- or two-port row intentionally share a table row). -/
inductive RootRow where
  | xiOne
  | xiTwo
  | etaThree
  | etaFour
  deriving DecidableEq, Repr

namespace RootRow

def count : RootRow → Nat
  | xiOne => 1
  | xiTwo => 2
  | etaThree => 3
  | etaFour => 4

/-- The manuscript's residue `xi` for a root row. -/
def xi : RootRow → Parity
  | xiOne | xiTwo => 0
  | etaThree | etaFour => 1

/-- The opposite, grey residue `eta`. -/
def eta (r : RootRow) : Parity := r.xi.opposite

/-- Entry residue at each displayed root interface. -/
def entry : (r : RootRow) → Parity
  | xiOne | xiTwo => 0
  | etaThree | etaFour => 0

/-- The displayed root port vectors. -/
def ports : (r : RootRow) → PortAssignment r.count
  | xiOne => ![Color.black]
  | xiTwo => ![Color.black, Color.white]
  | etaThree => ![Color.black, Color.white, Color.grey]
  | etaFour => ![Color.black, Color.white, Color.grey, Color.grey]

@[simp] theorem entry_eq_xi : (r : RootRow) →
    r = xiOne ∨ r = xiTwo → r.entry = r.xi := by
  intro r hr
  rcases hr with rfl | rfl <;> rfl

@[simp] theorem entry_eq_eta : (r : RootRow) →
    r = etaThree ∨ r = etaFour → r.entry = r.eta := by
  intro r hr
  rcases hr with rfl | rfl <;> decide

/-- Every displayed root exposure respects `(1,1,2)`. -/
theorem proper (r : RootRow) : ProperExposure (rootPortExposure r.ports) := by
  cases r <;> decide

/-- Every displayed port is admissible at its selected root interface. -/
theorem admissible (r : RootRow) (i : Fin r.count) :
    (r.ports i).AdmissibleAt r.entry r.eta := by
  cases r <;> fin_cases i <;> decide

/-- Ports in either `xi` root row are non-grey.  Thus a short root child in
such a row automatically receives a non-grey first colour. -/
theorem xi_port_nonGrey (r : RootRow)
    (hr : r = xiOne ∨ r = xiTwo) (i : Fin r.count) :
    (r.ports i).NonGrey := by
  rcases hr with rfl | rfl <;> fin_cases i <;> decide

end RootRow

/-- The root rows with three or four children, where the interface is `eta`
and a grey port can be reserved for an arbitrary designated child. -/
inductive EtaRootRow where
  | three
  | four
  deriving DecidableEq, Repr

namespace EtaRootRow

def count : EtaRootRow → Nat
  | three => 3
  | four => 4

def basePorts : (r : EtaRootRow) → PortAssignment r.count
  | three => ![Color.black, Color.white, Color.grey]
  | four => ![Color.black, Color.white, Color.grey, Color.grey]

/-- A fixed grey slot, later swapped with the actual short child. -/
def greySlot : (r : EtaRootRow) → Fin r.count
  | three => ⟨2, by decide⟩
  | four => ⟨2, by decide⟩

@[simp]
theorem basePorts_greySlot (r : EtaRootRow) :
    r.basePorts r.greySlot = Color.grey := by
  cases r <;> decide

/-- Move a displayed grey port to an arbitrary designated actual-child slot. -/
def portsAt (r : EtaRootRow) (short : Fin r.count) :
    PortAssignment r.count :=
  r.basePorts.reindex (Equiv.swap r.greySlot short)

@[simp]
theorem portsAt_short (r : EtaRootRow) (short : Fin r.count) :
    r.portsAt short short = Color.grey := by
  simp [portsAt, PortAssignment.reindex]

theorem portsAt_multiset (r : EtaRootRow) (short : Fin r.count) :
    portMultiset (r.portsAt short) = portMultiset r.basePorts := by
  exact portMultiset_reindex r.basePorts (Equiv.swap r.greySlot short)

/-- Reserving a grey port for any selected root child preserves properness. -/
theorem portsAt_proper (r : EtaRootRow) (short : Fin r.count) :
    ProperExposure (rootPortExposure (r.portsAt short)) := by
  rw [rootPortExposure, portsAt_multiset]
  cases r <;> decide

/-- Every selected/root port is admissible because these rows enter at eta. -/
theorem portsAt_admissible (r : EtaRootRow) (short i : Fin r.count)
    (eta : Parity) :
    (r.portsAt short i).AdmissibleAt eta eta :=
  Color.admissibleAt_self _ _

end EtaRootRow

/-! ## E and L rows -/

/-- The empty port vector. -/
def noPorts : PortAssignment 0 := ![]

/-- A single outgoing port equal to the closing colour. -/
def lOnePort (a : Color) : PortAssignment 1 := ![a]

/-- An E loop has only its singleton closing exposure. -/
theorem eExposure_proper (a : Color) :
    ProperExposure (loopPortExposure a noPorts) := by
  cases a <;> decide

/-- The same singleton row covers an L loop with no paired child. -/
theorem lZeroExposure_proper (a : Color) (ha : a.NonGrey) :
    ProperExposure (loopPortExposure a noPorts) := by
  rcases (Color.nonGrey_iff a).1 ha with hblack | hwhite
  · subst a
    decide
  · subst a
    decide

/-- With one outgoing helix, an L loop assigns it the same non-grey colour as
the closing pair, producing `{inv(a),a}`. -/
theorem lOneExposure_eq (a : Color) :
    loopPortExposure a (lOnePort a) = ({a.inv, a} : Multiset Color) := by
  cases a <;> decide

theorem lOneExposure_proper (a : Color) (ha : a.NonGrey) :
    ProperExposure (loopPortExposure a (lOnePort a)) := by
  rcases (Color.nonGrey_iff a).1 ha with hblack | hwhite
  · subst a
    decide
  · subst a
    decide

@[simp]
theorem lOnePort_nonGrey (a : Color) (ha : a.NonGrey) :
    (lOnePort a 0).NonGrey := by
  simpa [lOnePort] using ha

theorem lOnePort_admissible (a : Color) (ha : a.NonGrey)
    (entry eta : Parity) :
    (lOnePort a 0).AdmissibleAt entry eta := by
  exact Or.inl (lOnePort_nonGrey a ha)

/-! ## M rows -/

/-- The two possible outgoing arities of an M loop. -/
inductive MArity where
  | two
  | three
  deriving DecidableEq, Repr

namespace MArity

def count : MArity → Nat
  | two => 2
  | three => 3

def firstSlot : (d : MArity) → Fin d.count
  | two => ⟨0, by decide⟩
  | three => ⟨0, by decide⟩

end MArity

/-- The six ordinary M allocations. -/
def ordinaryMPorts (a : Color) : (d : MArity) → PortAssignment d.count
  | .two => match a with
    | .black => ![Color.black, Color.grey]
    | .white => ![Color.white, Color.grey]
    | .grey => ![Color.black, Color.white]
  | .three => match a with
    | .black => ![Color.black, Color.grey, Color.grey]
    | .white => ![Color.white, Color.grey, Color.grey]
    | .grey => ![Color.black, Color.white, Color.grey]

/-- The six exact ordinary exposed multisets from the manuscript. -/
def ordinaryMExposure : Color → MArity → Multiset Color
  | .black, .two => {Color.white, Color.black, Color.grey}
  | .black, .three => {Color.white, Color.black, Color.grey, Color.grey}
  | .white, .two => {Color.black, Color.white, Color.grey}
  | .white, .three => {Color.black, Color.white, Color.grey, Color.grey}
  | .grey, .two => {Color.grey, Color.black, Color.white}
  | .grey, .three => {Color.grey, Color.black, Color.white, Color.grey}

theorem ordinaryMExposure_eq (a : Color) (d : MArity) :
    loopPortExposure a (ordinaryMPorts a d) = ordinaryMExposure a d := by
  cases a <;> cases d <;> decide

/-- All six ordinary rows fit the exposure capacities. -/
theorem ordinaryMExposure_proper (a : Color) (d : MArity) :
    ProperExposure (loopPortExposure a (ordinaryMPorts a d)) := by
  cases a <;> cases d <;> decide

/-- Every ordinary M port is admissible at the M interface residue `eta`. -/
theorem ordinaryMPort_admissible (a : Color) (d : MArity)
    (i : Fin d.count) (eta : Parity) :
    (ordinaryMPorts a d i).AdmissibleAt eta eta :=
  Color.admissibleAt_self _ _

/-- Ordinary displayed ports may be permuted into any order without changing
the intended exposure row. -/
theorem ordinaryM_reindex_exposure_eq (a : Color) (d : MArity)
    (σ : Equiv.Perm (Fin d.count)) :
    loopPortExposure a ((ordinaryMPorts a d).reindex σ) =
      ordinaryMExposure a d := by
  rw [loopPortExposure, portMultiset_reindex]
  exact ordinaryMExposure_eq a d

/-- Designated M rows put the distinguished grey port in slot zero. -/
def designatedMBasePorts (a : Color) :
    (d : MArity) → PortAssignment d.count
  | .two => match a with
    | .black => ![Color.grey, Color.black]
    | .white => ![Color.grey, Color.white]
    | .grey => ![Color.grey, Color.black]
  | .three => match a with
    | .black => ![Color.grey, Color.black, Color.grey]
    | .white => ![Color.grey, Color.white, Color.grey]
    | .grey => ![Color.grey, Color.black, Color.white]

@[simp]
theorem designatedMBasePorts_first (a : Color) (d : MArity) :
    designatedMBasePorts a d d.firstSlot = Color.grey := by
  cases a <;> cases d <;> decide

/-- Move the distinguished grey port to an arbitrary selected child slot. -/
def designatedMPortsAt (a : Color) (d : MArity) (short : Fin d.count) :
    PortAssignment d.count :=
  (designatedMBasePorts a d).reindex (Equiv.swap d.firstSlot short)

@[simp]
theorem designatedMPortsAt_short (a : Color) (d : MArity)
    (short : Fin d.count) :
    designatedMPortsAt a d short short = Color.grey := by
  simp [designatedMPortsAt, PortAssignment.reindex]

/-- The six exact designated exposed multisets. -/
def designatedMExposure : Color → MArity → Multiset Color
  | .black, .two => {Color.white, Color.grey, Color.black}
  | .black, .three => {Color.white, Color.grey, Color.black, Color.grey}
  | .white, .two => {Color.black, Color.grey, Color.white}
  | .white, .three => {Color.black, Color.grey, Color.white, Color.grey}
  | .grey, .two => {Color.grey, Color.grey, Color.black}
  | .grey, .three => {Color.grey, Color.grey, Color.black, Color.white}

theorem designatedMExposure_eq (a : Color) (d : MArity)
    (short : Fin d.count) :
    loopPortExposure a (designatedMPortsAt a d short) =
      designatedMExposure a d := by
  unfold designatedMPortsAt
  rw [loopPortExposure, portMultiset_reindex]
  cases a <;> cases d <;> decide

/-- All six designated rows fit the exposure capacities. -/
theorem designatedMExposure_proper (a : Color) (d : MArity)
    (short : Fin d.count) :
    ProperExposure (loopPortExposure a (designatedMPortsAt a d short)) := by
  rw [designatedMExposure_eq]
  cases a <;> cases d <;> decide

/-- The tight designated row uses exactly `{G,G,B}`. -/
theorem designatedM_tight_exposure (short : Fin MArity.two.count) :
    loopPortExposure Color.grey
      (designatedMPortsAt Color.grey .two short) =
      ({Color.grey, Color.grey, Color.black} : Multiset Color) := by
  exact designatedMExposure_eq Color.grey .two short

theorem designatedM_tight_counts (short : Fin MArity.two.count) :
    (loopPortExposure Color.grey
        (designatedMPortsAt Color.grey .two short)).count Color.black = 1 ∧
    (loopPortExposure Color.grey
        (designatedMPortsAt Color.grey .two short)).count Color.white = 0 ∧
    (loopPortExposure Color.grey
        (designatedMPortsAt Color.grey .two short)).count Color.grey = 2 := by
  rw [designatedM_tight_exposure]
  decide

/-- Every designated M port is admissible at the M interface residue `eta`. -/
theorem designatedMPort_admissible (a : Color) (d : MArity)
    (short i : Fin d.count) (eta : Parity) :
    (designatedMPortsAt a d short i).AdmissibleAt eta eta :=
  Color.admissibleAt_self _ _

/-- In a designated row, any permutation that sends the selected short slot
to the displayed first (grey) slot is valid; hence the remaining colours can
be assigned to the remaining long children in arbitrary order. -/
theorem designatedM_reindex (a : Color) (d : MArity)
    (short : Fin d.count) (σ : Equiv.Perm (Fin d.count))
    (hshort : σ short = d.firstSlot) :
    ((designatedMBasePorts a d).reindex σ) short = Color.grey ∧
      loopPortExposure a ((designatedMBasePorts a d).reindex σ) =
        designatedMExposure a d ∧
      ProperExposure
        (loopPortExposure a ((designatedMBasePorts a d).reindex σ)) := by
  constructor
  · simp [PortAssignment.reindex, hshort]
  constructor
  · rw [loopPortExposure, portMultiset_reindex]
    cases a <;> cases d <;> decide
  · rw [loopPortExposure, portMultiset_reindex]
    cases a <;> cases d <;> decide

/-! ## Assignments to the actual ordered paired children -/

/-- Paired children alone, in increasing backbone order. -/
def orderedPairedChildren (T : SecondaryStructure n)
    (p : PairedOrRootNode T) : List (PairedNode T) :=
  (pairedChildren T p).sort

@[simp]
theorem orderedPairedChildren_length (T : SecondaryStructure n)
    (p : PairedOrRootNode T) :
    (orderedPairedChildren T p).length = pairedChildCount T p := by
  simp [orderedPairedChildren, pairedChildCount]

/-- The actual child occupying an ordered assignment slot. -/
def orderedPairedChild (T : SecondaryStructure n) (p : PairedOrRootNode T)
    (i : Fin (pairedChildCount T p)) : PairedNode T :=
  (orderedPairedChildren T p).get
    (Fin.cast (orderedPairedChildren_length T p).symm i)

theorem orderedPairedChild_mem (T : SecondaryStructure n)
    (p : PairedOrRootNode T) (i : Fin (pairedChildCount T p)) :
    orderedPairedChild T p i ∈ pairedChildren T p := by
  unfold orderedPairedChild
  have hmem := List.get_mem (orderedPairedChildren T p)
    (Fin.cast (orderedPairedChildren_length T p).symm i)
  simpa only [orderedPairedChildren, Finset.mem_sort] using hmem

/-- A port vector indexed by the actual ordered paired children of `p`. -/
abbrev ChildPortAssignment (T : SecondaryStructure n)
    (p : PairedOrRootNode T) :=
  PortAssignment (pairedChildCount T p)

/-- Explicit child/port pairs, in the target's backbone order. -/
def assignedChildPorts (T : SecondaryStructure n) (p : PairedOrRootNode T)
    (A : ChildPortAssignment T p) : List (PairedNode T × Color) :=
  List.ofFn (fun i => (orderedPairedChild T p i, A i))

@[simp]
theorem assignedChildPorts_length (T : SecondaryStructure n)
    (p : PairedOrRootNode T) (A : ChildPortAssignment T p) :
    (assignedChildPorts T p A).length = pairedChildCount T p := by
  simp [assignedChildPorts]

/-- Every assigned pair names an actual paired child. -/
theorem assignedChildPorts_fst_mem (T : SecondaryStructure n)
    (p : PairedOrRootNode T) (A : ChildPortAssignment T p)
    (q : PairedNode T × Color) (hq : q ∈ assignedChildPorts T p A) :
    q.1 ∈ pairedChildren T p := by
  simp only [assignedChildPorts, List.mem_ofFn] at hq
  obtain ⟨i, hi⟩ := hq
  rw [← hi]
  exact orderedPairedChild_mem T p i

/-- Choose the unique ordered slot of an actual paired child. -/
noncomputable def pairedChildIndex (T : SecondaryStructure n)
    (p : PairedOrRootNode T) (u : PairedNode T)
    (hu : u ∈ pairedChildren T p) : Fin (pairedChildCount T p) :=
  let hulist : u ∈ orderedPairedChildren T p := by
    simpa [orderedPairedChildren] using hu
  Fin.cast (orderedPairedChildren_length T p)
    (Classical.choose (List.get_of_mem hulist))

@[simp]
theorem orderedPairedChild_pairedChildIndex (T : SecondaryStructure n)
    (p : PairedOrRootNode T) (u : PairedNode T)
    (hu : u ∈ pairedChildren T p) :
    orderedPairedChild T p (pairedChildIndex T p u hu) = u := by
  unfold pairedChildIndex orderedPairedChild
  simp only [Fin.cast_cast, Fin.cast_eq_self]
  exact Classical.choose_spec (List.get_of_mem (by
    simpa [orderedPairedChildren] using hu))

/-- Ordered child slots name distinct actual paired children. -/
theorem orderedPairedChild_injective (T : SecondaryStructure n)
    (p : PairedOrRootNode T) :
    Function.Injective (orderedPairedChild T p) := by
  intro i j hij
  have hnodup : (orderedPairedChildren T p).Nodup :=
    Finset.sort_nodup _ _
  have hcast :
      Fin.cast (orderedPairedChildren_length T p).symm i =
        Fin.cast (orderedPairedChildren_length T p).symm j := by
    apply hnodup.injective_get
    simpa [orderedPairedChild] using hij
  exact (Fin.cast_inj (orderedPairedChildren_length T p).symm).mp hcast

/-! ## Reindexing table rows onto actual child lists -/

/-- Install a length-`d` table row on an actual interface whose paired-child
count is proved to be `d`. -/
def installPortRow (T : SecondaryStructure n) (p : PairedOrRootNode T)
    {d : Nat} (A : PortAssignment d)
    (hcount : pairedChildCount T p = d) : ChildPortAssignment T p :=
  A.reindex (finCongr hcount)

@[simp]
theorem installPortRow_multiset (T : SecondaryStructure n)
    (p : PairedOrRootNode T) {d : Nat} (A : PortAssignment d)
    (hcount : pairedChildCount T p = d) :
    portMultiset (installPortRow T p A hcount) = portMultiset A := by
  exact portMultiset_reindex A (finCongr hcount)

/-- Install one of the ordinary M rows on actual ordered children. -/
def ordinaryMActualPorts (T : SecondaryStructure n) (p : PairedNode T)
    (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some p) = d.count) :
    ChildPortAssignment T (some p) :=
  installPortRow T (some p) (ordinaryMPorts a d) hcount

theorem ordinaryMActualExposure_proper (T : SecondaryStructure n)
    (p : PairedNode T) (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some p) = d.count) :
    ProperExposure (loopPortExposure a
      (ordinaryMActualPorts T p a d hcount)) := by
  unfold ordinaryMActualPorts
  rw [loopPortExposure, installPortRow_multiset]
  exact ordinaryMExposure_proper a d

theorem ordinaryMActualExposure_eq (T : SecondaryStructure n)
    (p : PairedNode T) (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some p) = d.count) :
    loopPortExposure a (ordinaryMActualPorts T p a d hcount) =
      ordinaryMExposure a d := by
  unfold ordinaryMActualPorts
  rw [loopPortExposure, installPortRow_multiset]
  exact ordinaryMExposure_eq a d

theorem ordinaryMActualPort_admissible (T : SecondaryStructure n)
    (p : PairedNode T) (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some p) = d.count)
    (i : Fin (pairedChildCount T (some p))) (eta : Parity) :
    (ordinaryMActualPorts T p a d hcount i).AdmissibleAt eta eta :=
  Color.admissibleAt_self _ _

/-- Install a designated-grey M row and move its distinguished grey port to
the ordered slot of an actual short child. -/
noncomputable def designatedMActualPorts (T : SecondaryStructure n)
    (p : PairedNode T) (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some p) = d.count)
    (short : PairedNode T) (hshort : short ∈ pairedChildren T (some p)) :
    ChildPortAssignment T (some p) :=
  let actualShort := pairedChildIndex T (some p) short hshort
  let tableShort := finCongr hcount actualShort
  installPortRow T (some p) (designatedMPortsAt a d tableShort) hcount

@[simp]
theorem designatedMActualPorts_short (T : SecondaryStructure n)
    (p : PairedNode T) (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some p) = d.count)
    (short : PairedNode T) (hshort : short ∈ pairedChildren T (some p)) :
    designatedMActualPorts T p a d hcount short hshort
      (pairedChildIndex T (some p) short hshort) = Color.grey := by
  simp [designatedMActualPorts, installPortRow, PortAssignment.reindex]

theorem designatedMActualExposure_proper (T : SecondaryStructure n)
    (p : PairedNode T) (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some p) = d.count)
    (short : PairedNode T) (hshort : short ∈ pairedChildren T (some p)) :
    ProperExposure (loopPortExposure a
      (designatedMActualPorts T p a d hcount short hshort)) := by
  unfold designatedMActualPorts
  rw [loopPortExposure, installPortRow_multiset]
  exact designatedMExposure_proper a d _

theorem designatedMActualExposure_eq (T : SecondaryStructure n)
    (p : PairedNode T) (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some p) = d.count)
    (short : PairedNode T) (hshort : short ∈ pairedChildren T (some p)) :
    loopPortExposure a
      (designatedMActualPorts T p a d hcount short hshort) =
      designatedMExposure a d := by
  unfold designatedMActualPorts
  rw [loopPortExposure, installPortRow_multiset]
  exact designatedMExposure_eq a d _

theorem designatedMActualPort_admissible (T : SecondaryStructure n)
    (p : PairedNode T) (a : Color) (d : MArity)
    (hcount : pairedChildCount T (some p) = d.count)
    (short : PairedNode T) (hshort : short ∈ pairedChildren T (some p))
    (i : Fin (pairedChildCount T (some p))) (eta : Parity) :
    (designatedMActualPorts T p a d hcount short hshort i).AdmissibleAt eta eta :=
  Color.admissibleAt_self _ _

/-! ## Actual outgoing maximal helices -/

/-- The unique outgoing maximal helix at an ordered child of a loop node. -/
noncomputable def outgoingHelixAtLoopSlot (T : SecondaryStructure n)
    (p : PairedNode T) (hp : IsLoopNode p)
    (i : Fin (pairedChildCount T (some p))) : MaximalHelix T :=
  Classical.choose (existsUnique_outgoing_of_loop_child p hp
    (orderedPairedChild T (some p) i)
    (orderedPairedChild_mem T (some p) i))

@[simp]
theorem outgoingHelixAtLoopSlot_head (T : SecondaryStructure n)
    (p : PairedNode T) (hp : IsLoopNode p)
    (i : Fin (pairedChildCount T (some p))) :
    (outgoingHelixAtLoopSlot T p hp i).headNode =
      orderedPairedChild T (some p) i :=
  (Classical.choose_spec (existsUnique_outgoing_of_loop_child p hp
    (orderedPairedChild T (some p) i)
    (orderedPairedChild_mem T (some p) i))).1

/-- The unique outgoing maximal helix at an ordered root child. -/
noncomputable def outgoingHelixAtRootSlot (T : SecondaryStructure n)
    (i : Fin (pairedChildCount T none)) : MaximalHelix T :=
  Classical.choose (existsUnique_outgoing_of_root_child
    (orderedPairedChild T none i) (orderedPairedChild_mem T none i))

@[simp]
theorem outgoingHelixAtRootSlot_head (T : SecondaryStructure n)
    (i : Fin (pairedChildCount T none)) :
    (outgoingHelixAtRootSlot T i).headNode = orderedPairedChild T none i :=
  (Classical.choose_spec (existsUnique_outgoing_of_root_child
    (orderedPairedChild T none i) (orderedPairedChild_mem T none i))).1

/-- Any outgoing class-K helix other than the unique short helix is long. -/
theorem outgoingHelixAtLoopSlot_long_of_head_ne_short
    (hK : InTargetClassK T) (p : PairedNode T) (hp : IsLoopNode p)
    (i : Fin (pairedChildCount T (some p)))
    (hne : orderedPairedChild T (some p) i ≠ (shortHelix T hK).headNode) :
    3 ≤ (outgoingHelixAtLoopSlot T p hp i).length := by
  apply length_at_least_three_of_ne_shortHelix T hK
  intro heq
  apply hne
  rw [← outgoingHelixAtLoopSlot_head T p hp i, heq]

theorem outgoingHelixAtRootSlot_long_of_head_ne_short
    (hK : InTargetClassK T) (i : Fin (pairedChildCount T none))
    (hne : orderedPairedChild T none i ≠ (shortHelix T hK).headNode) :
    3 ≤ (outgoingHelixAtRootSlot T i).length := by
  apply length_at_least_three_of_ne_shortHelix T hK
  intro heq
  apply hne
  rw [← outgoingHelixAtRootSlot_head T i, heq]

theorem outgoingHelixAtLoopSlot_short_or_long
    (hK : InTargetClassK T) (p : PairedNode T) (hp : IsLoopNode p)
    (i : Fin (pairedChildCount T (some p))) :
    (outgoingHelixAtLoopSlot T p hp i).length = 2 ∨
      3 ≤ (outgoingHelixAtLoopSlot T p hp i).length := by
  by_cases heq : outgoingHelixAtLoopSlot T p hp i = shortHelix T hK
  · left
    rw [heq]
    exact shortHelix_length T hK
  · right
    exact length_at_least_three_of_ne_shortHelix T hK _ heq

theorem outgoingHelixAtRootSlot_short_or_long
    (hK : InTargetClassK T) (i : Fin (pairedChildCount T none)) :
    (outgoingHelixAtRootSlot T i).length = 2 ∨
      3 ≤ (outgoingHelixAtRootSlot T i).length := by
  by_cases heq : outgoingHelixAtRootSlot T i = shortHelix T hK
  · left
    rw [heq]
    exact shortHelix_length T hK
  · right
    exact length_at_least_three_of_ne_shortHelix T hK _ heq

/-- An actual outgoing loop child is short exactly when it is the head of the
globally unique short helix. -/
theorem outgoingHelixAtLoopSlot_length_two_iff
    (hK : InTargetClassK T) (p : PairedNode T) (hp : IsLoopNode p)
    (i : Fin (pairedChildCount T (some p))) :
    (outgoingHelixAtLoopSlot T p hp i).length = 2 ↔
      orderedPairedChild T (some p) i = (shortHelix T hK).headNode := by
  constructor
  · intro hlen
    have heq := eq_shortHelix_of_length_two T hK
      (outgoingHelixAtLoopSlot T p hp i) hlen
    rw [← outgoingHelixAtLoopSlot_head T p hp i, heq]
  · intro hhead
    have heq : outgoingHelixAtLoopSlot T p hp i = shortHelix T hK := by
      apply MaximalHelix.ext_outer
      change (outgoingHelixAtLoopSlot T p hp i).head = (shortHelix T hK).head
      have hnodes : (outgoingHelixAtLoopSlot T p hp i).headNode =
          (shortHelix T hK).headNode :=
        (outgoingHelixAtLoopSlot_head T p hp i).trans hhead
      exact congrArg Subtype.val hnodes
    rw [heq]
    exact shortHelix_length T hK

/-- Root analogue of the exact short-child characterization. -/
theorem outgoingHelixAtRootSlot_length_two_iff
    (hK : InTargetClassK T) (i : Fin (pairedChildCount T none)) :
    (outgoingHelixAtRootSlot T i).length = 2 ↔
      orderedPairedChild T none i = (shortHelix T hK).headNode := by
  constructor
  · intro hlen
    have heq := eq_shortHelix_of_length_two T hK
      (outgoingHelixAtRootSlot T i) hlen
    rw [← outgoingHelixAtRootSlot_head T i, heq]
  · intro hhead
    have heq : outgoingHelixAtRootSlot T i = shortHelix T hK := by
      apply MaximalHelix.ext_outer
      change (outgoingHelixAtRootSlot T i).head = (shortHelix T hK).head
      have hnodes : (outgoingHelixAtRootSlot T i).headNode =
          (shortHelix T hK).headNode :=
        (outgoingHelixAtRootSlot_head T i).trans hhead
      exact congrArg Subtype.val hnodes
    rw [heq]
    exact shortHelix_length T hK

/-! ## Complete root allocation on actual children -/

/-- Install a displayed root row on the actual ordered root children. -/
def rootActualPorts (T : SecondaryStructure n) (r : RootRow)
    (hcount : pairedChildCount T none = r.count) :
    ChildPortAssignment T none :=
  installPortRow T none r.ports hcount

@[simp]
theorem rootActualPorts_multiset (T : SecondaryStructure n) (r : RootRow)
    (hcount : pairedChildCount T none = r.count) :
    portMultiset (rootActualPorts T r hcount) = portMultiset r.ports := by
  exact installPortRow_multiset T none r.ports hcount

theorem rootActualPorts_proper (T : SecondaryStructure n) (r : RootRow)
    (hcount : pairedChildCount T none = r.count) :
    ProperExposure (rootPortExposure (rootActualPorts T r hcount)) := by
  rw [rootPortExposure, rootActualPorts_multiset]
  exact r.proper

theorem rootActualPorts_admissible (T : SecondaryStructure n) (r : RootRow)
    (hcount : pairedChildCount T none = r.count)
    (i : Fin (pairedChildCount T none)) :
    (rootActualPorts T r hcount i).AdmissibleAt r.entry r.eta := by
  exact r.admissible (finCongr hcount i)

theorem rootActualPorts_xi_nonGrey (T : SecondaryStructure n) (r : RootRow)
    (hr : r = .xiOne ∨ r = .xiTwo)
    (hcount : pairedChildCount T none = r.count)
    (i : Fin (pairedChildCount T none)) :
    (rootActualPorts T r hcount i).NonGrey := by
  exact r.xi_port_nonGrey hr (finCongr hcount i)

/-- Install a three/four-port eta row while moving grey to an arbitrary
actual root-child slot. -/
def etaRootActualPortsAt (T : SecondaryStructure n) (r : EtaRootRow)
    (hcount : pairedChildCount T none = r.count)
    (short : Fin (pairedChildCount T none)) : ChildPortAssignment T none :=
  installPortRow T none (r.portsAt (finCongr hcount short)) hcount

@[simp]
theorem etaRootActualPortsAt_short (T : SecondaryStructure n)
    (r : EtaRootRow) (hcount : pairedChildCount T none = r.count)
    (short : Fin (pairedChildCount T none)) :
    etaRootActualPortsAt T r hcount short short = Color.grey := by
  simp [etaRootActualPortsAt, installPortRow, PortAssignment.reindex]

theorem etaRootActualPortsAt_proper (T : SecondaryStructure n)
    (r : EtaRootRow) (hcount : pairedChildCount T none = r.count)
    (short : Fin (pairedChildCount T none)) :
    ProperExposure (rootPortExposure
      (etaRootActualPortsAt T r hcount short)) := by
  unfold etaRootActualPortsAt
  rw [rootPortExposure, installPortRow_multiset]
  exact r.portsAt_proper _

theorem etaRootActualPortsAt_admissible (T : SecondaryStructure n)
    (r : EtaRootRow) (hcount : pairedChildCount T none = r.count)
    (short i : Fin (pairedChildCount T none)) (eta : Parity) :
    (etaRootActualPortsAt T r hcount short i).AdmissibleAt eta eta :=
  Color.admissibleAt_self _ _

/-- A complete selected root row, installed on actual children.  The last two
fields state the short-root-child policy independently of whether the short
helix actually occurs at the root. -/
structure RootAllocation (T : SecondaryStructure n)
    (hK : InTargetClassK T) where
  row : RootRow
  count_eq : pairedChildCount T none = row.count
  ports : ChildPortAssignment T none
  sameDisplayedMultiset : portMultiset ports = portMultiset row.ports
  proper : ProperExposure (rootPortExposure ports)
  admissible : ∀ i, (ports i).AdmissibleAt row.entry row.eta
  shortGreyAtEta :
    ∀ hshort : (shortHelix T hK).headNode ∈ pairedChildren T none,
      row.entry = row.eta →
        ports (pairedChildIndex T none (shortHelix T hK).headNode hshort) =
          Color.grey
  shortNonGreyAtXi :
    ∀ hshort : (shortHelix T hK).headNode ∈ pairedChildren T none,
      row.entry = row.xi →
        (ports (pairedChildIndex T none
          (shortHelix T hK).headNode hshort)).NonGrey

/-- Every actual root port supplied by a root allocation satisfies the
stronger local `Safe` precondition of the transfer theorems. -/
theorem RootAllocation.safeOutgoing {hK : InTargetClassK T}
    (A : RootAllocation T hK)
    (i : Fin (pairedChildCount T none)) :
    Safe (outgoingHelixAtRootSlot T i).length A.row.entry A.row.eta
      (A.ports i) := by
  refine ⟨A.admissible i, ?_⟩
  rintro ⟨hlen, hentry⟩
  have hHelix : outgoingHelixAtRootSlot T i = shortHelix T hK :=
    eq_shortHelix_of_length_two T hK _ hlen
  have hchild : orderedPairedChild T none i = (shortHelix T hK).headNode := by
    rw [← outgoingHelixAtRootSlot_head T i, hHelix]
  have hshort : (shortHelix T hK).headNode ∈ pairedChildren T none := by
    rw [← hchild]
    exact orderedPairedChild_mem T none i
  have hi : i = pairedChildIndex T none (shortHelix T hK).headNode hshort := by
    apply orderedPairedChild_injective T none
    rw [orderedPairedChild_pairedChildIndex]
    exact hchild
  rw [hi]
  exact A.shortGreyAtEta hshort hentry

/-- The four actual-count possibilities for a class-K root. -/
theorem targetClass_root_count_cases (hK : InTargetClassK T) :
    pairedChildCount T none = 1 ∨
      pairedChildCount T none = 2 ∨
      pairedChildCount T none = 3 ∨
      pairedChildCount T none = 4 := by
  have hpos := targetClass_root_pairedChildCount_pos hK
  have hle := pairedDegree_le_four T (targetClass_motifFree hK) none
  simp only [pairedDegree] at hle
  omega

/-- The xi rows installed on actual root children. -/
noncomputable def xiRootAllocation (hK : InTargetClassK T)
    (r : RootRow) (hr : r = .xiOne ∨ r = .xiTwo)
    (hcount : pairedChildCount T none = r.count) : RootAllocation T hK where
  row := r
  count_eq := hcount
  ports := rootActualPorts T r hcount
  sameDisplayedMultiset := rootActualPorts_multiset T r hcount
  proper := rootActualPorts_proper T r hcount
  admissible := rootActualPorts_admissible T r hcount
  shortGreyAtEta := by
    intro _ heta
    rcases hr with rfl | rfl <;>
      simp [RootRow.entry, RootRow.eta, RootRow.xi, Parity.opposite] at heta
  shortNonGreyAtXi := by
    intro hshort _
    apply rootActualPorts_xi_nonGrey T r hr hcount

namespace EtaRootRow

/-- The corresponding displayed root-row tag. -/
def toRootRow : EtaRootRow → RootRow
  | .three => .etaThree
  | .four => .etaFour

@[simp]
theorem toRootRow_count (r : EtaRootRow) : r.toRootRow.count = r.count := by
  cases r <;> rfl

@[simp]
theorem toRootRow_base_multiset (r : EtaRootRow) :
    portMultiset r.toRootRow.ports = portMultiset r.basePorts := by
  cases r <;> decide

@[simp]
theorem toRootRow_entry_eq_eta (r : EtaRootRow) :
    r.toRootRow.entry = r.toRootRow.eta := by
  cases r <;> decide

@[simp]
theorem toRootRow_entry_ne_xi (r : EtaRootRow) :
    r.toRootRow.entry ≠ r.toRootRow.xi := by
  cases r <;> decide

end EtaRootRow

/-- The eta rows installed on actual root children.  When the unique short
helix is a root child, the assignment is permuted so that exact child receives
grey; otherwise the displayed base order is used. -/
noncomputable def etaRootAllocation (hK : InTargetClassK T)
    (r : EtaRootRow) (hcount : pairedChildCount T none = r.count) :
    RootAllocation T hK := by
  by_cases hshort :
      (shortHelix T hK).headNode ∈ pairedChildren T none
  · let shortIndex := pairedChildIndex T none (shortHelix T hK).headNode hshort
    let A := etaRootActualPortsAt T r hcount shortIndex
    refine {
      row := r.toRootRow
      count_eq := ?_
      ports := A
      sameDisplayedMultiset := ?_
      proper := ?_
      admissible := ?_
      shortGreyAtEta := ?_
      shortNonGreyAtXi := ?_ }
    · simpa using hcount
    · unfold A etaRootActualPortsAt
      rw [installPortRow_multiset, EtaRootRow.portsAt_multiset]
      exact r.toRootRow_base_multiset.symm
    · exact etaRootActualPortsAt_proper T r hcount shortIndex
    · intro i
      rw [r.toRootRow_entry_eq_eta]
      exact Color.admissibleAt_self _ _
    · intro hshort' _
      have hi : pairedChildIndex T none (shortHelix T hK).headNode hshort' =
          shortIndex := by
        rfl
      rw [hi]
      exact etaRootActualPortsAt_short T r hcount shortIndex
    · intro _ hxi
      exact False.elim (r.toRootRow_entry_ne_xi hxi)
  · let A := rootActualPorts T r.toRootRow (by simpa using hcount)
    refine {
      row := r.toRootRow
      count_eq := by simpa using hcount
      ports := A
      sameDisplayedMultiset := ?_
      proper := ?_
      admissible := ?_
      shortGreyAtEta := ?_
      shortNonGreyAtXi := ?_ }
    · exact rootActualPorts_multiset T r.toRootRow (by simpa using hcount)
    · exact rootActualPorts_proper T r.toRootRow (by simpa using hcount)
    · intro i
      exact rootActualPorts_admissible T r.toRootRow
        (by simpa using hcount) i
    · intro hshort' _
      exact False.elim (hshort hshort')
    · intro _ hxi
      exact False.elim (r.toRootRow_entry_ne_xi hxi)

@[simp]
theorem etaRootAllocation_row (hK : InTargetClassK T)
    (r : EtaRootRow) (hcount : pairedChildCount T none = r.count) :
    (etaRootAllocation hK r hcount).row = r.toRootRow := by
  unfold etaRootAllocation
  split <;> rfl

/-- Complete actual root allocation coverage of all three manuscript
conditions.  The witness contains the actual child-indexed assignment,
properness, admissibility, and the short-child grey/non-grey policy. -/
theorem completeRootAllocationCoverage (hK : InTargetClassK T) :
    ∃ A : RootAllocation T hK,
      (HasUnpairedChild T none →
        A.row = .xiOne ∨ A.row = .xiTwo) ∧
      (¬ HasUnpairedChild T none ∧ pairedChildCount T none ≤ 2 →
        A.row = .xiOne ∨ A.row = .xiTwo) ∧
      (¬ HasUnpairedChild T none ∧ 3 ≤ pairedChildCount T none →
        A.row = .etaThree ∨ A.row = .etaFour) := by
  rcases targetClass_root_count_cases hK with hone | htwo | hthree | hfour
  · let A := xiRootAllocation hK .xiOne (Or.inl rfl) hone
    refine ⟨A, ?_, ?_, ?_⟩
    · intro _
      exact Or.inl rfl
    · intro _
      exact Or.inl rfl
    · intro hlarge
      omega
  · let A := xiRootAllocation hK .xiTwo (Or.inr rfl) htwo
    refine ⟨A, ?_, ?_, ?_⟩
    · intro _
      exact Or.inr rfl
    · intro _
      exact Or.inr rfl
    · intro hlarge
      omega
  · have hno : ¬ HasUnpairedChild T none := by
      intro hu
      have hle := root_pairedChildren_le_two_of_unpaired
        T (targetClass_motifFree hK) hu
      omega
    let hcount : pairedChildCount T none = EtaRootRow.three.count := by
      change pairedChildCount T none = 3
      exact hthree
    let A := etaRootAllocation hK .three hcount
    refine ⟨A, ?_, ?_, ?_⟩
    · intro hu
      exact False.elim (hno hu)
    · intro hsmall
      omega
    · intro _
      exact Or.inl (by simp [A, EtaRootRow.toRootRow])
  · have hno : ¬ HasUnpairedChild T none := by
      intro hu
      have hle := root_pairedChildren_le_two_of_unpaired
        T (targetClass_motifFree hK) hu
      omega
    let hcount : pairedChildCount T none = EtaRootRow.four.count := by
      change pairedChildCount T none = 4
      exact hfour
    let A := etaRootAllocation hK .four hcount
    refine ⟨A, ?_, ?_, ?_⟩
    · intro hu
      exact False.elim (hno hu)
    · intro hsmall
      omega
    · intro _
      exact Or.inr (by simp [A, EtaRootRow.toRootRow])

/-- Prop-valued complete root theorem, including actual-child `Safe` and the
short-or-long class-K dichotomy for every outgoing helix. -/
theorem exists_completeRootAllocationCoverage (hK : InTargetClassK T) :
    ∃ A : RootAllocation T hK,
      (HasUnpairedChild T none →
        A.row = .xiOne ∨ A.row = .xiTwo) ∧
      (¬ HasUnpairedChild T none ∧ pairedChildCount T none ≤ 2 →
        A.row = .xiOne ∨ A.row = .xiTwo) ∧
      (¬ HasUnpairedChild T none ∧ 3 ≤ pairedChildCount T none →
        A.row = .etaThree ∨ A.row = .etaFour) ∧
      (∀ i, Safe (outgoingHelixAtRootSlot T i).length
        A.row.entry A.row.eta (A.ports i)) ∧
      (∀ i, (outgoingHelixAtRootSlot T i).length = 2 ∨
        3 ≤ (outgoingHelixAtRootSlot T i).length) := by
  obtain ⟨A, hu, hsmall, hlarge⟩ := completeRootAllocationCoverage hK
  exact ⟨A, hu, hsmall, hlarge, A.safeOutgoing,
    outgoingHelixAtRootSlot_short_or_long hK⟩

/-! ## Complete nonroot allocation coverage -/

/-- A complete allocation at one actual nonroot loop.  `entry` records the
interface residue chosen by the endpoint class; E deliberately carries no
forced-residue equation. -/
structure LoopAllocation (T : SecondaryStructure n) (hK : InTargetClassK T)
    (p : PairedNode T) (e : EndpointType) (a : Color) (xi : Parity) where
  entry : Parity
  ports : ChildPortAssignment T (some p)
  proper : ProperExposure (loopPortExposure a ports)
  admissible : ∀ i, (ports i).AdmissibleAt entry xi.opposite
  lEntry : e = .L → entry = xi
  mEntry : e = .M → entry = xi.opposite
  shortGreyAtM :
    e = .M →
      ∀ hshort : (shortHelix T hK).headNode ∈ pairedChildren T (some p),
        ports (pairedChildIndex T (some p)
          (shortHelix T hK).headNode hshort) = Color.grey
  shortNonGreyAtL :
    e = .L →
      ∀ hshort : (shortHelix T hK).headNode ∈ pairedChildren T (some p),
        (ports (pairedChildIndex T (some p)
          (shortHelix T hK).headNode hshort)).NonGrey

/-- Complete allocation coverage for E, L, and M on the actual ordered
outgoing helix heads.  For L the manuscript's non-grey closing precondition is
explicit.  For M the globally unique short child, when present, gets the
distinguished grey port; otherwise an ordinary row is installed. -/
noncomputable def completeLoopAllocationCoverage
    (hK : InTargetClassK T) (p : PairedNode T) (_hp : IsLoopNode p)
    (e : EndpointType) (he : HasEndpointType p e)
    (a : Color) (xi : Parity) (hclosing : e = .L → a.NonGrey) :
    LoopAllocation T hK p e a xi := by
  cases e with
  | E =>
      change IsEEndpoint p at he
      have hzero : pairedChildCount T (some p) = 0 := he.2
      let A := installPortRow T (some p) noPorts hzero
      refine {
        entry := xi
        ports := A
        proper := ?_
        admissible := ?_
        lEntry := ?_
        mEntry := ?_
        shortGreyAtM := ?_
        shortNonGreyAtL := ?_ }
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
      · intro h
        simp at h
  | L =>
      change IsLEndpoint p at he
      have ha : a.NonGrey := hclosing rfl
      by_cases hzero : pairedChildCount T (some p) = 0
      · let A := installPortRow T (some p) noPorts hzero
        refine {
          entry := xi
          ports := A
          proper := ?_
          admissible := ?_
          lEntry := ?_
          mEntry := ?_
          shortGreyAtM := ?_
          shortNonGreyAtL := ?_ }
        · unfold A
          rw [loopPortExposure, installPortRow_multiset]
          exact lZeroExposure_proper a ha
        · intro i
          exact Fin.elim0 (finCongr hzero i)
        · intro _
          rfl
        · intro h
          simp at h
        · intro h
          simp at h
        · intro _ hshort
          exact Fin.elim0 (finCongr hzero
            (pairedChildIndex T (some p) (shortHelix T hK).headNode hshort))
      · have hone : pairedChildCount T (some p) = 1 := by
          rcases he.2 with hz | ho
          · exact False.elim (hzero hz)
          · exact ho
        let A := installPortRow T (some p) (lOnePort a) hone
        refine {
          entry := xi
          ports := A
          proper := ?_
          admissible := ?_
          lEntry := ?_
          mEntry := ?_
          shortGreyAtM := ?_
          shortNonGreyAtL := ?_ }
        · unfold A
          rw [loopPortExposure, installPortRow_multiset]
          exact lOneExposure_proper a ha
        · intro i
          apply Or.inl
          have hi : finCongr hone i = (0 : Fin 1) := Subsingleton.elim _ _
          change (lOnePort a (finCongr hone i)).NonGrey
          rw [hi]
          exact lOnePort_nonGrey a ha
        · intro _
          rfl
        · intro h
          simp at h
        · intro h
          simp at h
        · intro _ hshort
          have hi : finCongr hone
              (pairedChildIndex T (some p) (shortHelix T hK).headNode hshort) =
              (0 : Fin 1) := Subsingleton.elim _ _
          change (lOnePort a (finCongr hone
            (pairedChildIndex T (some p)
              (shortHelix T hK).headNode hshort))).NonGrey
          rw [hi]
          exact lOnePort_nonGrey a ha
  | M =>
      change IsMEndpoint p at he
      have build (d : MArity)
          (hcount : pairedChildCount T (some p) = d.count) :
          LoopAllocation T hK p .M a xi := by
        by_cases hshort :
            (shortHelix T hK).headNode ∈ pairedChildren T (some p)
        · let A := designatedMActualPorts T p a d hcount
            (shortHelix T hK).headNode hshort
          refine {
            entry := xi.opposite
            ports := A
            proper := ?_
            admissible := ?_
            lEntry := ?_
            mEntry := ?_
            shortGreyAtM := ?_
            shortNonGreyAtL := ?_ }
          · exact designatedMActualExposure_proper T p a d hcount
              (shortHelix T hK).headNode hshort
          · intro i
            exact designatedMActualPort_admissible T p a d hcount
              (shortHelix T hK).headNode hshort i xi.opposite
          · intro h
            simp at h
          · intro _
            rfl
          · intro _ hshort'
            have hi : pairedChildIndex T (some p)
                (shortHelix T hK).headNode hshort' =
                pairedChildIndex T (some p)
                  (shortHelix T hK).headNode hshort := by
              rfl
            rw [hi]
            exact designatedMActualPorts_short T p a d hcount
              (shortHelix T hK).headNode hshort
          · intro h
            simp at h
        · let A := ordinaryMActualPorts T p a d hcount
          refine {
            entry := xi.opposite
            ports := A
            proper := ordinaryMActualExposure_proper T p a d hcount
            admissible := ?_
            lEntry := ?_
            mEntry := ?_
            shortGreyAtM := ?_
            shortNonGreyAtL := ?_ }
          · intro i
            exact ordinaryMActualPort_admissible T p a d hcount i xi.opposite
          · intro h
            simp at h
          · intro _
            rfl
          · intro _ hshort'
            exact False.elim (hshort hshort')
          · intro h
            simp at h
      by_cases htwo : pairedChildCount T (some p) = 2
      · exact build .two (by
          change pairedChildCount T (some p) = 2
          exact htwo)
      · have hthree : pairedChildCount T (some p) = 3 := by
          rcases he.2 with ht | hh
          · exact False.elim (htwo ht)
          · exact hh
        exact build .three (by
          change pairedChildCount T (some p) = 3
          exact hthree)

/-- Every actual outgoing loop port satisfies the stronger `Safe`
precondition.  At an L interface a short helix enters at `xi`; at an M
interface the designated-grey field supplies the short/eta clause; E has no
outgoing slot. -/
theorem LoopAllocation.safeOutgoing
    {hK : InTargetClassK T} {p : PairedNode T} {e : EndpointType}
    {a : Color} {xi : Parity}
    (A : LoopAllocation T hK p e a xi) (hp : IsLoopNode p)
    (he : HasEndpointType p e)
    (i : Fin (pairedChildCount T (some p))) :
    Safe (outgoingHelixAtLoopSlot T p hp i).length A.entry xi.opposite
      (A.ports i) := by
  cases e with
  | E =>
      change IsEEndpoint p at he
      exact Fin.elim0 (finCongr he.2 i)
  | L =>
      refine ⟨A.admissible i, ?_⟩
      rintro ⟨_hlen, hentry⟩
      have hxi : A.entry = xi := A.lEntry rfl
      exact False.elim (xi.ne_opposite (hxi.symm.trans hentry))
  | M =>
      refine ⟨A.admissible i, ?_⟩
      rintro ⟨hlen, _hentry⟩
      have hHelix : outgoingHelixAtLoopSlot T p hp i = shortHelix T hK :=
        eq_shortHelix_of_length_two T hK _ hlen
      have hchild : orderedPairedChild T (some p) i =
          (shortHelix T hK).headNode := by
        rw [← outgoingHelixAtLoopSlot_head T p hp i, hHelix]
      have hshort : (shortHelix T hK).headNode ∈
          pairedChildren T (some p) := by
        rw [← hchild]
        exact orderedPairedChild_mem T (some p) i
      have hi : i = pairedChildIndex T (some p)
          (shortHelix T hK).headNode hshort := by
        apply orderedPairedChild_injective T (some p)
        rw [orderedPairedChild_pairedChildIndex]
        exact hchild
      rw [hi]
      exact A.shortGreyAtM rfl hshort

/-- Prop-valued complete allocation theorem, suitable for dependency auditing and
later existence-style recursive proofs. -/
theorem exists_completeLoopAllocationCoverage
    (hK : InTargetClassK T) (p : PairedNode T) (hp : IsLoopNode p)
    (e : EndpointType) (he : HasEndpointType p e)
    (a : Color) (xi : Parity) (hclosing : e = .L → a.NonGrey) :
    Nonempty (LoopAllocation T hK p e a xi) :=
  ⟨completeLoopAllocationCoverage hK p hp e he a xi hclosing⟩

/-- The canonical complete witness supplies `Safe` to every actual outgoing
helix slot. -/
theorem completeLoopAllocationCoverage_safe
    (hK : InTargetClassK T) (p : PairedNode T) (hp : IsLoopNode p)
    (e : EndpointType) (he : HasEndpointType p e)
    (a : Color) (xi : Parity) (hclosing : e = .L → a.NonGrey)
    (i : Fin (pairedChildCount T (some p))) :
    Safe (outgoingHelixAtLoopSlot T p hp i).length
      (completeLoopAllocationCoverage hK p hp e he a xi hclosing).entry
      xi.opposite
      ((completeLoopAllocationCoverage hK p hp e he a xi hclosing).ports i) :=
  (completeLoopAllocationCoverage hK p hp e he a xi hclosing).safeOutgoing hp he i

/-- Complete endpoint-exhausting nonroot allocation theorem.  The caller
supplies only the mathematically necessary L-closing premise; the theorem
chooses the unique endpoint class and returns an actual assignment, `Safe` for
every outgoing helix, with every outgoing helix either the global short helix
or long. -/
theorem completeNonrootAllocationCoverage
    (hK : InTargetClassK T) (p : PairedNode T) (hp : IsLoopNode p)
    (a : Color) (xi : Parity)
    (hclosing : IsLEndpoint p → a.NonGrey) :
    ∃ e : EndpointType, ∃ A : LoopAllocation T hK p e a xi,
      HasEndpointType p e ∧
      (∀ i, Safe (outgoingHelixAtLoopSlot T p hp i).length
        A.entry xi.opposite (A.ports i)) ∧
      (∀ i, (outgoingHelixAtLoopSlot T p hp i).length = 2 ∨
        3 ≤ (outgoingHelixAtLoopSlot T p hp i).length) := by
  obtain ⟨e, he⟩ := loopNode_endpointType_exists
    (targetClass_motifFree hK) p hp
  have hclose : e = .L → a.NonGrey := by
    intro heL
    subst e
    exact hclosing he
  let A := completeLoopAllocationCoverage hK p hp e he a xi hclose
  refine ⟨e, A, he, ?_, ?_⟩
  · intro i
    exact A.safeOutgoing hp he i
  · exact outgoingHelixAtLoopSlot_short_or_long hK p hp

/-- In class K, two distinct outgoing children cannot both be short. -/
theorem atMostOne_short_outgoing_child (hK : InTargetClassK T)
    (p : PairedNode T) (hp : IsLoopNode p)
    (i j : Fin (pairedChildCount T (some p)))
    (hi : (outgoingHelixAtLoopSlot T p hp i).length = 2)
    (hj : (outgoingHelixAtLoopSlot T p hp j).length = 2) : i = j := by
  have hHi := eq_shortHelix_of_length_two T hK
    (outgoingHelixAtLoopSlot T p hp i) hi
  have hHj := eq_shortHelix_of_length_two T hK
    (outgoingHelixAtLoopSlot T p hp j) hj
  have hchildren : orderedPairedChild T (some p) i =
      orderedPairedChild T (some p) j := by
    rw [← outgoingHelixAtLoopSlot_head T p hp i,
      ← outgoingHelixAtLoopSlot_head T p hp j, hHi, hHj]
  exact orderedPairedChild_injective T (some p) hchildren

/-- Exact no-short/exactly-one-short dichotomy for the actual outgoing child
slots of any loop (and hence, in particular, of every M loop). -/
theorem outgoing_short_child_cases (hK : InTargetClassK T)
    (p : PairedNode T) (hp : IsLoopNode p) :
    (∀ i : Fin (pairedChildCount T (some p)),
      (outgoingHelixAtLoopSlot T p hp i).length ≠ 2) ∨
    ∃! i : Fin (pairedChildCount T (some p)),
      (outgoingHelixAtLoopSlot T p hp i).length = 2 := by
  by_cases hshort :
      (shortHelix T hK).headNode ∈ pairedChildren T (some p)
  · right
    let k := pairedChildIndex T (some p) (shortHelix T hK).headNode hshort
    refine ⟨k, ?_, ?_⟩
    · apply (outgoingHelixAtLoopSlot_length_two_iff hK p hp k).2
      exact orderedPairedChild_pairedChildIndex T (some p)
        (shortHelix T hK).headNode hshort
    · intro j hj
      apply orderedPairedChild_injective T (some p)
      have hjHead := (outgoingHelixAtLoopSlot_length_two_iff hK p hp j).1 hj
      rw [orderedPairedChild_pairedChildIndex]
      exact hjHead
  · left
    intro i hi
    apply hshort
    have hiHead := (outgoingHelixAtLoopSlot_length_two_iff hK p hp i).1 hi
    rw [← hiHead]
    exact orderedPairedChild_mem T (some p) i

/-- The virtual-root analogue: at most one root child is the global short
helix. -/
theorem atMostOne_short_root_outgoing_child (hK : InTargetClassK T)
    (i j : Fin (pairedChildCount T none))
    (hi : (outgoingHelixAtRootSlot T i).length = 2)
    (hj : (outgoingHelixAtRootSlot T j).length = 2) : i = j := by
  apply orderedPairedChild_injective T none
  rw [(outgoingHelixAtRootSlot_length_two_iff hK i).1 hi,
    (outgoingHelixAtRootSlot_length_two_iff hK j).1 hj]

end RNA
