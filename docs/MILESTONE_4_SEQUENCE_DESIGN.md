# Milestone 4 sequence-construction design

## Existing representation

The public target remains `SecondaryStructure n`.  A target pair is a
`PairedNode T`, its computed parent is `parent T (Sum.inl v)`, and its exact
paired siblings are `pairedChildren T p`.  Their deterministic backbone order
is already exposed by `orderedPairedChildren T p` and
`orderedPairedChild T p i`.  The construction will not replace these objects
with a second tree representation.

Before assigning letters, `RNA/PositionRole.lean` will exhibit a finite
equivalence between backbone positions and

```text
UnpairedPosition T ⊕ (PairedNode T × EndpointSide).
```

The forward map sends an unpaired node to its position and a paired node/side
to the corresponding endpoint.  Partial matching proves injectivity; the
definition of `positionPaired` proves surjectivity.  Its inverse gives the
unique role of every position.  Consequently endpoint lookup returns an
`Option PairedNode` and never invents a default arc.

## Architecture A: recursive assignment from the parent

For each interface `p`, filter its actual paired children to grey children and
sort them in backbone order.  For a grey child `v`, define its grey-sibling
rank as the number of grey children with smaller left endpoint.

Define a paired node's left letter by well-founded recursion:

- black is `G`;
- white is `C`;
- a grey root child, or a grey child of a non-grey parent, is `A` at grey rank
  zero and `U` at grey rank one;
- a grey child of a grey parent recursively copies that parent's left letter.

The recursive call is from a child to a strictly enclosing parent.  The
parent's left endpoint is strictly smaller, so `v.val.left.val` is a direct
well-founded termination measure.  No separately chosen depth or tree is
needed.

Properness is used through `ProperColoring` and the actual
`exposedMultiset`.  Multiset-count lemmas will prove:

- at the root and below a non-grey parent, the grey-child count is at most two;
- below a grey parent, the inverse-colour closing incidence consumes one grey
  slot, so the grey-child count is at most one;
- every relevant grey-sibling rank is less than two.

Thus the rank test implements exactly “first grey sibling gets `A`, second gets
`U`”.  Distinct anchor siblings have ranks zero and one, while a grey child of
a grey parent obtains the parent's already established orientation.

This architecture depends on ordered children only at component anchors.  Its
copy theorem is a definitional recursion equation, and sibling distinctness is
a small rank argument.  Prefix-balance proofs later need only the colour-to-
weight equations, not the recursion itself.

## Architecture B: nearest grey-component anchor

An alternative is to follow grey-parent links from `v` to the outermost grey
node in its connected grey chain.  That anchor lies at the root or below a
non-grey parent, receives `A` or `U` from its sibling rank, and every node in
the component reads the same orientation.

This avoids a recursive nucleotide-valued function, but it requires a second
proved search object: the nearest/outermost grey anchor.  One must prove anchor
existence, uniqueness, membership on the actual parent path, termination of the
search, and invariance of the selected anchor under one grey-parent step.
Ordered children are still needed to orient the anchor.  Sibling distinctness
is no easier, the copy theorem becomes an anchor-equality theorem, and the
extra ancestor machinery does not simplify prefix balance because grey letters
have weight zero there.

## Choice

Architecture A is selected.  It follows the manuscript literally, terminates
on the existing endpoint order, exposes the copy equation directly, and has a
smaller review surface.  Architecture B would be useful only if later results
needed grey components as first-class objects; Milestones 4 and 5 do not.

The computational constructor is `leftLetterOfColoring chi`; the properness
proof is used only by its correctness theorems and the proof-bearing public
wrapper.  Thus the assigned letters are deterministic once `T` and `chi` are
fixed and are independent of proof objects.  The construction performs no
search over A/U orientations.

## Complete sequence and certificate

`RNA/SequenceAssignment.lean` will define the left-letter function and

```text
sequenceOfProperColoring
  (chi : Coloring T) (hProper : ProperColoring chi) : Sequence n
```

by matching on the unique position role:

- target-unpaired: `A`;
- paired left endpoint: the recursive left letter;
- paired right endpoint: its Watson--Crick complement.

Pointwise theorems will specialize this definition to every role and colour.
`RNA/SequenceCertificate.lean` will prove target compatibility and local
distinctness and package the retained construction facts.  The class-K global
certificate will store the existing `GlobalColoringCertificate`, this one
sequence, and all downstream evidence about that same witness.
