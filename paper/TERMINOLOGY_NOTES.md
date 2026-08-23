# Terminology and style notes

This revision changes exposition, not the mathematical theorem or the Lean formalization.

## Terms aligned with the RNA-design literature

The manuscript now uses the established terms associated with the work of Haleš et al. and Boury et al. whenever they apply:

- RNA inverse folding and designability
- tree representation
- proper coloring and separated coloring
- level
- modulo-2 separation
- isolated base pair for a helix of length 1
- isolated stack for a helix of length 2
- multiloop
- paired restriction
- saturable sequence and atomic saturable design

American spellings `color`, `coloring`, and `gray` are used consistently.

## Project-specific notation kept to a minimum

- `E`, `L`, and `M` are only abbreviations for three explicitly defined terminal-loop types.
- `F` and `Q` are names for two explicitly listed sets of feasible entry states.
- `uniform residue form` describes the particular modulo-2 condition constructed in the proof and corresponds to `StrongTwoSeparated` in Lean.

No biological interpretation is assigned to these symbols.

## Phrases removed or replaced

The revision replaces informal or project-internal phrases such as:

- resource invariant -> induction on helix subtrees / inductive guarantee
- resource-aware allocation -> color assignment at a loop or the root
- positive-short subtree -> subtree containing an isolated stack
- short-free subtree -> subtree containing no isolated stack
- port -> first-pair color
- two-demand case -> case with two child subtrees containing isolated stacks
- pairing inventory -> nucleotide-count bound
- saturated skeleton -> paired restriction
- no-tie theorem -> uniqueness among optimal folds
- proof oracle / proof qualification -> external proof program / independent verification
- Track A / Track B / milestone terminology -> removed from the manuscript

## Structural choices

The main theorem is stated in the standard language of modulo-2 separation. The text then records the stronger uniform residue property actually produced by the construction and formalized in Lean. Formal-verification terminology is confined mainly to the dedicated verification section and appendices.
