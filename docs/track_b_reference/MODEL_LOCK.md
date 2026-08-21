# Track B model lock

**Locked on:** 2026-08-19 (America/Los_Angeles)

This document fixes the mathematical universe for every proof, program, and
claim in Track B. No biological energy term or geometric restriction not
listed here is implicit.

## Sequence and compatibility

For a fixed integer `n >= 0`, a sequence is a complete word

```text
w in {A,C,G,U}^n.
```

The compatible **ordered** pairs are exactly `(A,U)`, `(U,A)`, `(C,G)`, and
`(G,C)`. There are no G-U wobble pairs.

## Structures and energy

A secondary structure on backbone positions `[n] = {1,...,n}` is an arbitrary
noncrossing partial matching: every position is incident to at most one pair,
and there are no pairs `(i,j)` and `(k,l)` with `i < k < j < l`. Adjacent
positions may pair. There is no minimum arc length, minimum hairpin length,
stacking term, nearest-neighbor energy, experimental parameter, pseudoknot, or
three-dimensional constraint.

A structure `S` is compatible with `w` when the letters at both endpoints of
every pair of `S` form one of the four ordered compatible pairs above. Its
energy is

```text
E(w,S) = -|S|.
```

Thus minimum energy is exactly maximum pair count.

## Unique designability and quantifier order

A target structure `T` on `[n]` is uniquely designable precisely when

```text
exists w in {A,C,G,U}^n,
  [T is compatible with w]
  and
  [for every noncrossing partial matching S on [n],
     if S is compatible with w and S != T, then |S| < |T|].
```

The sequence is chosen after the target and before the universal quantifier
over competitors. Equivalently, `T` is the unique maximum-cardinality
compatible noncrossing matching of one complete sequence. The definition does
not quantify over a different sequence for each competitor.

## Exact Haleš interval tree

For a target `T`, form an interval tree containing:

- the virtual root interval `[0,n+1]`;
- one paired node `[i,j]` for each target pair `(i,j)`;
- one singleton unpaired node `[k,k]` for each target-unpaired position `k`.

The children of an interval are its maximal proper subintervals, ordered by
backbone position. Equivalently, the parent of a nonroot node is its unique
smallest strictly enclosing target pair, or the virtual root if none exists.

Only paired neighbors count toward paired degree. For a nonroot paired node
`v`,

```text
paired_degree(v) = 1 + number_of_paired_children(v),
```

where the extra one is its paired-parent edge. At the virtual root,

```text
paired_degree(root) = number_of_paired_children(root).
```

Unpaired children never contribute to paired degree.

The forbidden motifs are exactly:

- `m5`: some paired node or the virtual root has paired degree greater than 4;
- `m3•`: some paired node or the virtual root has at least one unpaired child
  and paired degree greater than 2.

## Maximal helices

A helix of length `h >= 1` is a maximal run of target pairs

```text
(i,j), (i+1,j-1), ..., (i+h-1,j-h+1).
```

Maximality is with respect to extension at either end by another adjacent
nested target pair.

## Target classes

`K2` is the class of targets satisfying all five conditions:

1. exactly two maximal helices have length 2;
2. no maximal helix has length 1;
3. every other maximal helix has length at least 3;
4. `m5` is absent;
5. `m3•` is absent.

`K<=2` is the class satisfying conditions 2, 3, 4, and 5 after replacing
condition 1 by: at most two maximal helices have length 2. Equivalently, every
maximal helix has length at least 2, at most two have length exactly 2, and all
others have length at least 3, with both forbidden motifs absent.

## Coloring predicates

Every nonroot paired node receives a color in `{B,W,G}`. Set

```text
inv(B)=W,  inv(W)=B,  inv(G)=G,
delta(B)=+1, delta(W)=-1, delta(G)=0.
```

For a nonroot paired node `v`, its exposed multiset is

```text
X(v) = {inv(color(v))} multiset-union
       {color(u) : u is a paired child of v}.
```

At the root it is just the multiset of paired-child colors. A coloring is
**proper** iff every exposed multiset contains at most one `B`, at most one
`W`, and at most two `G` entries.

The inclusive integer level of a paired node is the sum of `delta(color)` over
the paired nodes on the root-to-node path, including the node. The root level
is zero. An unpaired node has its paired parent's inclusive level, or zero when
its parent is the root.

A proper coloring is **ordinary separated** iff no integer level occupied by
a gray paired node is occupied by an unpaired node.

A proper coloring is **strong 2-separated** iff there exists
`xi in Z/2Z`, with `eta = 1-xi`, such that every unpaired-node level has residue
`xi` and every gray-paired-node level has residue `eta`. This remains
nonvacuous on the unpaired side even if no gray pair exists.

## Four distinct questions

Every report must keep these implications one-way and the verdicts separate:

- **A:** Does a specified extended deterministic construction work on every
  `K2` target?
- **B:** Does every `K2` target admit *some* proper strong 2-separated coloring?
- **C:** Does every `K2` target admit *some* proper ordinary separated coloring?
- **D:** Is every `K2` target uniquely designable in the locked sequence model?

An A failure does not decide B, C, or D. A B failure does not decide C or D. A
C failure does not decide D. Only an exact sequence-level impossibility result
can establish a D counterexample.

