# Final example verification

## Method

The checks use `verify_examples.py`, a standard-library-only implementation of the strict four-letter Watson-Crick model with minimum arc length zero. Its Nussinov dynamic program ranges over arbitrary noncrossing partial matchings, returns the maximum pair count, and counts all optimum structures. The same script reconstructs pair colors and inclusive levels from each target/sequence pair, checks every exposed multiset for properness, and exhaustively enumerates the `3^6 = 729` colorings of the three-stack boundary target.

Command:

```sh
python3 verify_examples.py
```

## Exact output

```text
PASS root two-demand T1: n=14, target_pairs=7, compatible=yes, optimum=7, optimum_count=1
PASS T2 coloring certificate: xi=0, eta=1; helix_words=BBB,GBB,GB,GB,BBB; levels=[[1, 2, 3], [3, 4, 5], [5, 6], [5, 6], [4, 5, 6]]; proper=yes
PASS internal two-demand T2: n=26, target_pairs=13, compatible=yes, optimum=13, optimum_count=1
PASS three-short coloring boundary: searched=3^6=729, proper=180, proper_ordinary_separated=36, proper_modulo2_separated=0; ordinary_words=BB,WW,GB; gray_levels=[0], unpaired_levels=[-2, 1, 2]
PASS three-short ordinary design: n=15, target_pairs=6, compatible=yes, optimum=6, optimum_count=1
PASS nested AUAU negative control: target_pairs=2, optimum=2, optimum_count=2; competitor=()()
```

## Deterministic T2 construction

The retained target is

```text
(((((((())(()))))((())))))
```

Under the deterministic small-root convention `xi = 0`, `eta = 1`, the construction specified by the manuscript has:

| Helix | Target pairs (1-based) | Color word | Inclusive levels |
|---|---|---|---|
| outer | `(1,26),(2,25),(3,24)` | `BBB` | `1,2,3` |
| critical | `(4,17),(5,16),(6,15)` | `GBB` | `3,4,5` |
| first isolated stack | `(7,10),(8,9)` | `GB` | `5,6` |
| second isolated stack | `(11,14),(12,13)` | `GB` | `5,6` |
| side | `(18,23),(19,22),(20,21)` | `BBB` | `4,5,6` |

The corresponding deterministic sequence is:

```text
GGGAGGAGCUUGCACCUGGGCCCCCC
```

All gray pairs have odd level, the two load-bearing short children enter gray, the critical helix closes black, and the internal exposure is `{W,G,G}`. The target is compatible with the sequence and is the unique optimum with 13 pairs.

The review prompt reported `GGGGGAGGCCCCGGUCCAGGCCUCCC`. That sequence is also compatible and uniquely designing, but its decoded helix words are `BBB, BBG, BB, WW, GBB`. It comes from an unconstrained search witness, not the manuscript's stated F/Q recursion: the positive-short critical child starts non-gray at an `eta` entry and its two isolated-stack children do not receive gray. The reconstructed sequence above is therefore used so that Example 13.2 and Figure 5 continue to instantiate the strengthened two-demand transfer.

## Three-stack boundary

For `((.))((.))((.))`, exhaustive enumeration finds 180 proper colorings, 36 ordinarily separated proper colorings, and no proper modulo-2 separated coloring. The sequence

```text
GGACCCCAGGAGACU
```

encodes the ordinary separated helix words `BB, WW, GB`. Its gray level set is `{0}` and its unpaired level set is `{-2,1,2}`, which are disjoint over the integers but collide modulo two. Exact folding gives six target pairs, optimum six, and optimum count one.

## Negative control

`AUAU` is compatible with both the nested target `(())` and the disjoint fold `()()`. The optimum score is two and the exact optimum count is two, so `AUAU` does not uniquely design `(())`.
