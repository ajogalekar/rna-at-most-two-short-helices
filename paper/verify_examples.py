#!/usr/bin/env python3
"""Exact publication checks for the worked and negative-control examples.

Model: strict Watson-Crick pairs, minimum arc length zero, and arbitrary
noncrossing partial matchings. The Nussinov recurrence returns both the
optimum pair count and the exact number of optimum structures.
"""
from __future__ import annotations

from collections import Counter
from functools import lru_cache
from itertools import product
from typing import FrozenSet, Mapping

Pair = tuple[int, int]
COMPATIBLE = {("A", "U"), ("U", "A"), ("C", "G"), ("G", "C")}
PAIR_TO_COLOR = {
    ("G", "C"): "B",
    ("C", "G"): "W",
    ("A", "U"): "G",
    ("U", "A"): "G",
}
INVERSE_COLOR = {"B": "W", "W": "B", "G": "G"}
DELTA = {"B": 1, "W": -1, "G": 0}


def parse_dot_bracket(text: str) -> FrozenSet[Pair]:
    stack: list[int] = []
    pairs: set[Pair] = set()
    for index, char in enumerate(text):
        if char == "(":
            stack.append(index)
        elif char == ")":
            if not stack:
                raise ValueError("unmatched closing parenthesis")
            pairs.add((stack.pop(), index))
        elif char != ".":
            raise ValueError(f"unexpected character: {char!r}")
    if stack:
        raise ValueError("unmatched opening parenthesis")
    return frozenset(pairs)


def optimum_and_count(sequence: str) -> tuple[int, int, FrozenSet[Pair]]:
    """Return maximum pair count, number of optimal folds, and one optimum."""

    @lru_cache(maxsize=None)
    def solve(left: int, right: int) -> tuple[int, int, FrozenSet[Pair]]:
        if left > right:
            return 0, 1, frozenset()

        best_score, best_count, representative = solve(left, right - 1)

        for partner in range(left, right):
            if (sequence[partner], sequence[right]) not in COMPATIBLE:
                continue
            left_score, left_count, left_pairs = solve(left, partner - 1)
            inside_score, inside_count, inside_pairs = solve(partner + 1, right - 1)
            candidate_score = left_score + inside_score + 1
            candidate_count = left_count * inside_count
            candidate_pairs = left_pairs | inside_pairs | {(partner, right)}
            if candidate_score > best_score:
                best_score = candidate_score
                best_count = candidate_count
                representative = frozenset(candidate_pairs)
            elif candidate_score == best_score:
                best_count += candidate_count

        return best_score, best_count, representative

    return solve(0, len(sequence) - 1)


def pair_parents(pairs: FrozenSet[Pair]) -> dict[Pair, Pair | None]:
    parents: dict[Pair, Pair | None] = {}
    for pair in pairs:
        containers = [
            candidate
            for candidate in pairs
            if candidate[0] < pair[0] and pair[1] < candidate[1]
        ]
        parents[pair] = min(
            containers, key=lambda candidate: candidate[1] - candidate[0], default=None
        )
    return parents


def paired_children(
    pairs: FrozenSet[Pair], parents: Mapping[Pair, Pair | None], parent: Pair | None
) -> list[Pair]:
    return sorted(pair for pair in pairs if parents[pair] == parent)


def unpaired_parent(index: int, pairs: FrozenSet[Pair]) -> Pair | None:
    containers = [pair for pair in pairs if pair[0] < index < pair[1]]
    return min(containers, key=lambda pair: pair[1] - pair[0], default=None)


def levels_for_coloring(
    pairs: FrozenSet[Pair], colors: Mapping[Pair, str]
) -> tuple[dict[Pair, int], dict[Pair, Pair | None]]:
    parents = pair_parents(pairs)
    levels: dict[Pair, int] = {}
    for pair in sorted(pairs, key=lambda item: item[1] - item[0], reverse=True):
        parent = parents[pair]
        entry = 0 if parent is None else levels[parent]
        levels[pair] = entry + DELTA[colors[pair]]
    return levels, parents


def coloring_from_sequence(
    pairs: FrozenSet[Pair], sequence: str
) -> dict[Pair, str]:
    try:
        return {pair: PAIR_TO_COLOR[(sequence[pair[0]], sequence[pair[1]])] for pair in pairs}
    except KeyError as error:
        raise AssertionError(f"non-Watson-Crick target pair: {error.args[0]}") from error


def coloring_is_proper(
    pairs: FrozenSet[Pair], colors: Mapping[Pair, str]
) -> bool:
    parents = pair_parents(pairs)
    for parent in [None, *pairs]:
        exposure = [] if parent is None else [INVERSE_COLOR[colors[parent]]]
        exposure.extend(colors[child] for child in paired_children(pairs, parents, parent))
        counts = Counter(exposure)
        if counts["B"] > 1 or counts["W"] > 1 or counts["G"] > 2:
            return False
    return True


def unpaired_levels(
    target_text: str,
    pairs: FrozenSet[Pair],
    pair_levels: Mapping[Pair, int],
) -> list[int]:
    paired_positions = {endpoint for pair in pairs for endpoint in pair}
    result = []
    for index in range(len(target_text)):
        if index in paired_positions:
            continue
        parent = unpaired_parent(index, pairs)
        result.append(0 if parent is None else pair_levels[parent])
    return result


def maximal_helices(pairs: FrozenSet[Pair]) -> list[list[Pair]]:
    helices: list[list[Pair]] = []
    for outer in sorted(pairs):
        if (outer[0] - 1, outer[1] + 1) in pairs:
            continue
        helix: list[Pair] = []
        pair = outer
        while pair in pairs:
            helix.append(pair)
            pair = (pair[0] + 1, pair[1] - 1)
        helices.append(helix)
    return helices


def check_unique_design(name: str, target_text: str, sequence: str) -> None:
    target = parse_dot_bracket(target_text)
    if len(target_text) != len(sequence):
        raise AssertionError(f"{name}: target and sequence lengths differ")
    if not all((sequence[i], sequence[j]) in COMPATIBLE for i, j in target):
        raise AssertionError(f"{name}: target is incompatible with sequence")
    score, count, representative = optimum_and_count(sequence)
    if score != len(target) or count != 1 or representative != target:
        raise AssertionError(
            f"{name}: failed (target pairs={len(target)}, score={score}, "
            f"count={count}, target_is_representative={representative == target})"
        )
    print(
        f"PASS {name}: n={len(sequence)}, target_pairs={len(target)}, "
        f"compatible=yes, optimum={score}, optimum_count={count}"
    )


def check_corrected_t2_coloring() -> None:
    target_text = "(((((((())(()))))((())))))"
    sequence = "GGGAGGAGCUUGCACCUGGGCCCCCC"
    pairs = parse_dot_bracket(target_text)
    colors = coloring_from_sequence(pairs, sequence)
    levels, _parents = levels_for_coloring(pairs, colors)
    helices = maximal_helices(pairs)
    words = ["".join(colors[pair] for pair in helix) for helix in helices]
    helix_levels = [[levels[pair] for pair in helix] for helix in helices]

    expected_words = ["BBB", "GBB", "GB", "GB", "BBB"]
    expected_levels = [[1, 2, 3], [3, 4, 5], [5, 6], [5, 6], [4, 5, 6]]
    if words != expected_words or helix_levels != expected_levels:
        raise AssertionError(
            f"T2 coloring mismatch: words={words}, levels={helix_levels}"
        )
    if not coloring_is_proper(pairs, colors):
        raise AssertionError("T2 coloring is not proper")
    gray_levels = [levels[pair] for pair in pairs if colors[pair] == "G"]
    if not gray_levels or {level % 2 for level in gray_levels} != {1}:
        raise AssertionError(f"T2 gray residues are not eta=1: {gray_levels}")
    print(
        "PASS corrected T2 coloring: xi=0, eta=1; "
        f"helix_words={','.join(words)}; levels={helix_levels}; proper=yes"
    )


def check_three_short_boundary() -> None:
    target_text = "((.))((.))((.))"
    sequence = "GGACCCCAGGAGACU"
    pairs = parse_dot_bracket(target_text)
    designed_colors = coloring_from_sequence(pairs, sequence)
    levels, _parents = levels_for_coloring(pairs, designed_colors)
    gray_levels = {levels[pair] for pair in pairs if designed_colors[pair] == "G"}
    free_levels = set(unpaired_levels(target_text, pairs, levels))
    designed_words = [
        "".join(designed_colors[pair] for pair in helix)
        for helix in maximal_helices(pairs)
    ]
    if designed_words != ["BB", "WW", "GB"]:
        raise AssertionError(f"unexpected ordinary separated coloring: {designed_words}")
    if not coloring_is_proper(pairs, designed_colors) or gray_levels & free_levels:
        raise AssertionError(
            f"claimed ordinary separation failed: gray={gray_levels}, free={free_levels}"
        )

    proper_count = 0
    ordinarily_separated_count = 0
    modulo_two_separated_count = 0
    ordered_pairs = sorted(pairs)
    for word in product("BWG", repeat=len(ordered_pairs)):
        colors = dict(zip(ordered_pairs, word, strict=True))
        if not coloring_is_proper(pairs, colors):
            continue
        proper_count += 1
        pair_levels, _ = levels_for_coloring(pairs, colors)
        gray_residues = {
            pair_levels[pair] % 2 for pair in pairs if colors[pair] == "G"
        }
        gray_integer_levels = {
            pair_levels[pair] for pair in pairs if colors[pair] == "G"
        }
        free_integer_levels = set(
            unpaired_levels(target_text, pairs, pair_levels)
        )
        if not (gray_integer_levels & free_integer_levels):
            ordinarily_separated_count += 1
        free_residues = {
            level % 2 for level in free_integer_levels
        }
        if not (gray_residues & free_residues):
            modulo_two_separated_count += 1

    if modulo_two_separated_count != 0:
        raise AssertionError(
            "three-short target unexpectedly has a proper modulo-2 separated coloring"
        )
    print(
        "PASS three-short coloring boundary: "
        f"searched=3^{len(pairs)}={3 ** len(pairs)}, proper={proper_count}, "
        f"proper_ordinary_separated={ordinarily_separated_count}, "
        "proper_modulo2_separated=0; ordinary_words=BB,WW,GB; "
        f"gray_levels={sorted(gray_levels)}, unpaired_levels={sorted(free_levels)}"
    )
    check_unique_design("three-short ordinary design", target_text, sequence)


def check_nested_tie() -> None:
    target_text = "(())"
    sequence = "AUAU"
    target = parse_dot_bracket(target_text)
    score, count, _representative = optimum_and_count(sequence)
    disjoint = parse_dot_bracket("()()")
    if score != 2 or count != 2:
        raise AssertionError(f"AUAU tie count mismatch: score={score}, count={count}")
    if not all((sequence[i], sequence[j]) in COMPATIBLE for i, j in target | disjoint):
        raise AssertionError("AUAU is not compatible with both tied structures")
    print(
        "PASS nested AUAU negative control: target_pairs=2, optimum=2, "
        "optimum_count=2; competitor=()()"
    )


def main() -> None:
    check_unique_design("root two-demand T1", "(())(())((()))", "AGCUUGCAGGGCCC")
    check_corrected_t2_coloring()
    check_unique_design(
        "internal two-demand T2",
        "(((((((())(()))))((())))))",
        "GGGAGGAGCUUGCACCUGGGCCCCCC",
    )
    check_three_short_boundary()
    check_nested_tie()


if __name__ == "__main__":
    main()
