#!/usr/bin/env python3
"""Parse every dot-bracket literal printed in the manuscript source."""

from __future__ import annotations

import re
from pathlib import Path

from verify_examples import parse_dot_bracket


TEX_PATH = Path(__file__).with_name(
    "Designability_of_RNA_Targets_with_Up_to_Two_Length_2_Helices.tex"
)
TOKEN = re.compile(r"(?<![A-Za-z0-9])([().]{2,})(?![A-Za-z0-9])")


def main() -> None:
    occurrences: list[tuple[int, str]] = []
    for line_number, line in enumerate(TEX_PATH.read_text(encoding="utf-8").splitlines(), 1):
        for match in TOKEN.finditer(line):
            literal = match.group(1)
            if "(" not in literal or ")" not in literal:
                continue
            pairs = parse_dot_bracket(literal)
            occurrences.append((line_number, literal))
            print(
                f"PASS line {line_number}: {literal} "
                f"(n={len(literal)}, pairs={len(pairs)})"
            )

    if not occurrences:
        raise AssertionError("no manuscript dot-bracket literals found")

    unique = sorted({literal for _line, literal in occurrences}, key=lambda item: (len(item), item))
    print(
        f"PASS manuscript literal coverage: occurrences={len(occurrences)}, "
        f"unique={len(unique)}; literals={','.join(unique)}"
    )


if __name__ == "__main__":
    main()
