#!/usr/bin/env python3
"""Token-aware prohibited-word audit for handwritten Lean source."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


FORBIDDEN = ("sorry", "admit", "axiom", "unsafe", "sorryAx", "native_decide")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def source_paths(root: Path) -> list[Path]:
    commands = (
        ("git", "ls-files", "*.lean"),
        ("git", "ls-files", "--others", "--exclude-standard", "*.lean"),
    )
    relative: set[str] = set()
    for command in commands:
        completed = subprocess.run(
            command,
            cwd=root,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        )
        relative.update(
            line
            for line in completed.stdout.splitlines()
            if line == "RNA.lean" or line.startswith("RNA/")
        )
    return [root / item for item in sorted(relative)]


def strip_comments_and_strings(text: str) -> str:
    """Replace comments and quoted strings by whitespace, preserving newlines."""
    output: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    string = False
    escaped = False
    while index < len(text):
        char = text[index]
        pair = text[index : index + 2]
        if char == "\n":
            output.append("\n")
            line_comment = False
            escaped = False
            index += 1
            continue
        if line_comment:
            output.append(" ")
            index += 1
            continue
        if block_depth:
            if pair == "/-":
                output.extend((" ", " "))
                block_depth += 1
                index += 2
            elif pair == "-/":
                output.extend((" ", " "))
                block_depth -= 1
                index += 2
            else:
                output.append(" ")
                index += 1
            continue
        if string:
            output.append(" ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                string = False
            index += 1
            continue
        if pair == "--":
            output.extend((" ", " "))
            line_comment = True
            index += 2
        elif pair == "/-":
            output.extend((" ", " "))
            block_depth = 1
            index += 2
        else:
            output.append(" ")
            if char == '"':
                string = True
            else:
                output[-1] = char
            index += 1
    if block_depth or string:
        raise ValueError("unterminated block comment or string")
    return "".join(output)


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    paths = source_paths(root)
    findings: list[tuple[str, int, str]] = []
    counts = {token: 0 for token in FORBIDDEN}

    for path in paths:
        clean = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        relative = path.relative_to(root).as_posix()
        for line_number, line in enumerate(clean.splitlines(), 1):
            for match in TOKEN_RE.finditer(line):
                token = match.group(0)
                if token in counts:
                    counts[token] += 1
                    findings.append((relative, line_number, token))

    print(f"handwritten_lean_files={len(paths)}")
    for token in FORBIDDEN:
        print(f"{token}={counts[token]}")
    print(f"actual_code_token_count={len(findings)}")
    if findings:
        for relative, line_number, token in findings:
            print(f"FINDING {relative}:{line_number}: {token}")
        return 1
    print("RESULT=PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
