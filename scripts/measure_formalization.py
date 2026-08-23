#!/usr/bin/env python3
"""Measure the handwritten Lean source in the publication release.

The default scopes are:
  * the authoritative 46-file final theorem dependency closure; and
  * the full 62-file handwritten project (tracked Lean plus the two downstream
    publication modules).

Only Python's standard library is used.  Build products, generated files, and
Mathlib sources are excluded from the project scope.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from typing import Iterable, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CLOSURE_LIST = Path(
    os.environ.get(
        "RNA_FINAL_CLOSURE_LIST",
        str(REPO_ROOT / "docs" / "final_dependency_closure.txt"),
    )
)
PUBLICATION_MODULES = (
    "RNA/AtMostTwoShort/PublicationExamples.lean",
    "RNA/AtMostTwoShort/PublicationExamplesAxiomAudit.lean",
)
EXCLUDED_PARTS = frozenset(
    {
        ".lake",
        "build",
        "generated",
        "lake-packages",
        "Mathlib",
    }
)
COMMAND_KEYWORDS = (
    "def",
    "abbrev",
    "structure",
    "inductive",
    "theorem",
    "lemma",
    "example",
    "class",
    "instance",
    "opaque",
    "axiom",
)
DECLARATION_MODIFIERS = frozenset(
    {
        "private",
        "protected",
        "noncomputable",
        "partial",
        "public",
        "local",
        "scoped",
        "nonrec",
        "unsafe",
    }
)
TOKEN_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_']*)\b")


@dataclass
class Metrics:
    files: int = 0
    physical_lines: int = 0
    raw_nonblank_lines: int = 0
    nonblank_noncomment_lines: int = 0
    definitions: int = 0
    structures_inductives: int = 0
    lemmas_theorems: int = 0
    examples: int = 0
    other_declaration_commands: int = 0
    all_counted_declaration_commands: int = 0
    def_commands: int = 0
    abbrev_commands: int = 0
    structure_commands: int = 0
    inductive_commands: int = 0
    lemma_commands: int = 0
    theorem_commands: int = 0
    example_commands: int = 0
    class_commands: int = 0
    instance_commands: int = 0
    opaque_commands: int = 0
    axiom_commands: int = 0


def run_git(*args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return result.stdout.strip()


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_relative_path(raw: str) -> str:
    path = raw.strip()
    while path.startswith("./"):
        path = path[2:]
    candidate = Path(path)
    if candidate.is_absolute() or ".." in candidate.parts:
        raise ValueError(f"scope path is not repository-relative: {raw!r}")
    return candidate.as_posix()


def is_handwritten_lean(rel: str) -> bool:
    path = Path(rel)
    is_project_path = rel == "RNA.lean" or rel.startswith("RNA/")
    return (
        is_project_path
        and path.suffix == ".lean"
        and not any(part in EXCLUDED_PARTS for part in path.parts)
    )


def tracked_lean_paths() -> list[str]:
    output = run_git("ls-files", "*.lean")
    paths = [normalize_relative_path(line) for line in output.splitlines() if line]
    return sorted(path for path in paths if is_handwritten_lean(path))


def read_closure_paths(path: Path) -> list[str]:
    if not path.is_file():
        raise FileNotFoundError(
            f"closure list not found: {path}\n"
            "Pass --closure-list PATH or set RNA_FINAL_CLOSURE_LIST."
        )
    paths = [
        normalize_relative_path(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if len(paths) != len(set(paths)):
        duplicates = sorted(path for path in set(paths) if paths.count(path) > 1)
        raise ValueError(f"duplicate closure paths: {duplicates}")
    if any(not is_handwritten_lean(rel) for rel in paths):
        invalid = [rel for rel in paths if not is_handwritten_lean(rel)]
        raise ValueError(f"non-handwritten or non-Lean closure paths: {invalid}")
    return paths


def validate_paths(paths: Iterable[str], scope_name: str) -> list[str]:
    normalized = sorted(set(paths))
    missing = [rel for rel in normalized if not (REPO_ROOT / rel).is_file()]
    if missing:
        raise FileNotFoundError(f"{scope_name} has missing files: {missing}")
    return normalized


def strip_lean_comments(text: str) -> list[str]:
    """Return physical lines after removing Lean comments.

    Nested /- ... -/ comments and -- comments are recognized.  Quoted strings
    and their escapes are retained, so comment markers inside strings do not
    start comments.
    """

    output: list[str] = []
    current: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(text):
        char = text[index]
        pair = text[index : index + 2]

        if char == "\n":
            output.append("".join(current))
            current = []
            in_line_comment = False
            escaped = False
            index += 1
            continue

        if in_line_comment:
            index += 1
            continue

        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                index += 1
            continue

        if in_string:
            current.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue

        if pair == "--":
            in_line_comment = True
            index += 2
        elif pair == "/-":
            block_depth = 1
            index += 2
        else:
            current.append(char)
            if char == '"':
                in_string = True
            index += 1

    if block_depth:
        raise ValueError("unterminated block comment")
    if current or (text and not text.endswith("\n")):
        output.append("".join(current))
    return output


def after_same_line_attributes(line: str) -> str:
    text = line.lstrip()
    while text.startswith("@["):
        depth = 0
        in_string = False
        escaped = False
        end = None
        for index, char in enumerate(text[1:], start=1):
            if in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
            elif char == '"':
                in_string = True
            elif char == "[":
                depth += 1
            elif char == "]":
                depth -= 1
                if depth == 0:
                    end = index + 1
                    break
        if end is None:
            return text
        text = text[end:].lstrip()
    return text


def declaration_command(line: str) -> str | None:
    text = after_same_line_attributes(line)
    while True:
        match = TOKEN_RE.match(text)
        if not match or match.group(1) not in DECLARATION_MODIFIERS:
            break
        text = text[match.end() :].lstrip()
    match = TOKEN_RE.match(text)
    if match and match.group(1) in COMMAND_KEYWORDS:
        return match.group(1)
    return None


def measure(paths: Sequence[str]) -> Metrics:
    raw_counts: Counter[str] = Counter()
    command_counts: Counter[str] = Counter()

    for rel in paths:
        text = (REPO_ROOT / rel).read_text(encoding="utf-8")
        raw_lines = text.splitlines()
        code_lines = strip_lean_comments(text)
        if len(code_lines) != len(raw_lines):
            raise AssertionError(f"physical-line mismatch after comment scan: {rel}")

        raw_counts["physical"] += len(raw_lines)
        raw_counts["raw_nonblank"] += sum(bool(line.strip()) for line in raw_lines)
        raw_counts["nonblank_noncomment"] += sum(
            bool(line.strip()) for line in code_lines
        )
        for line in code_lines:
            command = declaration_command(line)
            if command is not None:
                command_counts[command] += 1

    definitions = command_counts["def"] + command_counts["abbrev"]
    structures_inductives = (
        command_counts["structure"] + command_counts["inductive"]
    )
    lemmas_theorems = command_counts["lemma"] + command_counts["theorem"]
    examples = command_counts["example"]
    other = sum(
        command_counts[key] for key in ("class", "instance", "opaque", "axiom")
    )
    all_counted = definitions + structures_inductives + lemmas_theorems + examples + other

    return Metrics(
        files=len(paths),
        physical_lines=raw_counts["physical"],
        raw_nonblank_lines=raw_counts["raw_nonblank"],
        nonblank_noncomment_lines=raw_counts["nonblank_noncomment"],
        definitions=definitions,
        structures_inductives=structures_inductives,
        lemmas_theorems=lemmas_theorems,
        examples=examples,
        other_declaration_commands=other,
        all_counted_declaration_commands=all_counted,
        def_commands=command_counts["def"],
        abbrev_commands=command_counts["abbrev"],
        structure_commands=command_counts["structure"],
        inductive_commands=command_counts["inductive"],
        lemma_commands=command_counts["lemma"],
        theorem_commands=command_counts["theorem"],
        example_commands=command_counts["example"],
        class_commands=command_counts["class"],
        instance_commands=command_counts["instance"],
        opaque_commands=command_counts["opaque"],
        axiom_commands=command_counts["axiom"],
    )


def print_markdown(
    closure_metrics: Metrics,
    project_metrics: Metrics,
    closure_list: Path,
) -> None:
    print(f"Repository: {REPO_ROOT}")
    print(f"Branch: {run_git('branch', '--show-current')}")
    print(f"Commit: {run_git('rev-parse', 'HEAD')}")
    print(f"Closure manifest: {closure_list}")
    print(f"Closure manifest SHA-256: {sha256_file(closure_list)}")
    print()
    print(
        "| Scope | Files | Raw physical | Raw nonblank | "
        "Nonblank/noncomment | Defs | Structures + inductives | "
        "Lemmas + theorems | Examples | Other declarations | All counted |"
    )
    print(
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|"
    )
    for name, metrics in (
        ("Final theorem closure", closure_metrics),
        ("Full handwritten project", project_metrics),
    ):
        print(
            f"| {name} | {metrics.files} | {metrics.physical_lines} | "
            f"{metrics.raw_nonblank_lines} | "
            f"{metrics.nonblank_noncomment_lines} | {metrics.definitions} | "
            f"{metrics.structures_inductives} | "
            f"{metrics.lemmas_theorems} | {metrics.examples} | "
            f"{metrics.other_declaration_commands} | "
            f"{metrics.all_counted_declaration_commands} |"
        )
    print()
    print("Definitions group = def + abbrev.")
    print("Other declarations = class + instance + opaque + axiom.")
    print()
    print("| Scope | def | abbrev | structure | inductive | lemma | theorem | "
          "example | class | instance | opaque | axiom |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for name, metrics in (
        ("Final theorem closure", closure_metrics),
        ("Full handwritten project", project_metrics),
    ):
        print(
            f"| {name} | {metrics.def_commands} | {metrics.abbrev_commands} | "
            f"{metrics.structure_commands} | {metrics.inductive_commands} | "
            f"{metrics.lemma_commands} | {metrics.theorem_commands} | "
            f"{metrics.example_commands} | {metrics.class_commands} | "
            f"{metrics.instance_commands} | {metrics.opaque_commands} | "
            f"{metrics.axiom_commands} |"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--closure-list",
        type=Path,
        default=DEFAULT_CLOSURE_LIST,
        help="authoritative relative-path list for the theorem closure",
    )
    parser.add_argument(
        "--expected-closure-files",
        type=int,
        default=46,
        help="fail unless the closure has this many files (default: 46)",
    )
    parser.add_argument(
        "--expected-project-files",
        type=int,
        default=62,
        help="fail unless the handwritten project has this many files (default: 62)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit machine-readable JSON instead of Markdown tables",
    )
    args = parser.parse_args()

    closure_list = args.closure_list.expanduser().resolve()
    closure_paths = validate_paths(
        read_closure_paths(closure_list), "final theorem closure"
    )

    tracked = tracked_lean_paths()
    project_paths = validate_paths(
        [*tracked, *PUBLICATION_MODULES], "full handwritten project"
    )

    if len(closure_paths) != args.expected_closure_files:
        parser.error(
            f"closure has {len(closure_paths)} files; "
            f"expected {args.expected_closure_files}"
        )
    if len(project_paths) != args.expected_project_files:
        parser.error(
            f"project has {len(project_paths)} files; "
            f"expected {args.expected_project_files}"
        )
    if not set(closure_paths).issubset(project_paths):
        missing = sorted(set(closure_paths) - set(project_paths))
        parser.error(f"closure is not a subset of the project: {missing}")

    closure_metrics = measure(closure_paths)
    project_metrics = measure(project_paths)

    if args.json:
        payload = {
            "repository": str(REPO_ROOT),
            "branch": run_git("branch", "--show-current"),
            "commit": run_git("rev-parse", "HEAD"),
            "closure_manifest": str(closure_list),
            "closure_manifest_sha256": sha256_file(closure_list),
            "excluded_roots": sorted(EXCLUDED_PARTS),
            "scopes": {
                "final_theorem_closure": asdict(closure_metrics),
                "full_handwritten_project": asdict(project_metrics),
            },
        }
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print_markdown(closure_metrics, project_metrics, closure_list)


if __name__ == "__main__":
    main()
