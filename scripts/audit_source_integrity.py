#!/usr/bin/env python3
"""Verify frozen Lean sources, theorem closure hashes, and import direction."""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import sys
from pathlib import Path


DEFAULT_BASELINE = "28070dd0032f417b1eed03a1fa23f81a260eaff7"
EXPECTED_PUBLICATION_MODULES = {
    "RNA/AtMostTwoShort/PublicationExamples.lean",
    "RNA/AtMostTwoShort/PublicationExamplesAxiomAudit.lean",
}
PUBLICATION_IMPORT = re.compile(
    r"^\s*(?:public\s+)?import\s+"
    r"RNA\.AtMostTwoShort\.PublicationExamples(?:AxiomAudit)?\s*$",
    re.MULTILINE,
)


def git(root: Path, *args: str) -> bytes:
    return subprocess.run(
        ("git", *args),
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_sidecar(path: Path) -> list[tuple[str, str]]:
    entries: list[tuple[str, str]] = []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if not match:
            raise ValueError(f"malformed sidecar line {number}: {line!r}")
        entries.append((match.group(1), match.group(2)))
    return entries


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", default=DEFAULT_BASELINE)
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    baseline_paths = {
        line
        for line in git(root, "ls-tree", "-r", "--name-only", args.baseline).decode().splitlines()
        if line.endswith(".lean")
    }
    current_tracked = {
        line
        for line in git(root, "ls-files", "*.lean").decode().splitlines()
        if line
    }
    current_untracked = {
        line
        for line in git(root, "ls-files", "--others", "--exclude-standard", "*.lean").decode().splitlines()
        if line
    }
    current_union = current_tracked | current_untracked
    publication_modules = current_union - baseline_paths

    changed: list[str] = []
    missing: list[str] = []
    for relative in sorted(baseline_paths):
        path = root / relative
        if not path.is_file():
            missing.append(relative)
            continue
        baseline_bytes = git(root, "show", f"{args.baseline}:{relative}")
        if path.read_bytes() != baseline_bytes:
            changed.append(relative)

    sidecar_path = root / "docs/THEOREM_CLOSURE_BASELINE.sha256"
    sidecar = parse_sidecar(sidecar_path)
    sidecar_paths = [relative for _, relative in sidecar]
    closure_mismatches = [
        relative
        for expected, relative in sidecar
        if not (root / relative).is_file()
        or digest((root / relative).read_bytes()) != expected
    ]

    reverse_imports: list[str] = []
    for relative in sorted(baseline_paths):
        text = (root / relative).read_text(encoding="utf-8")
        if PUBLICATION_IMPORT.search(text):
            reverse_imports.append(relative)

    checks = {
        "baseline_lean_file_count": len(baseline_paths) == 60,
        "preexisting_files_missing": not missing,
        "preexisting_files_changed": not changed,
        "closure_entry_count": len(sidecar) == 46,
        "closure_paths_unique": len(sidecar_paths) == len(set(sidecar_paths)),
        "closure_digest_mismatches": not closure_mismatches,
        "publication_module_set": publication_modules == EXPECTED_PUBLICATION_MODULES,
        "full_handwritten_union_count": len(current_union) == 62,
        "reverse_imports_from_preexisting_sources": not reverse_imports,
    }

    print(f"baseline_commit={args.baseline}")
    print(f"baseline_lean_files={len(baseline_paths)}")
    print(f"current_tracked_lean_files={len(current_tracked)}")
    print(f"current_untracked_lean_files={len(current_untracked)}")
    print(f"full_handwritten_union_files={len(current_union)}")
    print(f"closure_sidecar_sha256={digest(sidecar_path.read_bytes())}")
    print(f"closure_entries={len(sidecar)}")
    print(f"preexisting_missing={len(missing)}")
    print(f"preexisting_changed={len(changed)}")
    print(f"closure_digest_mismatches={len(closure_mismatches)}")
    print(f"reverse_imports={len(reverse_imports)}")
    print("publication_modules=" + ",".join(sorted(publication_modules)))
    for label, passed in checks.items():
        print(f"CHECK {label}={'PASS' if passed else 'FAIL'}")

    details = {
        "MISSING": missing,
        "CHANGED": changed,
        "CLOSURE_MISMATCH": closure_mismatches,
        "REVERSE_IMPORT": reverse_imports,
    }
    for label, paths in details.items():
        for relative in paths:
            print(f"{label} {relative}")

    if all(checks.values()):
        print("RESULT=PASS")
        return 0
    print("RESULT=FAIL")
    return 1


if __name__ == "__main__":
    sys.exit(main())
