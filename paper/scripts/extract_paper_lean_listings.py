#!/usr/bin/env python3
"""Extract the manuscript's Lean listings from the frozen theorem sources.

The extraction is intentionally line-based and hash-pinned.  It refuses to
produce listings if any frozen source file differs from the audited version.
"""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import dataclass
from pathlib import Path
import sys


SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_REPO = SCRIPT_DIR.parent.parent
DEFAULT_OUTPUT = SCRIPT_DIR.parent / "paper_listings"


FROZEN_SOURCE_HASHES = {
    "RNA/Alphabet.lean": "da4bc09c95a4b23b73ebc2493881ccafee46362c6aebefe95d18fb2f9c5e258f",
    "RNA/Structure.lean": "ab3662a5730dd1d42f53859d43750a15e9b0edcb1e21e4a8ca0e3d5cda4d5451",
    "RNA/Helix.lean": "03b69def8a4baefac27dde9d1ae4fde98dcf0cacc3e6345ef8d2392532dc7465",
    "RNA/Motifs.lean": "79eecd6fb95fc33566dfbd81834c82a76c88dae17b9889c830be32e4b58a570a",
    "RNA/AtMostTwoShort/TargetClass.lean": "18be543996a716ea1be6589ad5cc160299b47cbe22adde4b62382209a9834254",
    "RNA/AtMostTwoShort/Designability.lean": "14336b0650651ea64387637318dd0005d0ce5d8239f50228e1025d6cc733c36e",
}

LEAN_MODULES = {
    "RNA/Alphabet.lean": "RNA.Alphabet",
    "RNA/Structure.lean": "RNA.Structure",
    "RNA/Helix.lean": "RNA.Helix",
    "RNA/Motifs.lean": "RNA.Motifs",
    "RNA/AtMostTwoShort/TargetClass.lean": "RNA.AtMostTwoShort.TargetClass",
    "RNA/AtMostTwoShort/Designability.lean": "RNA.AtMostTwoShort.Designability",
}


@dataclass(frozen=True)
class Block:
    output_file: str
    declaration: str
    source_path: str
    start_line: int
    end_line: int


BLOCKS = (
    Block("01_core_model.lean", "RNA.Nucleotide", "RNA/Alphabet.lean", 28, 33),
    Block("01_core_model.lean", "RNA.Nucleotide.comp", "RNA/Alphabet.lean", 45, 49),
    Block("01_core_model.lean", "RNA.Compatible", "RNA/Alphabet.lean", 68, 68),
    Block("01_core_model.lean", "RNA.Sequence", "RNA/Alphabet.lean", 110, 110),
    Block("01_core_model.lean", "RNA.Arc", "RNA/Structure.lean", 26, 30),
    Block("01_core_model.lean", "RNA.Arc.Crosses", "RNA/Structure.lean", 113, 115),
    Block("01_core_model.lean", "RNA.IsPartialMatching", "RNA/Structure.lean", 132, 135),
    Block("01_core_model.lean", "RNA.IsNoncrossing", "RNA/Structure.lean", 138, 141),
    Block("01_core_model.lean", "RNA.SecondaryStructure", "RNA/Structure.lean", 152, 155),
    Block("01_core_model.lean", "RNA.StructureCompatible", "RNA/Structure.lean", 239, 240),
    Block("01_core_model.lean", "RNA.pairCount", "RNA/Structure.lean", 252, 252),
    Block("01_core_model.lean", "RNA.UniqueDesigns", "RNA/Structure.lean", 273, 278),
    Block("02_helix_target_class.lean", "RNA.HelixCandidate", "RNA/Helix.lean", 71, 71),
    Block("02_helix_target_class.lean", "RNA.HelixCandidate.outer", "RNA/Helix.lean", 75, 75),
    Block("02_helix_target_class.lean", "RNA.HelixCandidate.length", "RNA/Helix.lean", 77, 77),
    Block("02_helix_target_class.lean", "RNA.HasStackOffset", "RNA/Helix.lean", 87, 88),
    Block("02_helix_target_class.lean", "RNA.IsMaximalHelixRun", "RNA/Helix.lean", 97, 102),
    Block("02_helix_target_class.lean", "RNA.IsMaximalHelix", "RNA/Helix.lean", 122, 123),
    Block("02_helix_target_class.lean", "RNA.MaximalHelix", "RNA/Helix.lean", 131, 132),
    Block("02_helix_target_class.lean", "RNA.MaximalHelix.outer", "RNA/Helix.lean", 155, 155),
    Block("02_helix_target_class.lean", "RNA.MaximalHelix.length", "RNA/Helix.lean", 157, 157),
    Block("02_helix_target_class.lean", "RNA.HasM5", "RNA/Motifs.lean", 30, 31),
    Block("02_helix_target_class.lean", "RNA.HasM3Dot", "RNA/Motifs.lean", 35, 37),
    Block(
        "02_helix_target_class.lean",
        "RNA.lengthTwoHelices",
        "RNA/AtMostTwoShort/TargetClass.lean",
        21,
        22,
    ),
    Block(
        "02_helix_target_class.lean",
        "RNA.shortHelixCount",
        "RNA/AtMostTwoShort/TargetClass.lean",
        25,
        26,
    ),
    Block(
        "02_helix_target_class.lean",
        "RNA.InTargetClassKLeTwo",
        "RNA/AtMostTwoShort/TargetClass.lean",
        111,
        116,
    ),
    Block(
        "03_public_theorem.lean",
        "RNA.AtMostTwoShortHelixDesignabilityStatement",
        "RNA/AtMostTwoShort/Designability.lean",
        45,
        48,
    ),
    Block(
        "03_public_theorem.lean",
        "RNA.atMostTwoShortHelixDesignability",
        "RNA/AtMostTwoShort/Designability.lean",
        52,
        58,
    ),
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def extract_block(lines: list[str], block: Block) -> str:
    if block.start_line < 1 or block.end_line < block.start_line:
        raise ValueError(f"invalid line range for {block.declaration}")
    if block.end_line > len(lines):
        raise ValueError(
            f"{block.source_path} has {len(lines)} lines; cannot extract "
            f"{block.start_line}-{block.end_line}"
        )
    return "".join(lines[block.start_line - 1 : block.end_line])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=DEFAULT_REPO)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    repo = args.repo.expanduser().resolve()
    output = args.output.expanduser().resolve()

    sources: dict[str, tuple[list[str], str]] = {}
    for relative_path, expected_hash in FROZEN_SOURCE_HASHES.items():
        source = repo / relative_path
        try:
            data = source.read_bytes()
        except OSError as exc:
            print(f"ERROR: cannot read {source}: {exc}", file=sys.stderr)
            return 2
        actual_hash = sha256_bytes(data)
        if actual_hash != expected_hash:
            print(
                f"ERROR: frozen-source hash mismatch for {relative_path}\n"
                f"  expected {expected_hash}\n"
                f"  actual   {actual_hash}",
                file=sys.stderr,
            )
            return 3
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError as exc:
            print(f"ERROR: {source} is not UTF-8: {exc}", file=sys.stderr)
            return 4
        sources[relative_path] = (text.splitlines(keepends=True), actual_hash)

    output.mkdir(parents=True, exist_ok=True)
    grouped: dict[str, list[tuple[Block, str]]] = {}
    for block in BLOCKS:
        lines, _ = sources[block.source_path]
        grouped.setdefault(block.output_file, []).append(
            (block, extract_block(lines, block))
        )

    for output_file, entries in grouped.items():
        # The sole inserted material is one blank separator line between exact
        # source blocks; the content of every mapped block is byte-for-byte.
        rendered = "\n".join(text.rstrip("\n") for _, text in entries) + "\n"
        (output / output_file).write_text(rendered, encoding="utf-8", newline="\n")

    map_header = (
        "output_file\tblock_order\tdeclaration\tsource_path\tlean_module\t"
        "start_line\tend_line\tsource_sha256\tblock_sha256\n"
    )
    map_rows = []
    per_file_order: dict[str, int] = {}
    for block in BLOCKS:
        per_file_order[block.output_file] = per_file_order.get(block.output_file, 0) + 1
        lines, source_hash = sources[block.source_path]
        block_text = extract_block(lines, block)
        map_rows.append(
            "\t".join(
                (
                    block.output_file,
                    str(per_file_order[block.output_file]),
                    block.declaration,
                    block.source_path,
                    LEAN_MODULES[block.source_path],
                    str(block.start_line),
                    str(block.end_line),
                    source_hash,
                    sha256_bytes(block_text.encode("utf-8")),
                )
            )
            + "\n"
        )
    (output / "SOURCE_MAP.tsv").write_text(
        map_header + "".join(map_rows), encoding="utf-8", newline="\n"
    )

    print(f"Validated {len(FROZEN_SOURCE_HASHES)} frozen source files.")
    print(f"Extracted {len(BLOCKS)} declaration blocks into {len(grouped)} listings.")
    print(f"Wrote source map: {output / 'SOURCE_MAP.tsv'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
