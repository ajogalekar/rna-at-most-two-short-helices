# License scopes

This repository is a mixed-license publication artifact. The primary software
license reported by GitHub and Zenodo is Apache License 2.0. The following
path-based scopes are authoritative.

## Apache License 2.0 — Lean source and software

The exact terms are in [`LICENSE`](LICENSE). They apply to:

- `RNA.lean` and every file under `RNA/`;
- `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json`;
- every file under `scripts/` and `.github/`;
- `paper/scripts/` and `paper/verify_examples.py`;
- source-derived Lean code under `paper/paper_listings/*.lean`; and
- any other project software not assigned a different license below.

The Lean listing files are excerpts of the Apache-2.0-licensed formal source,
not separately licensed manuscript prose.

## Creative Commons Attribution 4.0 International — paper and documentation

The exact legal code is in
[`LICENSES/CC-BY-4.0.txt`](LICENSES/CC-BY-4.0.txt). It applies to:

- `README.md`, `LICENSES.md`, `CITATION.cff`, `.zenodo.json`, and
  `RELEASE_NOTES.md`;
- all project-written documents and reports under `docs/`;
- the manuscript text and original TikZ figures in `paper/*.tex` and the
  rendered `paper/*.pdf`;
- project-written files under `paper/docs/` and `paper/supplement/`;
- source-derived manuscript macros under `paper/generated/*.tex`;
- `paper/README.md`, paper review/revision records, terminology notes, example
  output, and the paper manifest; and
- project-written listing documentation and maps under `paper/paper_listings/`
  other than the `.lean` source excerpts described above.

Attribution should identify Ashutosh S. Jogalekar, the work title
“Designability of RNA Targets with Up to Two Length-2 Helices,” and the
repository or archival DOI for the version used.

## STIX fonts — STIX Font License / SIL Open Font License 1.1 terms

The bundled `.otf` files under `paper/fonts/` and their font documentation are
distributed under the license shipped with those fonts. The preserved text is
available at both [`paper/fonts/LICENSE.txt`](paper/fonts/LICENSE.txt) and
[`LICENSES/OFL-1.1.txt`](LICENSES/OFL-1.1.txt).

## Precedence

When categories overlap, the most specific path rule above controls: formal
code and source-derived Lean excerpts remain Apache-2.0; bundled font files
remain under their font license; all other manuscript and project-documentation
material is CC BY 4.0.
