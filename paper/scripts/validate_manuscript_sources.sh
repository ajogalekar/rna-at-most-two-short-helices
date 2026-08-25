#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
manuscript_dir="$(cd "$script_dir/.." && pwd -P)"
lean_repo_input="${1:-${RNA_LEAN_REPO:-$manuscript_dir/..}}"
tex_name="Designability_of_RNA_Targets_with_Up_to_Two_Length_2_Helices.tex"
tex_path="$manuscript_dir/$tex_name"
log_path="${tex_path%.tex}.log"
pdf_path="${tex_path%.tex}.pdf"

die() {
  printf 'ERROR: %s\n' "$*" >&2
  exit 1
}

for command_name in python3 lake rg awk diff mktemp tectonic; do
  command -v "$command_name" >/dev/null 2>&1 ||
    die "required command not found: $command_name"
done

[[ -d "$lean_repo_input" ]] ||
  die "Lean repository not found: $lean_repo_input"
lean_repo="$(cd "$lean_repo_input" && pwd -P)"
[[ -f "$lean_repo/lakefile.toml" ]] ||
  die "not a Lean project root: $lean_repo"
[[ -f "$tex_path" ]] || die "manuscript source not found: $tex_path"

printf '==> Regenerating hash-pinned Lean listings\n'
python3 "$script_dir/extract_paper_lean_listings.py" \
  --repo "$lean_repo" \
  --output "$manuscript_dir/paper_listings"

source_map="$manuscript_dir/paper_listings/SOURCE_MAP.tsv"
audit_module="$manuscript_dir/paper_listings/PaperLeanListingAudit.lean"
awk -F '\t' '
  NR == 1 {
    expected = "output_file\tblock_order\tdeclaration\tsource_path\tlean_module\tstart_line\tend_line\tsource_sha256\tblock_sha256"
    if ($0 != expected) exit 1
  }
  NR > 1 {
    if (NF != 9 || $3 == "" || $4 == "" || $5 == "") exit 1
  }
  END {
    if (NR != 43) exit 1
  }
' "$source_map" || die "SOURCE_MAP.tsv schema or 42-row count check failed"

check_count="$(rg -c '^#check ' "$audit_module")"
[[ "$check_count" == "42" ]] ||
  die "expected 42 Lean #check commands, found $check_count"

for listing_name in \
  01_core_model.lean \
  02_helix_target_class.lean \
  03_public_theorem.lean; do
  rg -Fq "{paper_listings/$listing_name}" "$tex_path" ||
    die "manuscript does not include paper_listings/$listing_name"
done

printf '==> Resolving all displayed declarations with pinned Lean\n'
(
  cd "$lean_repo"
  lake build RNA.AtMostTwoShort.Designability
  lake env lean "$audit_module"
)

publication_literals_output="$(mktemp "${TMPDIR:-/tmp}/rna-publication-literals.XXXXXX")"
example_output="$(mktemp "${TMPDIR:-/tmp}/rna-example-verification.XXXXXX")"
dot_bracket_output="$(mktemp "${TMPDIR:-/tmp}/rna-dot-bracket-literals.XXXXXX")"
reference_labels="$(mktemp "${TMPDIR:-/tmp}/rna-reference-labels.XXXXXX")"
cleanup() {
  rm -f "$publication_literals_output" "$example_output" "$dot_bracket_output" "$reference_labels"
}
trap cleanup EXIT

printf '==> Comparing Lean-derived publication sequence literals\n'
(
  cd "$lean_repo"
  lake env lean --run "$manuscript_dir/scripts/ExportPublicationExampleLiterals.lean"
) > "$publication_literals_output"
diff -u "$manuscript_dir/generated/publication_example_literals.tex" \
  "$publication_literals_output"
rg -Fq '{generated/publication_example_literals.tex}' "$tex_path" ||
  die "manuscript does not include generated publication-example literals"
t1_macro_uses="$(rg -o -F '\TOneSequenceLiteral' "$tex_path" | awk 'END {print NR}')"
t2_macro_uses="$(rg -o -F '\TTwoSequenceLiteral' "$tex_path" | awk 'END {print NR}')"
[[ "$t1_macro_uses" == "2" ]] ||
  die "expected exactly two T1 sequence-macro uses, found $t1_macro_uses"
[[ "$t2_macro_uses" == "1" ]] ||
  die "expected exactly one T2 sequence-macro use, found $t2_macro_uses"
t2_assignment_count="$(rg -o -P 'w_2\s*=\s*\\texttt\{\\TTwoSequenceLiteral\}' "$tex_path" | awk 'END {print NR}')"
t2_total_assignments="$(rg -o -P 'w_2\s*=' "$tex_path" | awk 'END {print NR}')"
[[ "$t2_assignment_count" == "1" ]] ||
  die "expected exactly one Lean-derived T2 sequence assignment, found $t2_assignment_count"
[[ "$t2_total_assignments" == "1" ]] ||
  die "expected exactly one total T2 sequence assignment, found $t2_total_assignments"
if rg -n -P 'w_[12]\s*=\s*\\texttt\{[ACGU]+' "$tex_path"; then
  die "raw publication sequence assignment found; use the Lean-derived macro"
fi

printf '==> Comparing exact computational-example output\n'
python3 "$manuscript_dir/verify_examples.py" > "$example_output"
diff -u "$manuscript_dir/EXAMPLE_VERIFICATION.txt" "$example_output"
python3 "$manuscript_dir/check_dot_bracket_literals.py" > "$dot_bracket_output"
diff -u "$manuscript_dir/DOT_BRACKET_LITERAL_AUDIT.txt" "$dot_bracket_output"

printf '==> Scanning terminology, release language, and references\n'
for forbidden_text in \
  'Track A' \
  'Track B' \
  'milestone' \
  'machine-checked extension' \
  'gray port' \
  'resource-aware' \
  'proof oracle' \
  'primary verdict' \
  'resource pipeline' \
  'agent run' \
  'are containing' \
  'length-two' \
  'repository URL pending' \
  'archival DOI pending' \
  'public-source license pending' \
  'is registered when that record is published' \
  'blinded independent audit' \
  'through August 2026' \
  'blinded review bundle' \
  'Claude review package'; do
  if rg -n -F "$forbidden_text" "$tex_path"; then
    die "forbidden superseded manuscript wording found: $forbidden_text"
  fi
done

cutoff_count="$(rg -o -F 'through 19 August 2026' "$tex_path" | awk 'END {print NR}')"
[[ "$cutoff_count" == "2" ]] ||
  die "expected two exact novelty-search cutoffs, found $cutoff_count"

for required_text in \
  'github.com/ajogalekar/rna-at-most-two-short-helices' \
  '10.5281/zenodo.22089626' \
  'Apache License 2.0' \
  'Creative Commons Attribution 4.0 International' \
  'SIL Open Font License 1.1' \
  'immutable Zenodo Software record' \
  '\newcommand{\ReleaseVersion}{1.0.1}' \
  '\textbf{Review status and author responsibility.}' \
  'canonical source archive' \
  'release-qualification results package' \
  'blinded fidelity bundle' \
  'Claude fidelity-audit package' \
  'manuscript source package'; do
  rg -Fq "$required_text" "$tex_path" ||
    die "required manuscript release language missing: $required_text"
done

python3 - "$tex_path" > "$reference_labels" <<'PY'
from pathlib import Path
import re
import sys

text = Path(sys.argv[1]).read_text(encoding="utf-8")
labels = re.findall(r"\\label\{([^{}]+)\}", text)
labels += re.findall(r"\blabel=\{([^{}]+)\}", text)
duplicates = sorted({label for label in labels if labels.count(label) > 1})
references = []
for group in re.findall(
    r"\\(?:ref|cref|Cref|eqref|autoref)\{([^{}]+)\}", text
):
    references.extend(part.strip() for part in group.split(","))
missing = sorted(set(references) - set(labels))
if duplicates:
    raise SystemExit("duplicate labels: " + ", ".join(duplicates))
if missing:
    raise SystemExit("undefined source references: " + ", ".join(missing))
print(f"labels={len(set(labels))} references={len(references)} missing=0 duplicates=0")
PY
cat "$reference_labels"

printf '==> Building the final manuscript with Tectonic\n'
(
  cd "$manuscript_dir"
  SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1787529600}" \
    tectonic --keep-logs "$tex_name"
)
[[ -s "$pdf_path" ]] || die "Tectonic did not produce a nonempty PDF"
[[ -f "$log_path" ]] || die "Tectonic did not retain the LaTeX log"
if rg -n -i \
    'undefined (citation|reference|references)|citation.*undefined|reference.*undefined|there were undefined references' \
    "$log_path"; then
  die "undefined citation/reference warning found in the Tectonic log"
fi

printf 'PASS: listings, Lean checks, examples, manuscript language, references, and PDF build\n'
