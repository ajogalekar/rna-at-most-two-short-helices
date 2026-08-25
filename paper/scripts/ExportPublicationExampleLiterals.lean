import RNA.AtMostTwoShort.PublicationExamples

open RNA RNA.PublicationExamples

private def nucleotideLetter : Nucleotide → Char
  | .A => 'A'
  | .C => 'C'
  | .G => 'G'
  | .U => 'U'

private def sequenceLiteral {n : Nat} (w : Sequence n) : String :=
  String.ofList ((List.ofFn w).map nucleotideLetter)

def main : IO Unit := do
  IO.println "% AUTO-GENERATED from actual Lean sequence values; do not edit."
  IO.println "% Source: RNA/AtMostTwoShort/PublicationExamples.lean"
  IO.println ("\\newcommand{\\TOneSequenceLiteral}{" ++ sequenceLiteral w1 ++ "}")
  IO.println ("\\newcommand{\\TTwoSequenceLiteral}{" ++ sequenceLiteral w2 ++ "}")
