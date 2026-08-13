import Fuglede.Z180K30ExceptionalRawCoreV2

/-!
# Exact five-Gram witness for the surviving K30 exceptional orbit

This file records the positive half of the finite certificate.  All entries
are literal subsets of `Fin 36`, and the equality is checked in the integral
basis of `Z[x] / (x^12 - x^6 + 1)` supplied by the raw core.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalH : RawSet := [0, 6, 12, 18, 24, 30]

def z180K30ExceptionalHStarWitness (i : Fin 5) : RawSet :=
  match i with
  | 0 => [0, 1, 12, 18, 24, 30]
  | 1 => [1, 10, 16, 22, 28, 34]
  | 2 => [1, 11, 17, 23, 29, 35]
  | 3 => [1, 2, 14, 20, 26, 32]
  | 4 => [1, 3, 15, 21, 27, 33]

set_option maxRecDepth 100000 in
theorem z180_k30_exceptional_H_fiveGramStar :
    fiveGramStarB z180K30ExceptionalHStarWitness z180K30ExceptionalH = true := by
  decide

#print axioms z180_k30_exceptional_H_fiveGramStar

end Fuglede.Z180K30ExceptionalRawV2
