import Fuglede.Z180K18M6DPArithmetic
import Fuglede.Z180K18M6EnvelopeInterfaces
import Fuglede.Z180K18M12DPSemanticDefs
import Fuglede.Z180K18M2Phi2Phi6Semantic
import Fuglede.Z180K18M4Phi4HighSemantic
import Fuglede.Z180K12M6HighOrderRemainders18Shard
import Fuglede.Z180K12M6HighOrderRemainders36ZeroShard
import Fuglede.Z180K12DescentOrder12Converse
import Mathlib.Tactic

/-! Shared data for the sharded semantic realization of the residual
`m = 6` DP families.  The local balance coordinates are the common
`z180K18M12DP*` coordinates from the order-twelve semantic layer. -/

namespace Fuglede

/-- Projection occupancy, nine-fibre masses, and the nonzero `Phi_6`
five-multiple defect shared by all four semantic leaves. -/
structure Z180K18M6DPBaseData (b : Fin 36 → Int) where
  lo : ∀ i : Fin 36, 0 ≤ b i
  hi : ∀ i : Fin 36, b i ≤ 1
  mass0 : b 0 + b 9 + b 18 + b 27 = 2
  mass1 : b 1 + b 10 + b 19 + b 28 = 2
  mass2 : b 2 + b 11 + b 20 + b 29 = 2
  mass3 : b 3 + b 12 + b 21 + b 30 = 2
  mass4 : b 4 + b 13 + b 22 + b 31 = 2
  mass5 : b 5 + b 14 + b 23 + b 32 = 2
  mass6 : b 6 + b 15 + b 24 + b 33 = 2
  mass7 : b 7 + b 16 + b 25 + b 34 = 2
  mass8 : b 8 + b 17 + b 26 + b 35 = 2
  k60 : Int
  k61 : Int
  mul60 : projection36Phi6R0 b = 5 * k60
  mul61 : projection36Phi6R1 b = 5 * k61
  nonzero : Z180K18M6TwoRemaindersNonzero
    (projection36Phi6R0 b) (projection36Phi6R1 b)

end Fuglede
