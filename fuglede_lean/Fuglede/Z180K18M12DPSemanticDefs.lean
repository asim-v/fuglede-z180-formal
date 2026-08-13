import Fuglede.Z180K18M12DPInterfaces
import Fuglede.Z180K18M12DPArithmeticSharded
import Fuglede.Z180K18M4Phi4HighSemantic
import Fuglede.Z180K12M6HighOrderRemainders18Shard
import Fuglede.Z180K12M6HighOrderRemainders36ZeroShard
import Fuglede.Z180K12DescentOrder12Converse
import Mathlib.Tactic

/-! Shared definitions for the sharded semantic realization of the residual
`m = 12` DP families. -/

namespace Fuglede

def z180K18M12DPx0 (b : Fin 36 → Int) : Int := b 0 - b 18
def z180K18M12DPy0 (b : Fin 36 → Int) : Int := b 9 - b 27
def z180K18M12DPz0 (b : Fin 36 → Int) : Int := b 0 + b 18 - 1
def z180K18M12DPx1 (b : Fin 36 → Int) : Int := b 28 - b 10
def z180K18M12DPy1 (b : Fin 36 → Int) : Int := b 1 - b 19
def z180K18M12DPz1 (b : Fin 36 → Int) : Int := b 1 + b 19 - 1
def z180K18M12DPx2 (b : Fin 36 → Int) : Int := b 20 - b 2
def z180K18M12DPy2 (b : Fin 36 → Int) : Int := b 29 - b 11
def z180K18M12DPz2 (b : Fin 36 → Int) : Int := b 2 + b 20 - 1
def z180K18M12DPx3 (b : Fin 36 → Int) : Int := b 12 - b 30
def z180K18M12DPy3 (b : Fin 36 → Int) : Int := b 21 - b 3
def z180K18M12DPz3 (b : Fin 36 → Int) : Int := b 3 + b 21 - 1
def z180K18M12DPx4 (b : Fin 36 → Int) : Int := b 4 - b 22
def z180K18M12DPy4 (b : Fin 36 → Int) : Int := b 13 - b 31
def z180K18M12DPz4 (b : Fin 36 → Int) : Int := b 4 + b 22 - 1
def z180K18M12DPx5 (b : Fin 36 → Int) : Int := b 32 - b 14
def z180K18M12DPy5 (b : Fin 36 → Int) : Int := b 5 - b 23
def z180K18M12DPz5 (b : Fin 36 → Int) : Int := b 5 + b 23 - 1
def z180K18M12DPx6 (b : Fin 36 → Int) : Int := b 24 - b 6
def z180K18M12DPy6 (b : Fin 36 → Int) : Int := b 33 - b 15
def z180K18M12DPz6 (b : Fin 36 → Int) : Int := b 6 + b 24 - 1
def z180K18M12DPx7 (b : Fin 36 → Int) : Int := b 16 - b 34
def z180K18M12DPy7 (b : Fin 36 → Int) : Int := b 25 - b 7
def z180K18M12DPz7 (b : Fin 36 → Int) : Int := b 7 + b 25 - 1
def z180K18M12DPx8 (b : Fin 36 → Int) : Int := b 8 - b 26
def z180K18M12DPy8 (b : Fin 36 → Int) : Int := b 17 - b 35
def z180K18M12DPz8 (b : Fin 36 → Int) : Int := b 8 + b 26 - 1

def z180K18M12DPX0 (b : Fin 36 → Int) : Int :=
  z180K18M12DPx0 b + z180K18M12DPx3 b + z180K18M12DPx6 b
def z180K18M12DPX1 (b : Fin 36 → Int) : Int :=
  z180K18M12DPx1 b + z180K18M12DPx4 b + z180K18M12DPx7 b
def z180K18M12DPX2 (b : Fin 36 → Int) : Int :=
  z180K18M12DPx2 b + z180K18M12DPx5 b + z180K18M12DPx8 b
def z180K18M12DPY0 (b : Fin 36 → Int) : Int :=
  z180K18M12DPy0 b + z180K18M12DPy3 b + z180K18M12DPy6 b
def z180K18M12DPY1 (b : Fin 36 → Int) : Int :=
  z180K18M12DPy1 b + z180K18M12DPy4 b + z180K18M12DPy7 b
def z180K18M12DPY2 (b : Fin 36 → Int) : Int :=
  z180K18M12DPy2 b + z180K18M12DPy5 b + z180K18M12DPy8 b
def z180K18M12DPW0 (b : Fin 36 → Int) : Int :=
  z180K18M12DPz0 b - z180K18M12DPz3 b + z180K18M12DPz6 b
def z180K18M12DPW1 (b : Fin 36 → Int) : Int :=
  z180K18M12DPz1 b - z180K18M12DPz4 b + z180K18M12DPz7 b
def z180K18M12DPW2 (b : Fin 36 → Int) : Int :=
  z180K18M12DPz2 b - z180K18M12DPz5 b + z180K18M12DPz8 b

/-- Projection occupancy, nine fibre masses, and the nonzero `Phi_12`
five-multiple defect shared by all four semantic leaves. -/
structure Z180K18M12DPBaseData (b : Fin 36 → Int) where
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
  k120 : Int
  k121 : Int
  k122 : Int
  k123 : Int
  mul120 : Z180K12HighOrder.projection36Phi12R0 b = 5 * k120
  mul121 : Z180K12HighOrder.projection36Phi12R1 b = 5 * k121
  mul122 : Z180K12HighOrder.projection36Phi12R2 b = 5 * k122
  mul123 : Z180K12HighOrder.projection36Phi12R3 b = 5 * k123
  nonzero : ¬ (Z180K12HighOrder.projection36Phi12R0 b = 0 ∧
    Z180K12HighOrder.projection36Phi12R1 b = 0 ∧
    Z180K12HighOrder.projection36Phi12R2 b = 0 ∧
    Z180K12HighOrder.projection36Phi12R3 b = 0)

end Fuglede
