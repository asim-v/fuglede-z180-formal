import Mathlib.Data.Int.Basic

/-! The two periodic alternatives forced by a six-term `Phi_36` zero. -/

namespace Fuglede

def Z36AntipodalIndicator (b : Fin 36 → Int) : Prop :=
  b 0 = b 18 ∧ b 1 = b 19 ∧ b 2 = b 20 ∧
  b 3 = b 21 ∧ b 4 = b 22 ∧ b 5 = b 23 ∧
  b 6 = b 24 ∧ b 7 = b 25 ∧ b 8 = b 26 ∧
  b 9 = b 27 ∧ b 10 = b 28 ∧ b 11 = b 29 ∧
  b 12 = b 30 ∧ b 13 = b 31 ∧ b 14 = b 32 ∧
  b 15 = b 33 ∧ b 16 = b 34 ∧ b 17 = b 35

def Z36ThreeCycleIndicator (b : Fin 36 → Int) : Prop :=
  b 0 = b 12 ∧ b 12 = b 24 ∧ b 1 = b 13 ∧ b 13 = b 25 ∧
  b 2 = b 14 ∧ b 14 = b 26 ∧ b 3 = b 15 ∧ b 15 = b 27 ∧
  b 4 = b 16 ∧ b 16 = b 28 ∧ b 5 = b 17 ∧ b 17 = b 29 ∧
  b 6 = b 18 ∧ b 18 = b 30 ∧ b 7 = b 19 ∧ b 19 = b 31 ∧
  b 8 = b 20 ∧ b 20 = b 32 ∧ b 9 = b 21 ∧ b 21 = b 33 ∧
  b 10 = b 22 ∧ b 22 = b 34 ∧ b 11 = b 23 ∧ b 23 = b 35

end Fuglede
