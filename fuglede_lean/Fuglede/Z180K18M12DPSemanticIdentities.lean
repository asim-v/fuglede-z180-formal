import Fuglede.Z180K18M12DPSemanticAggregates

/-! Small algebraic identities shared by the four semantic leaves. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_threeFiberBalance_X_bounds
    (X W e : Int) (h : Z180K18M12ThreeFiberBalance X W e) :
    -3 ≤ X ∧ X ≤ 3 := by
  dsimp only [Z180K18M12ThreeFiberBalance] at h
  omega

theorem z180_k18_m12_dp_diff_bounds
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b)
    (i j : Fin 36) :
    -1 ≤ b i - b j ∧ b i - b j ≤ 1 := by
  have hilo := d.lo i
  have hihi := d.hi i
  have hjlo := d.lo j
  have hjhi := d.hi j
  omega

theorem z180_k18_m12_dp_pair_bounds
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b)
    (i j : Fin 36) :
    -1 ≤ b i + b j - 1 ∧ b i + b j - 1 ≤ 1 := by
  have hilo := d.lo i
  have hihi := d.hi i
  have hjlo := d.lo j
  have hjhi := d.hi j
  omega

theorem z180_k18_m12_dp_R120 (b : Fin 36 → Int) :
    Z180K12HighOrder.projection36Phi12R0 b =
      z180K18M12DPX0 b - z180K18M12DPX1 b := by
  change
    ((b 0 + b 12 + b 24) - (b 4 + b 16 + b 28) -
      (b 6 + b 18 + b 30) + (b 10 + b 22 + b 34)) = _
  dsimp only [z180K18M12DPX0, z180K18M12DPX1,
    z180K18M12DPx0, z180K18M12DPx1, z180K18M12DPx3,
    z180K18M12DPx4, z180K18M12DPx6, z180K18M12DPx7]
  ring

theorem z180_k18_m12_dp_R121 (b : Fin 36 → Int) :
    Z180K12HighOrder.projection36Phi12R1 b =
      z180K18M12DPY1 b - z180K18M12DPY2 b := by
  change
    ((b 1 + b 13 + b 25) - (b 5 + b 17 + b 29) -
      (b 7 + b 19 + b 31) + (b 11 + b 23 + b 35)) = _
  dsimp only [z180K18M12DPY1, z180K18M12DPY2,
    z180K18M12DPy1, z180K18M12DPy2, z180K18M12DPy4,
    z180K18M12DPy5, z180K18M12DPy7, z180K18M12DPy8]
  ring

theorem z180_k18_m12_dp_R122 (b : Fin 36 → Int) :
    Z180K12HighOrder.projection36Phi12R2 b =
      z180K18M12DPX1 b - z180K18M12DPX2 b := by
  change
    ((b 2 + b 14 + b 26) + (b 4 + b 16 + b 28) -
      (b 8 + b 20 + b 32) - (b 10 + b 22 + b 34)) = _
  dsimp only [z180K18M12DPX1, z180K18M12DPX2,
    z180K18M12DPx1, z180K18M12DPx2, z180K18M12DPx4,
    z180K18M12DPx5, z180K18M12DPx7, z180K18M12DPx8]
  ring

theorem z180_k18_m12_dp_R123 (b : Fin 36 → Int) :
    Z180K12HighOrder.projection36Phi12R3 b =
      -z180K18M12DPY0 b + z180K18M12DPY2 b := by
  change
    ((b 3 + b 15 + b 27) + (b 5 + b 17 + b 29) -
      (b 9 + b 21 + b 33) - (b 11 + b 23 + b 35)) = _
  dsimp only [z180K18M12DPY0, z180K18M12DPY2,
    z180K18M12DPy0, z180K18M12DPy2, z180K18M12DPy3,
    z180K18M12DPy5, z180K18M12DPy6, z180K18M12DPy8]
  ring

theorem z180_k18_m12_dp_R40 (b : Fin 36 → Int) :
    z180K18ProjectionPhi4R0 b =
      z180K18M12DPX0 b + z180K18M12DPX1 b + z180K18M12DPX2 b := by
  change
    ((b 0 + b 12 + b 24) - (b 2 + b 14 + b 26) +
      (b 4 + b 16 + b 28) - (b 6 + b 18 + b 30) +
      (b 8 + b 20 + b 32) - (b 10 + b 22 + b 34)) = _
  dsimp only [z180K18M12DPX0, z180K18M12DPX1, z180K18M12DPX2,
    z180K18M12DPx0, z180K18M12DPx1, z180K18M12DPx2,
    z180K18M12DPx3, z180K18M12DPx4, z180K18M12DPx5,
    z180K18M12DPx6, z180K18M12DPx7, z180K18M12DPx8]
  ring

theorem z180_k18_m12_dp_R41 (b : Fin 36 → Int) :
    z180K18ProjectionPhi4R1 b =
      z180K18M12DPY0 b + z180K18M12DPY1 b + z180K18M12DPY2 b := by
  change
    ((b 1 + b 13 + b 25) - (b 3 + b 15 + b 27) +
      (b 5 + b 17 + b 29) - (b 7 + b 19 + b 31) +
      (b 9 + b 21 + b 33) - (b 11 + b 23 + b 35)) = _
  dsimp only [z180K18M12DPY0, z180K18M12DPY1, z180K18M12DPY2,
    z180K18M12DPy0, z180K18M12DPy1, z180K18M12DPy2,
    z180K18M12DPy3, z180K18M12DPy4, z180K18M12DPy5,
    z180K18M12DPy6, z180K18M12DPy7, z180K18M12DPy8]
  ring

theorem z180_k18_m12_dp_R60
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b) :
    projection36Phi6R0 b =
      2 * (z180K18M12DPW0 b - z180K18M12DPW2 b) := by
  dsimp only [projection36Phi6R0, z180K18M12DPW0,
    z180K18M12DPW2, z180K18M12DPz0, z180K18M12DPz2,
    z180K18M12DPz3, z180K18M12DPz5, z180K18M12DPz6,
    z180K18M12DPz8]
  linear_combination
    -d.mass0 + d.mass2 + d.mass3 - d.mass5 - d.mass6 + d.mass8

theorem z180_k18_m12_dp_R61
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b) :
    projection36Phi6R1 b =
      2 * (z180K18M12DPW1 b + z180K18M12DPW2 b) := by
  dsimp only [projection36Phi6R1, z180K18M12DPW1,
    z180K18M12DPW2, z180K18M12DPz1, z180K18M12DPz2,
    z180K18M12DPz4, z180K18M12DPz5, z180K18M12DPz7,
    z180K18M12DPz8]
  linear_combination
    -d.mass1 - d.mass2 + d.mass4 + d.mass5 - d.mass7 - d.mass8

theorem z180_k18_m12_dp_aggregate_nonzero
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b) :
    Z180K18M12FourRemaindersNonzero
      (z180K18M12DPX0 b - z180K18M12DPX1 b)
      (z180K18M12DPY1 b - z180K18M12DPY2 b)
      (z180K18M12DPX1 b - z180K18M12DPX2 b)
      (-z180K18M12DPY0 b + z180K18M12DPY2 b) := by
  dsimp only [Z180K18M12FourRemaindersNonzero]
  intro hz
  apply d.nonzero
  constructor
  · rw [z180_k18_m12_dp_R120]
    exact hz.1
  constructor
  · rw [z180_k18_m12_dp_R121]
    exact hz.2.1
  constructor
  · rw [z180_k18_m12_dp_R122]
    exact hz.2.2.1
  · rw [z180_k18_m12_dp_R123]
    exact hz.2.2.2

#print axioms z180_k18_m12_dp_R120
#print axioms z180_k18_m12_dp_R40
#print axioms z180_k18_m12_dp_R60
#print axioms z180_k18_m12_dp_aggregate_nonzero

end Fuglede
