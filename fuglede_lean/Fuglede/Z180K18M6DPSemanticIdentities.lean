import Fuglede.Z180K18M6DPSemanticAggregates
import Fuglede.Z180K18M12DPSemanticIdentities

/-! Small algebraic identities shared by the four `m = 6` semantic leaves. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m6_threeFiberBalance_W_bounds
    (X W e : Int) (h : Z180K18M12ThreeFiberBalance X W e) :
    -3 ≤ W ∧ W ≤ 3 := by
  dsimp only [Z180K18M12ThreeFiberBalance] at h
  omega

theorem z180_k18_m6_dp_diff_bounds
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b)
    (i j : Fin 36) :
    -1 ≤ b i - b j ∧ b i - b j ≤ 1 := by
  have hilo := d.lo i
  have hihi := d.hi i
  have hjlo := d.lo j
  have hjhi := d.hi j
  omega

theorem z180_k18_m6_dp_pair_bounds
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b)
    (i j : Fin 36) :
    -1 ≤ b i + b j - 1 ∧ b i + b j - 1 ≤ 1 := by
  have hilo := d.lo i
  have hihi := d.hi i
  have hjlo := d.lo j
  have hjhi := d.hi j
  omega

theorem z180_k18_m6_dp_R2
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b) :
    z180K18ProjectionPhi2R0 b =
      2 * (z180K18M12DPW0 b - z180K18M12DPW1 b +
        z180K18M12DPW2 b) := by
  dsimp only [z180K18ProjectionPhi2R0,
    z180K18M12DPW0, z180K18M12DPW1, z180K18M12DPW2,
    z180K18M12DPz0, z180K18M12DPz1, z180K18M12DPz2,
    z180K18M12DPz3, z180K18M12DPz4, z180K18M12DPz5,
    z180K18M12DPz6, z180K18M12DPz7, z180K18M12DPz8]
  linear_combination
    -d.mass0 + d.mass1 - d.mass2 + d.mass3 - d.mass4 +
      d.mass5 - d.mass6 + d.mass7 - d.mass8

theorem z180_k18_m6_dp_R60
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b) :
    projection36Phi6R0 b =
      2 * (z180K18M12DPW0 b - z180K18M12DPW2 b) := by
  dsimp only [projection36Phi6R0, z180K18M12DPW0,
    z180K18M12DPW2, z180K18M12DPz0, z180K18M12DPz2,
    z180K18M12DPz3, z180K18M12DPz5, z180K18M12DPz6,
    z180K18M12DPz8]
  linear_combination
    -d.mass0 + d.mass2 + d.mass3 - d.mass5 - d.mass6 + d.mass8

theorem z180_k18_m6_dp_R61
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b) :
    projection36Phi6R1 b =
      2 * (z180K18M12DPW1 b + z180K18M12DPW2 b) := by
  dsimp only [projection36Phi6R1, z180K18M12DPW1,
    z180K18M12DPW2, z180K18M12DPz1, z180K18M12DPz2,
    z180K18M12DPz4, z180K18M12DPz5, z180K18M12DPz7,
    z180K18M12DPz8]
  linear_combination
    -d.mass1 - d.mass2 + d.mass4 + d.mass5 - d.mass7 - d.mass8

theorem z180_k18_m6_dp_mul60
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b) :
    2 * (z180K18M12DPW0 b - z180K18M12DPW2 b) = 5 * d.k60 := by
  rw [← z180_k18_m6_dp_R60 b d]
  exact d.mul60

theorem z180_k18_m6_dp_mul61
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b) :
    2 * (z180K18M12DPW1 b + z180K18M12DPW2 b) = 5 * d.k61 := by
  rw [← z180_k18_m6_dp_R61 b d]
  exact d.mul61

theorem z180_k18_m6_dp_aggregate_nonzero
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b) :
    Z180K18M6TwoRemaindersNonzero
      (2 * (z180K18M12DPW0 b - z180K18M12DPW2 b))
      (2 * (z180K18M12DPW1 b + z180K18M12DPW2 b)) := by
  dsimp only [Z180K18M6TwoRemaindersNonzero]
  intro hz
  apply d.nonzero
  constructor
  · rw [z180_k18_m6_dp_R60 b d]
    exact hz.1
  · rw [z180_k18_m6_dp_R61 b d]
    exact hz.2

#print axioms z180_k18_m6_dp_R2
#print axioms z180_k18_m6_dp_R60
#print axioms z180_k18_m6_dp_aggregate_nonzero

end Fuglede
