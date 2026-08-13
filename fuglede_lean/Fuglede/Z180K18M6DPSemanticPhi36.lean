import Fuglede.Z180K18M6DPSemanticIdentities

/-! Semantic leaf for the projected `Phi_36` family. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m6_dp_close36
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b)
    (hzero :
      Z180K12HighOrder.projection36Phi36R0 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R1 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R2 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R3 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R4 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R5 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R6 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R7 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R8 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R9 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R10 b = 0 ∧
      Z180K12HighOrder.projection36Phi36R11 b = 0) : False := by
  obtain ⟨eX0, eY0, eX1, eY1, eX2, eY2,
    hX0, hY0, hX1, hY1, hX2, hY2⟩ :=
      z180_k18_m6_dp_aggregates b d
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5,
    hr6, hr7, hr8, hr9, hr10, hr11⟩ := hzero
  have hx03 : z180K18M12DPx0 b = z180K18M12DPx3 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R0,
      z180K18M12DPx0, z180K18M12DPx3] at hr0 ⊢
    omega
  have hx36 : z180K18M12DPx3 b = z180K18M12DPx6 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R6,
      z180K18M12DPx3, z180K18M12DPx6] at hr6 ⊢
    omega
  have hx17 : z180K18M12DPx1 b = z180K18M12DPx7 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R10,
      z180K18M12DPx1, z180K18M12DPx7] at hr10 ⊢
    omega
  have hx47 : z180K18M12DPx4 b = z180K18M12DPx7 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R4,
      z180K18M12DPx4, z180K18M12DPx7] at hr4 ⊢
    omega
  have hx25 : z180K18M12DPx2 b = z180K18M12DPx5 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R2,
      z180K18M12DPx2, z180K18M12DPx5] at hr2 ⊢
    omega
  have hx58 : z180K18M12DPx5 b = z180K18M12DPx8 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R8,
      z180K18M12DPx5, z180K18M12DPx8] at hr8 ⊢
    omega
  have hX0triple : z180K18M12DPX0 b = 3 * z180K18M12DPx0 b := by
    dsimp only [z180K18M12DPX0]
    omega
  have hX1triple : z180K18M12DPX1 b = 3 * z180K18M12DPx1 b := by
    dsimp only [z180K18M12DPX1]
    omega
  have hX2triple : z180K18M12DPX2 b = 3 * z180K18M12DPx2 b := by
    dsimp only [z180K18M12DPX2]
    omega
  exact z180_k18_m6_phi6_phi36_kernel
    (z180K18M12DPX0 b) (z180K18M12DPX1 b) (z180K18M12DPX2 b)
    (z180K18M12DPW0 b) (z180K18M12DPW1 b) (z180K18M12DPW2 b)
    (z180K18M12DPx0 b) (z180K18M12DPx1 b) (z180K18M12DPx2 b)
    eX0 eX1 eX2 d.k60 d.k61 hX0 hX1 hX2
    hX0triple hX1triple hX2triple
    (z180_k18_m6_dp_mul60 b d) (z180_k18_m6_dp_mul61 b d)
    (z180_k18_m6_dp_aggregate_nonzero b d)

#print axioms z180_k18_m6_dp_close36

end Fuglede
