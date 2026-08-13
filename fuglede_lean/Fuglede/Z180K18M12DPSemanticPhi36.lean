import Fuglede.Z180K18M12DPSemanticIdentities

/-! Semantic leaf for the projected and mod-five `Phi_36` families. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_dp_close36
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b)
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
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5,
    hr6, hr7, hr8, hr9, hr10, hr11⟩ := hzero
  have hx0b : -1 ≤ z180K18M12DPx0 b ∧ z180K18M12DPx0 b ≤ 1 := by
    simpa [z180K18M12DPx0] using z180_k18_m12_dp_diff_bounds b d 0 18
  have hx1b : -1 ≤ z180K18M12DPx1 b ∧ z180K18M12DPx1 b ≤ 1 := by
    simpa [z180K18M12DPx1] using z180_k18_m12_dp_diff_bounds b d 28 10
  have hx2b : -1 ≤ z180K18M12DPx2 b ∧ z180K18M12DPx2 b ≤ 1 := by
    simpa [z180K18M12DPx2] using z180_k18_m12_dp_diff_bounds b d 20 2
  have hy0b : -1 ≤ z180K18M12DPy0 b ∧ z180K18M12DPy0 b ≤ 1 := by
    simpa [z180K18M12DPy0] using z180_k18_m12_dp_diff_bounds b d 9 27
  have hy1b : -1 ≤ z180K18M12DPy1 b ∧ z180K18M12DPy1 b ≤ 1 := by
    simpa [z180K18M12DPy1] using z180_k18_m12_dp_diff_bounds b d 1 19
  have hy2b : -1 ≤ z180K18M12DPy2 b ∧ z180K18M12DPy2 b ≤ 1 := by
    simpa [z180K18M12DPy2] using z180_k18_m12_dp_diff_bounds b d 29 11
  obtain ⟨hx0lo, hx0hi⟩ := hx0b
  obtain ⟨hx1lo, hx1hi⟩ := hx1b
  obtain ⟨hx2lo, hx2hi⟩ := hx2b
  obtain ⟨hy0lo, hy0hi⟩ := hy0b
  obtain ⟨hy1lo, hy1hi⟩ := hy1b
  obtain ⟨hy2lo, hy2hi⟩ := hy2b
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
  have hy14 : z180K18M12DPy1 b = z180K18M12DPy4 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R1,
      z180K18M12DPy1, z180K18M12DPy4] at hr1 ⊢
    omega
  have hy47 : z180K18M12DPy4 b = z180K18M12DPy7 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R7,
      z180K18M12DPy4, z180K18M12DPy7] at hr7 ⊢
    omega
  have hy36 : z180K18M12DPy3 b = z180K18M12DPy6 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R3,
      z180K18M12DPy3, z180K18M12DPy6] at hr3 ⊢
    omega
  have hy06 : z180K18M12DPy0 b = z180K18M12DPy6 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R9,
      z180K18M12DPy0, z180K18M12DPy6] at hr9 ⊢
    omega
  have hy58 : z180K18M12DPy5 b = z180K18M12DPy8 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R5,
      z180K18M12DPy5, z180K18M12DPy8] at hr5 ⊢
    omega
  have hy28 : z180K18M12DPy2 b = z180K18M12DPy8 b := by
    dsimp only [Z180K12HighOrder.projection36Phi36R11,
      z180K18M12DPy2, z180K18M12DPy8] at hr11 ⊢
    omega
  have h120triple :
      z180K18M12DPX0 b - z180K18M12DPX1 b =
        3 * (z180K18M12DPx0 b - z180K18M12DPx1 b) := by
    dsimp only [z180K18M12DPX0, z180K18M12DPX1]
    omega
  have h121triple :
      z180K18M12DPY1 b - z180K18M12DPY2 b =
        3 * (z180K18M12DPy1 b - z180K18M12DPy2 b) := by
    dsimp only [z180K18M12DPY1, z180K18M12DPY2]
    omega
  have h122triple :
      z180K18M12DPX1 b - z180K18M12DPX2 b =
        3 * (z180K18M12DPx1 b - z180K18M12DPx2 b) := by
    dsimp only [z180K18M12DPX1, z180K18M12DPX2]
    omega
  have h123triple :
      -z180K18M12DPY0 b + z180K18M12DPY2 b =
        3 * (-z180K18M12DPy0 b + z180K18M12DPy2 b) := by
    dsimp only [z180K18M12DPY0, z180K18M12DPY2]
    omega
  have hk120 : 3 * (z180K18M12DPx0 b - z180K18M12DPx1 b) =
      5 * d.k120 := by rw [← h120triple, ← z180_k18_m12_dp_R120]; exact d.mul120
  have hk121 : 3 * (z180K18M12DPy1 b - z180K18M12DPy2 b) =
      5 * d.k121 := by rw [← h121triple, ← z180_k18_m12_dp_R121]; exact d.mul121
  have hk122 : 3 * (z180K18M12DPx1 b - z180K18M12DPx2 b) =
      5 * d.k122 := by rw [← h122triple, ← z180_k18_m12_dp_R122]; exact d.mul122
  have hk123 : 3 * (-z180K18M12DPy0 b + z180K18M12DPy2 b) =
      5 * d.k123 := by rw [← h123triple, ← z180_k18_m12_dp_R123]; exact d.mul123
  have hne : Z180K18M12FourRemaindersNonzero
      (3 * (z180K18M12DPx0 b - z180K18M12DPx1 b))
      (3 * (z180K18M12DPy1 b - z180K18M12DPy2 b))
      (3 * (z180K18M12DPx1 b - z180K18M12DPx2 b))
      (3 * (-z180K18M12DPy0 b + z180K18M12DPy2 b)) := by
    dsimp only [Z180K18M12FourRemaindersNonzero]
    intro hz
    apply z180_k18_m12_dp_aggregate_nonzero b d
    exact ⟨by rw [h120triple]; exact hz.1,
      by rw [h121triple]; exact hz.2.1,
      by rw [h122triple]; exact hz.2.2.1,
      by rw [h123triple]; exact hz.2.2.2⟩
  exact z180_k18_m12_phi12_phi36_kernel
    (z180K18M12DPx0 b) (z180K18M12DPx1 b) (z180K18M12DPx2 b)
    (z180K18M12DPy0 b) (z180K18M12DPy1 b) (z180K18M12DPy2 b)
    d.k120 d.k121 d.k122 d.k123
    hx0lo hx0hi hx1lo hx1hi hx2lo hx2hi
    hy0lo hy0hi hy1lo hy1hi hy2lo hy2hi
    hk120 hk121 hk122 hk123 hne

#print axioms z180_k18_m12_dp_close36

end Fuglede
