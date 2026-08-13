import Fuglede.Z180K18M6DPSemanticIdentities

/-! Semantic leaf for the projected and mod-five `Phi_18` families. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m6_dp_close18
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b)
    (hzero :
      Z180K12HighOrder.projection36Phi18R0 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R1 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R2 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R3 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R4 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R5 b = 0) : False := by
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ := hzero
  have hz0b : -1 ≤ z180K18M12DPz0 b ∧ z180K18M12DPz0 b ≤ 1 := by
    simpa [z180K18M12DPz0] using z180_k18_m6_dp_pair_bounds b d 0 18
  have hz1b : -1 ≤ z180K18M12DPz1 b ∧ z180K18M12DPz1 b ≤ 1 := by
    simpa [z180K18M12DPz1] using z180_k18_m6_dp_pair_bounds b d 1 19
  have hz2b : -1 ≤ z180K18M12DPz2 b ∧ z180K18M12DPz2 b ≤ 1 := by
    simpa [z180K18M12DPz2] using z180_k18_m6_dp_pair_bounds b d 2 20
  obtain ⟨hz0lo, hz0hi⟩ := hz0b
  obtain ⟨hz1lo, hz1hi⟩ := hz1b
  obtain ⟨hz2lo, hz2hi⟩ := hz2b
  have hW0twice :
      2 * z180K18M12DPW0 b = 6 * z180K18M12DPz0 b := by
    dsimp only [Z180K12HighOrder.projection36Phi18R0,
      Z180K12HighOrder.projection36Phi18R3,
      z180K18M12DPW0, z180K18M12DPz0,
      z180K18M12DPz3, z180K18M12DPz6] at hr0 hr3 ⊢
    linear_combination
      -2 * hr0 - hr3 - 2 * d.mass0 - d.mass3 + d.mass6
  have hW0 : z180K18M12DPW0 b = 3 * z180K18M12DPz0 b := by
    omega
  have hW1twice :
      2 * z180K18M12DPW1 b = 6 * z180K18M12DPz1 b := by
    dsimp only [Z180K12HighOrder.projection36Phi18R1,
      Z180K12HighOrder.projection36Phi18R4,
      z180K18M12DPW1, z180K18M12DPz1,
      z180K18M12DPz4, z180K18M12DPz7] at hr1 hr4 ⊢
    linear_combination
      -2 * hr1 - hr4 - 2 * d.mass1 - d.mass4 + d.mass7
  have hW1 : z180K18M12DPW1 b = 3 * z180K18M12DPz1 b := by
    omega
  have hW2twice :
      2 * z180K18M12DPW2 b = 6 * z180K18M12DPz2 b := by
    dsimp only [Z180K12HighOrder.projection36Phi18R2,
      Z180K12HighOrder.projection36Phi18R5,
      z180K18M12DPW2, z180K18M12DPz2,
      z180K18M12DPz5, z180K18M12DPz8] at hr2 hr5 ⊢
    linear_combination
      -2 * hr2 - hr5 - 2 * d.mass2 - d.mass5 + d.mass8
  have hW2 : z180K18M12DPW2 b = 3 * z180K18M12DPz2 b := by
    omega
  have hk60 :
      6 * (z180K18M12DPz0 b - z180K18M12DPz2 b) = 5 * d.k60 := by
    have h := z180_k18_m6_dp_mul60 b d
    omega
  have hk61 :
      6 * (z180K18M12DPz1 b + z180K18M12DPz2 b) = 5 * d.k61 := by
    have h := z180_k18_m6_dp_mul61 b d
    omega
  have hne : Z180K18M6TwoRemaindersNonzero
      (6 * (z180K18M12DPz0 b - z180K18M12DPz2 b))
      (6 * (z180K18M12DPz1 b + z180K18M12DPz2 b)) := by
    have h := z180_k18_m6_dp_aggregate_nonzero b d
    dsimp only [Z180K18M6TwoRemaindersNonzero] at h ⊢
    omega
  exact z180_k18_m6_phi6_phi18_kernel
    (z180K18M12DPz0 b) (-z180K18M12DPz1 b)
    (z180K18M12DPz2 b) d.k60 d.k61
    hz0lo hz0hi (by omega) (by omega) hz2lo hz2hi
    hk60 (by simpa only [neg_neg] using hk61)
    (by simpa only [neg_neg] using hne)

#print axioms z180_k18_m6_dp_close18

end Fuglede
