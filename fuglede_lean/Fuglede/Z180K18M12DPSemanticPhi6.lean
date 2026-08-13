import Fuglede.Z180K18M12DPSemanticIdentities

/-! Semantic leaf for the projected `Phi_6` family. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_dp_close6
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b)
    (hzero : projection36Phi6R0 b = 0 ∧
      projection36Phi6R1 b = 0) : False := by
  obtain ⟨eX0, eY0, eX1, eY1, eX2, eY2,
    hX0, hY0, hX1, hY1, hX2, hY2⟩ :=
      z180_k18_m12_dp_aggregates b d
  have hW02 : z180K18M12DPW0 b = z180K18M12DPW2 b := by
    have h := hzero.1
    rw [z180_k18_m12_dp_R60 b d] at h
    omega
  have hW12 : z180K18M12DPW1 b = -z180K18M12DPW2 b := by
    have h := hzero.2
    rw [z180_k18_m12_dp_R61 b d] at h
    omega
  have hk120 : z180K18M12DPX0 b - z180K18M12DPX1 b =
      5 * d.k120 := by rw [← z180_k18_m12_dp_R120]; exact d.mul120
  have hk121 : z180K18M12DPY1 b - z180K18M12DPY2 b =
      5 * d.k121 := by rw [← z180_k18_m12_dp_R121]; exact d.mul121
  have hk122 : z180K18M12DPX1 b - z180K18M12DPX2 b =
      5 * d.k122 := by rw [← z180_k18_m12_dp_R122]; exact d.mul122
  have hk123 : -z180K18M12DPY0 b + z180K18M12DPY2 b =
      5 * d.k123 := by rw [← z180_k18_m12_dp_R123]; exact d.mul123
  exact z180_k18_m12_phi12_phi6_kernel
    (z180K18M12DPX0 b) (z180K18M12DPX1 b) (z180K18M12DPX2 b)
    (z180K18M12DPY0 b) (z180K18M12DPY1 b) (z180K18M12DPY2 b)
    (z180K18M12DPW0 b) (z180K18M12DPW1 b) (z180K18M12DPW2 b)
    eX0 eX1 eX2 eY0 eY1 eY2 d.k120 d.k121 d.k122 d.k123
    hX0 hX1 hX2 hY0 hY1 hY2 hW02 hW12
    hk120 hk121 hk122 hk123 (z180_k18_m12_dp_aggregate_nonzero b d)

#print axioms z180_k18_m12_dp_close6

end Fuglede
