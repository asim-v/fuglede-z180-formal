import Fuglede.Z180K18M6DPSemanticIdentities

/-! Semantic leaf for the projected and mod-five `Phi_12` families. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m6_dp_close12
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b)
    (hmultiple : ∃ k120 k121 k122 k123 : Int,
      Z180K12HighOrder.projection36Phi12R0 b = 5 * k120 ∧
      Z180K12HighOrder.projection36Phi12R1 b = 5 * k121 ∧
      Z180K12HighOrder.projection36Phi12R2 b = 5 * k122 ∧
      Z180K12HighOrder.projection36Phi12R3 b = 5 * k123) : False := by
  obtain ⟨eX0, eY0, eX1, eY1, eX2, eY2,
    hX0, hY0, hX1, hY1, hX2, hY2⟩ :=
      z180_k18_m6_dp_aggregates b d
  obtain ⟨k120, k121, k122, k123, hk120, hk121, hk122, hk123⟩ :=
    hmultiple
  have hk120' : z180K18M12DPX0 b - z180K18M12DPX1 b =
      5 * k120 := by rw [← z180_k18_m12_dp_R120]; exact hk120
  have hk121' : z180K18M12DPY1 b - z180K18M12DPY2 b =
      5 * k121 := by rw [← z180_k18_m12_dp_R121]; exact hk121
  have hk122' : z180K18M12DPX1 b - z180K18M12DPX2 b =
      5 * k122 := by rw [← z180_k18_m12_dp_R122]; exact hk122
  have hk123' : -z180K18M12DPY0 b + z180K18M12DPY2 b =
      5 * k123 := by rw [← z180_k18_m12_dp_R123]; exact hk123
  exact z180_k18_m6_phi6_phi12_kernel
    (z180K18M12DPX0 b) (z180K18M12DPX1 b) (z180K18M12DPX2 b)
    (z180K18M12DPY0 b) (z180K18M12DPY1 b) (z180K18M12DPY2 b)
    (z180K18M12DPW0 b) (z180K18M12DPW1 b) (z180K18M12DPW2 b)
    eX0 eX1 eX2 eY0 eY1 eY2
    k120 k121 k122 k123 d.k60 d.k61
    hX0 hX1 hX2 hY0 hY1 hY2
    hk120' hk121' hk122' hk123'
    (z180_k18_m6_dp_mul60 b d) (z180_k18_m6_dp_mul61 b d)
    (z180_k18_m6_dp_aggregate_nonzero b d)

#print axioms z180_k18_m6_dp_close12

end Fuglede
