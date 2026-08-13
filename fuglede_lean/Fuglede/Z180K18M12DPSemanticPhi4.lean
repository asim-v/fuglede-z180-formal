import Fuglede.Z180K18M12DPSemanticIdentities

/-! Semantic leaf for the projected `Phi_4` / mod-five `Phi_4` families. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_dp_close4
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b)
    (hrem : ∃ k40 k41 : Int,
      z180K18ProjectionPhi4R0 b = 5 * k40 ∧
      z180K18ProjectionPhi4R1 b = 5 * k41) : False := by
  obtain ⟨eX0, eY0, eX1, eY1, eX2, eY2,
    hX0, hY0, hX1, hY1, hX2, hY2⟩ :=
      z180_k18_m12_dp_aggregates b d
  obtain ⟨hX0lo, hX0hi⟩ :=
    z180_k18_m12_threeFiberBalance_X_bounds _ _ _ hX0
  obtain ⟨hX1lo, hX1hi⟩ :=
    z180_k18_m12_threeFiberBalance_X_bounds _ _ _ hX1
  obtain ⟨hX2lo, hX2hi⟩ :=
    z180_k18_m12_threeFiberBalance_X_bounds _ _ _ hX2
  obtain ⟨hY0lo, hY0hi⟩ :=
    z180_k18_m12_threeFiberBalance_X_bounds _ _ _ hY0
  obtain ⟨hY1lo, hY1hi⟩ :=
    z180_k18_m12_threeFiberBalance_X_bounds _ _ _ hY1
  obtain ⟨hY2lo, hY2hi⟩ :=
    z180_k18_m12_threeFiberBalance_X_bounds _ _ _ hY2
  obtain ⟨k40, k41, hk40, hk41⟩ := hrem
  have hk120 : z180K18M12DPX0 b - z180K18M12DPX1 b =
      5 * d.k120 := by
    rw [← z180_k18_m12_dp_R120]
    exact d.mul120
  have hk121 : z180K18M12DPY1 b - z180K18M12DPY2 b =
      5 * d.k121 := by
    rw [← z180_k18_m12_dp_R121]
    exact d.mul121
  have hk122 : z180K18M12DPX1 b - z180K18M12DPX2 b =
      5 * d.k122 := by
    rw [← z180_k18_m12_dp_R122]
    exact d.mul122
  have hk123 : -z180K18M12DPY0 b + z180K18M12DPY2 b =
      5 * d.k123 := by
    rw [← z180_k18_m12_dp_R123]
    exact d.mul123
  have hk40' : z180K18M12DPX0 b + z180K18M12DPX1 b +
      z180K18M12DPX2 b = 5 * k40 := by
    rw [← z180_k18_m12_dp_R40]
    exact hk40
  have hk41' : z180K18M12DPY0 b + z180K18M12DPY1 b +
      z180K18M12DPY2 b = 5 * k41 := by
    rw [← z180_k18_m12_dp_R41]
    exact hk41
  exact z180_k18_m12_phi12_phi4_kernel
    (z180K18M12DPX0 b) (z180K18M12DPX1 b) (z180K18M12DPX2 b)
    (z180K18M12DPY0 b) (z180K18M12DPY1 b) (z180K18M12DPY2 b)
    d.k120 d.k121 d.k122 d.k123 k40 k41
    hX0lo hX0hi hX1lo hX1hi hX2lo hX2hi
    hY0lo hY0hi hY1lo hY1hi hY2lo hY2hi
    hk120 hk121 hk122 hk123 hk40' hk41'
    (z180_k18_m12_dp_aggregate_nonzero b d)

#print axioms z180_k18_m12_dp_close4

end Fuglede
