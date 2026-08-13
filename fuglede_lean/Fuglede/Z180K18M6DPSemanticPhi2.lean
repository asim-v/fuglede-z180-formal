import Fuglede.Z180K18M6DPSemanticIdentities

/-! Semantic leaf for the projected and mod-five `Phi_2` families. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m6_dp_close2
    (b : Fin 36 → Int) (d : Z180K18M6DPBaseData b)
    (hmultiple : ∃ k2 : Int, z180K18ProjectionPhi2R0 b = 5 * k2) :
    False := by
  obtain ⟨eX0, eY0, eX1, eY1, eX2, eY2,
    hX0, hY0, hX1, hY1, hX2, hY2⟩ :=
      z180_k18_m6_dp_aggregates b d
  obtain ⟨hW0lo, hW0hi⟩ :=
    z180_k18_m6_threeFiberBalance_W_bounds _ _ _ hX0
  obtain ⟨hW1lo, hW1hi⟩ :=
    z180_k18_m6_threeFiberBalance_W_bounds _ _ _ hX1
  obtain ⟨hW2lo, hW2hi⟩ :=
    z180_k18_m6_threeFiberBalance_W_bounds _ _ _ hX2
  obtain ⟨k2, hk2⟩ := hmultiple
  have hk2' :
      2 * (z180K18M12DPW0 b - z180K18M12DPW1 b +
        z180K18M12DPW2 b) = 5 * k2 := by
    rw [← z180_k18_m6_dp_R2 b d]
    exact hk2
  exact z180_k18_m6_phi6_phi2_kernel
    (z180K18M12DPW0 b) (-z180K18M12DPW1 b)
    (z180K18M12DPW2 b) k2 d.k60 d.k61
    hW0lo hW0hi (by omega) (by omega) hW2lo hW2hi
    (by simpa only [sub_eq_add_neg] using hk2')
    (z180_k18_m6_dp_mul60 b d)
    (by simpa only [neg_neg] using z180_k18_m6_dp_mul61 b d)
    (by simpa only [neg_neg] using z180_k18_m6_dp_aggregate_nonzero b d)

#print axioms z180_k18_m6_dp_close2

end Fuglede
