import Fuglede.Z180K18M12DPSemanticIdentities

/-! Semantic leaf for the projected `Phi_18` family. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_dp_close18
    (b : Fin 36 → Int) (d : Z180K18M12DPBaseData b)
    (hzero :
      Z180K12HighOrder.projection36Phi18R0 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R1 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R2 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R3 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R4 b = 0 ∧
      Z180K12HighOrder.projection36Phi18R5 b = 0) : False := by
  obtain ⟨eX0, eY0, eX1, eY1, eX2, eY2,
    hX0, hY0, hX1, hY1, hX2, hY2⟩ :=
      z180_k18_m12_dp_aggregates b d
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ := hzero
  have hz0b : -1 ≤ z180K18M12DPz0 b ∧ z180K18M12DPz0 b ≤ 1 := by
    simpa [z180K18M12DPz0] using z180_k18_m12_dp_pair_bounds b d 0 18
  have hz1b : -1 ≤ z180K18M12DPz1 b ∧ z180K18M12DPz1 b ≤ 1 := by
    simpa [z180K18M12DPz1] using z180_k18_m12_dp_pair_bounds b d 1 19
  have hz2b : -1 ≤ z180K18M12DPz2 b ∧ z180K18M12DPz2 b ≤ 1 := by
    simpa [z180K18M12DPz2] using z180_k18_m12_dp_pair_bounds b d 2 20
  obtain ⟨hz0lo, hz0hi⟩ := hz0b
  obtain ⟨hz1lo, hz1hi⟩ := hz1b
  obtain ⟨hz2lo, hz2hi⟩ := hz2b
  have hW0 : z180K18M12DPW0 b = 3 * z180K18M12DPz0 b := by
    have hb0lo : 0 ≤ b 0 := d.lo 0
    have hb0hi : b 0 ≤ 1 := d.hi 0
    have hb3lo : 0 ≤ b 3 := d.lo 3
    have hb3hi : b 3 ≤ 1 := d.hi 3
    have hb6lo : 0 ≤ b 6 := d.lo 6
    have hb6hi : b 6 ≤ 1 := d.hi 6
    have hb9lo : 0 ≤ b 9 := d.lo 9
    have hb9hi : b 9 ≤ 1 := d.hi 9
    have hb12lo : 0 ≤ b 12 := d.lo 12
    have hb12hi : b 12 ≤ 1 := d.hi 12
    have hb15lo : 0 ≤ b 15 := d.lo 15
    have hb15hi : b 15 ≤ 1 := d.hi 15
    have hb18lo : 0 ≤ b 18 := d.lo 18
    have hb18hi : b 18 ≤ 1 := d.hi 18
    have hb21lo : 0 ≤ b 21 := d.lo 21
    have hb21hi : b 21 ≤ 1 := d.hi 21
    have hb24lo : 0 ≤ b 24 := d.lo 24
    have hb24hi : b 24 ≤ 1 := d.hi 24
    have hb27lo : 0 ≤ b 27 := d.lo 27
    have hb27hi : b 27 ≤ 1 := d.hi 27
    have hb30lo : 0 ≤ b 30 := d.lo 30
    have hb30hi : b 30 ≤ 1 := d.hi 30
    have hb33lo : 0 ≤ b 33 := d.lo 33
    have hb33hi : b 33 ≤ 1 := d.hi 33
    have hm0 := d.mass0
    have hm3 := d.mass3
    have hm6 := d.mass6
    dsimp only [Z180K12HighOrder.projection36Phi18R0,
      Z180K12HighOrder.projection36Phi18R3,
      z180K18M12DPW0, z180K18M12DPz0,
      z180K18M12DPz3, z180K18M12DPz6] at hr0 hr3 ⊢
    omega
  have hW1 : z180K18M12DPW1 b = 3 * z180K18M12DPz1 b := by
    have hb1lo : 0 ≤ b 1 := d.lo 1
    have hb1hi : b 1 ≤ 1 := d.hi 1
    have hb4lo : 0 ≤ b 4 := d.lo 4
    have hb4hi : b 4 ≤ 1 := d.hi 4
    have hb7lo : 0 ≤ b 7 := d.lo 7
    have hb7hi : b 7 ≤ 1 := d.hi 7
    have hb10lo : 0 ≤ b 10 := d.lo 10
    have hb10hi : b 10 ≤ 1 := d.hi 10
    have hb13lo : 0 ≤ b 13 := d.lo 13
    have hb13hi : b 13 ≤ 1 := d.hi 13
    have hb16lo : 0 ≤ b 16 := d.lo 16
    have hb16hi : b 16 ≤ 1 := d.hi 16
    have hb19lo : 0 ≤ b 19 := d.lo 19
    have hb19hi : b 19 ≤ 1 := d.hi 19
    have hb22lo : 0 ≤ b 22 := d.lo 22
    have hb22hi : b 22 ≤ 1 := d.hi 22
    have hb25lo : 0 ≤ b 25 := d.lo 25
    have hb25hi : b 25 ≤ 1 := d.hi 25
    have hb28lo : 0 ≤ b 28 := d.lo 28
    have hb28hi : b 28 ≤ 1 := d.hi 28
    have hb31lo : 0 ≤ b 31 := d.lo 31
    have hb31hi : b 31 ≤ 1 := d.hi 31
    have hb34lo : 0 ≤ b 34 := d.lo 34
    have hb34hi : b 34 ≤ 1 := d.hi 34
    have hm1 := d.mass1
    have hm4 := d.mass4
    have hm7 := d.mass7
    dsimp only [Z180K12HighOrder.projection36Phi18R1,
      Z180K12HighOrder.projection36Phi18R4,
      z180K18M12DPW1, z180K18M12DPz1,
      z180K18M12DPz4, z180K18M12DPz7] at hr1 hr4 ⊢
    omega
  have hW2 : z180K18M12DPW2 b = 3 * z180K18M12DPz2 b := by
    have hb2lo : 0 ≤ b 2 := d.lo 2
    have hb2hi : b 2 ≤ 1 := d.hi 2
    have hb5lo : 0 ≤ b 5 := d.lo 5
    have hb5hi : b 5 ≤ 1 := d.hi 5
    have hb8lo : 0 ≤ b 8 := d.lo 8
    have hb8hi : b 8 ≤ 1 := d.hi 8
    have hb11lo : 0 ≤ b 11 := d.lo 11
    have hb11hi : b 11 ≤ 1 := d.hi 11
    have hb14lo : 0 ≤ b 14 := d.lo 14
    have hb14hi : b 14 ≤ 1 := d.hi 14
    have hb17lo : 0 ≤ b 17 := d.lo 17
    have hb17hi : b 17 ≤ 1 := d.hi 17
    have hb20lo : 0 ≤ b 20 := d.lo 20
    have hb20hi : b 20 ≤ 1 := d.hi 20
    have hb23lo : 0 ≤ b 23 := d.lo 23
    have hb23hi : b 23 ≤ 1 := d.hi 23
    have hb26lo : 0 ≤ b 26 := d.lo 26
    have hb26hi : b 26 ≤ 1 := d.hi 26
    have hb29lo : 0 ≤ b 29 := d.lo 29
    have hb29hi : b 29 ≤ 1 := d.hi 29
    have hb32lo : 0 ≤ b 32 := d.lo 32
    have hb32hi : b 32 ≤ 1 := d.hi 32
    have hb35lo : 0 ≤ b 35 := d.lo 35
    have hb35hi : b 35 ≤ 1 := d.hi 35
    have hm2 := d.mass2
    have hm5 := d.mass5
    have hm8 := d.mass8
    dsimp only [Z180K12HighOrder.projection36Phi18R2,
      Z180K12HighOrder.projection36Phi18R5,
      z180K18M12DPW2, z180K18M12DPz2,
      z180K18M12DPz5, z180K18M12DPz8] at hr2 hr5 ⊢
    omega
  have hk120 : z180K18M12DPX0 b - z180K18M12DPX1 b =
      5 * d.k120 := by rw [← z180_k18_m12_dp_R120]; exact d.mul120
  have hk121 : z180K18M12DPY1 b - z180K18M12DPY2 b =
      5 * d.k121 := by rw [← z180_k18_m12_dp_R121]; exact d.mul121
  have hk122 : z180K18M12DPX1 b - z180K18M12DPX2 b =
      5 * d.k122 := by rw [← z180_k18_m12_dp_R122]; exact d.mul122
  have hk123 : -z180K18M12DPY0 b + z180K18M12DPY2 b =
      5 * d.k123 := by rw [← z180_k18_m12_dp_R123]; exact d.mul123
  exact z180_k18_m12_phi12_phi18_kernel
    (z180K18M12DPX0 b) (z180K18M12DPX1 b) (z180K18M12DPX2 b)
    (z180K18M12DPY0 b) (z180K18M12DPY1 b) (z180K18M12DPY2 b)
    (z180K18M12DPW0 b) (z180K18M12DPW1 b) (z180K18M12DPW2 b)
    eX0 eX1 eX2 eY0 eY1 eY2
    (z180K18M12DPz0 b) (z180K18M12DPz1 b) (z180K18M12DPz2 b)
    d.k120 d.k121 d.k122 d.k123
    hX0 hX1 hX2 hY0 hY1 hY2
    hz0lo hz0hi hz1lo hz1hi hz2lo hz2hi hW0 hW1 hW2
    hk120 hk121 hk122 hk123 (z180_k18_m12_dp_aggregate_nonzero b d)

#print axioms z180_k18_m12_dp_close18

end Fuglede
