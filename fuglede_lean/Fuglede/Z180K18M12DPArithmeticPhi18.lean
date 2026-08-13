import Fuglede.Z180K18M12DPArithmeticPhi18Pair

/-! Presburger leaf for the canonical `(12,18)` family. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_phi12_phi18_kernel
    (X0 X1 X2 Y0 Y1 Y2 W0 W1 W2 : Int)
    (eX0 eX1 eX2 eY0 eY1 eY2 z0 z1 z2 : Int)
    (k120 k121 k122 k123 : Int)
    (hX0 : Z180K18M12ThreeFiberBalance X0 W0 eX0)
    (hX1 : Z180K18M12ThreeFiberBalance X1 W1 eX1)
    (hX2 : Z180K18M12ThreeFiberBalance X2 W2 eX2)
    (hY0 : Z180K18M12ThreeFiberBalance Y0 W0 eY0)
    (hY1 : Z180K18M12ThreeFiberBalance Y1 W1 eY1)
    (hY2 : Z180K18M12ThreeFiberBalance Y2 W2 eY2)
    (hz0lo : -1 ≤ z0) (hz0hi : z0 ≤ 1)
    (hz1lo : -1 ≤ z1) (hz1hi : z1 ≤ 1)
    (hz2lo : -1 ≤ z2) (hz2hi : z2 ≤ 1)
    (hW0 : W0 = 3 * z0) (hW1 : W1 = 3 * z1) (hW2 : W2 = 3 * z2)
    (h120 : X0 - X1 = 5 * k120)
    (h121 : Y1 - Y2 = 5 * k121)
    (h122 : X1 - X2 = 5 * k122)
    (h123 : -Y0 + Y2 = 5 * k123)
    (hne : Z180K18M12FourRemaindersNonzero
      (X0 - X1) (Y1 - Y2) (X1 - X2) (-Y0 + Y2)) :
    False := by
  have hz120 := z180_k18_m12_balanced_pair_diff_zero_of_five_mul
    X0 X1 W0 W1 eX0 eX1 z0 z1 k120
    hX0 hX1 hz0lo hz0hi hz1lo hz1hi hW0 hW1 h120
  have hz121 := z180_k18_m12_balanced_pair_diff_zero_of_five_mul
    Y1 Y2 W1 W2 eY1 eY2 z1 z2 k121
    hY1 hY2 hz1lo hz1hi hz2lo hz2hi hW1 hW2 h121
  have hz122 := z180_k18_m12_balanced_pair_diff_zero_of_five_mul
    X1 X2 W1 W2 eX1 eX2 z1 z2 k122
    hX1 hX2 hz1lo hz1hi hz2lo hz2hi hW1 hW2 h122
  have h123' : Y2 - Y0 = 5 * k123 := by
    simpa only [sub_eq_add_neg, add_comm] using h123
  have hz123 := z180_k18_m12_balanced_pair_diff_zero_of_five_mul
    Y2 Y0 W2 W0 eY2 eY0 z2 z0 k123
    hY2 hY0 hz2lo hz2hi hz0lo hz0hi hW2 hW0 h123'
  dsimp only [Z180K18M12FourRemaindersNonzero] at hne
  apply hne
  exact ⟨hz120, hz121, hz122,
    by simpa only [sub_eq_add_neg, add_comm] using hz123⟩

#print axioms z180_k18_m12_phi12_phi18_kernel

end Fuglede
