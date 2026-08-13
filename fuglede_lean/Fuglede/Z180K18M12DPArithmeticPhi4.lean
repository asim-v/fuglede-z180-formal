import Fuglede.Z180K18M12DPArithmeticDefs

/-! Presburger leaf for the canonical `(12,4)` family. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_phi12_phi4_kernel
    (X0 X1 X2 Y0 Y1 Y2 : Int)
    (k120 k121 k122 k123 k40 k41 : Int)
    (hX0lo : -3 ≤ X0) (hX0hi : X0 ≤ 3)
    (hX1lo : -3 ≤ X1) (hX1hi : X1 ≤ 3)
    (hX2lo : -3 ≤ X2) (hX2hi : X2 ≤ 3)
    (hY0lo : -3 ≤ Y0) (hY0hi : Y0 ≤ 3)
    (hY1lo : -3 ≤ Y1) (hY1hi : Y1 ≤ 3)
    (hY2lo : -3 ≤ Y2) (hY2hi : Y2 ≤ 3)
    (h120 : X0 - X1 = 5 * k120)
    (h121 : Y1 - Y2 = 5 * k121)
    (h122 : X1 - X2 = 5 * k122)
    (h123 : -Y0 + Y2 = 5 * k123)
    (h40 : X0 + X1 + X2 = 5 * k40)
    (h41 : Y0 + Y1 + Y2 = 5 * k41)
    (hne : Z180K18M12FourRemaindersNonzero
      (X0 - X1) (Y1 - Y2) (X1 - X2) (-Y0 + Y2)) :
    False := by
  dsimp only [Z180K18M12FourRemaindersNonzero] at hne
  omega

#print axioms z180_k18_m12_phi12_phi4_kernel

end Fuglede
