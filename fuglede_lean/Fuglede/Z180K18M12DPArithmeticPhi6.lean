import Fuglede.Z180K18M12DPArithmeticDefs

/-! Presburger leaf for the canonical `(12,6)` family. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_phi12_phi6_kernel
    (X0 X1 X2 Y0 Y1 Y2 W0 W1 W2 : Int)
    (eX0 eX1 eX2 eY0 eY1 eY2 : Int)
    (k120 k121 k122 k123 : Int)
    (hX0 : Z180K18M12ThreeFiberBalance X0 W0 eX0)
    (hX1 : Z180K18M12ThreeFiberBalance X1 W1 eX1)
    (hX2 : Z180K18M12ThreeFiberBalance X2 W2 eX2)
    (hY0 : Z180K18M12ThreeFiberBalance Y0 W0 eY0)
    (hY1 : Z180K18M12ThreeFiberBalance Y1 W1 eY1)
    (hY2 : Z180K18M12ThreeFiberBalance Y2 W2 eY2)
    (hW02 : W0 = W2) (hW12 : W1 = -W2)
    (h120 : X0 - X1 = 5 * k120)
    (h121 : Y1 - Y2 = 5 * k121)
    (h122 : X1 - X2 = 5 * k122)
    (h123 : -Y0 + Y2 = 5 * k123)
    (hne : Z180K18M12FourRemaindersNonzero
      (X0 - X1) (Y1 - Y2) (X1 - X2) (-Y0 + Y2)) :
    False := by
  dsimp only [Z180K18M12ThreeFiberBalance,
    Z180K18M12FourRemaindersNonzero] at hX0 hX1 hX2 hY0 hY1 hY2 hne
  omega

#print axioms z180_k18_m12_phi12_phi6_kernel

end Fuglede
