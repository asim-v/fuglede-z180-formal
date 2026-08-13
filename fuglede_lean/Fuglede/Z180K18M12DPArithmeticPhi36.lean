import Fuglede.Z180K18M12DPArithmeticDefs

/-! Presburger leaf for the canonical `(12,36)` family. -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_k18_m12_phi12_phi36_kernel
    (x0 x1 x2 y0 y1 y2 : Int)
    (k120 k121 k122 k123 : Int)
    (hx0lo : -1 ≤ x0) (hx0hi : x0 ≤ 1)
    (hx1lo : -1 ≤ x1) (hx1hi : x1 ≤ 1)
    (hx2lo : -1 ≤ x2) (hx2hi : x2 ≤ 1)
    (hy0lo : -1 ≤ y0) (hy0hi : y0 ≤ 1)
    (hy1lo : -1 ≤ y1) (hy1hi : y1 ≤ 1)
    (hy2lo : -1 ≤ y2) (hy2hi : y2 ≤ 1)
    (h120 : 3 * (x0 - x1) = 5 * k120)
    (h121 : 3 * (y1 - y2) = 5 * k121)
    (h122 : 3 * (x1 - x2) = 5 * k122)
    (h123 : 3 * (-y0 + y2) = 5 * k123)
    (hne : Z180K18M12FourRemaindersNonzero
      (3 * (x0 - x1)) (3 * (y1 - y2))
      (3 * (x1 - x2)) (3 * (-y0 + y2))) :
    False := by
  dsimp only [Z180K18M12FourRemaindersNonzero] at hne
  omega

#print axioms z180_k18_m12_phi12_phi36_kernel

end Fuglede
