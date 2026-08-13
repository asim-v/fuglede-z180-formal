import Fuglede.Z180K18M12DPArithmeticSharded
import Mathlib.Tactic

/-!
# Presburger kernels for the residual `k = 18`, `m = 6` families

The four theorems below are the algebraic endpoints of the canonical
`(6,2)`, `(6,12)`, `(6,18)`, and `(6,36)` paired-remainder audits.  They
use only bounded integral arithmetic; the set-to-remainder bridge is kept in
the semantic module.
-/

namespace Fuglede

set_option maxHeartbeats 0

/-- Nonvanishing spelling for the two primitive-six remainder coordinates. -/
def Z180K18M6TwoRemaindersNonzero (r0 r1 : Int) : Prop :=
  ¬ (r0 = 0 ∧ r1 = 0)

/-- Algebraic replacement for the 343-state canonical `(6,2)` family. -/
theorem z180_k18_m6_phi6_phi2_kernel
    (a b c k2 k60 k61 : Int)
    (haLo : -3 ≤ a) (haHi : a ≤ 3)
    (hbLo : -3 ≤ b) (hbHi : b ≤ 3)
    (hcLo : -3 ≤ c) (hcHi : c ≤ 3)
    (h2 : 2 * (a + b + c) = 5 * k2)
    (h60 : 2 * (a - c) = 5 * k60)
    (h61 : 2 * (-b + c) = 5 * k61)
    (hne : Z180K18M6TwoRemaindersNonzero
      (2 * (a - c)) (2 * (-b + c))) :
    False := by
  dsimp only [Z180K18M6TwoRemaindersNonzero] at hne
  omega

/-- Algebraic replacement for the canonical `(6,12)` family. -/
theorem z180_k18_m6_phi6_phi12_kernel
    (X0 X1 X2 Y0 Y1 Y2 W0 W1 W2 : Int)
    (eX0 eX1 eX2 eY0 eY1 eY2 : Int)
    (k120 k121 k122 k123 k60 k61 : Int)
    (hX0 : Z180K18M12ThreeFiberBalance X0 W0 eX0)
    (hX1 : Z180K18M12ThreeFiberBalance X1 W1 eX1)
    (hX2 : Z180K18M12ThreeFiberBalance X2 W2 eX2)
    (hY0 : Z180K18M12ThreeFiberBalance Y0 W0 eY0)
    (hY1 : Z180K18M12ThreeFiberBalance Y1 W1 eY1)
    (hY2 : Z180K18M12ThreeFiberBalance Y2 W2 eY2)
    (h120 : X0 - X1 = 5 * k120)
    (h121 : Y1 - Y2 = 5 * k121)
    (h122 : X1 - X2 = 5 * k122)
    (h123 : -Y0 + Y2 = 5 * k123)
    (h60 : 2 * (W0 - W2) = 5 * k60)
    (h61 : 2 * (W1 + W2) = 5 * k61)
    (hne : Z180K18M6TwoRemaindersNonzero
      (2 * (W0 - W2)) (2 * (W1 + W2))) :
    False := by
  dsimp only [Z180K18M12ThreeFiberBalance,
    Z180K18M6TwoRemaindersNonzero] at hX0 hX1 hX2 hY0 hY1 hY2 hne
  omega

/-- After the six `Phi_18` equations identify the three triples, the
canonical `(6,18)` family has this three-variable endpoint. -/
theorem z180_k18_m6_phi6_phi18_kernel
    (t0 t1 t2 k60 k61 : Int)
    (ht0lo : -1 ≤ t0) (ht0hi : t0 ≤ 1)
    (ht1lo : -1 ≤ t1) (ht1hi : t1 ≤ 1)
    (ht2lo : -1 ≤ t2) (ht2hi : t2 ≤ 1)
    (h60 : 6 * (t0 - t2) = 5 * k60)
    (h61 : 6 * (-t1 + t2) = 5 * k61)
    (hne : Z180K18M6TwoRemaindersNonzero
      (6 * (t0 - t2)) (6 * (-t1 + t2))) :
    False := by
  dsimp only [Z180K18M6TwoRemaindersNonzero] at hne
  omega

/-- Once the twelve `Phi_36` equations identify each local triple, every
aggregate balance coordinate is three times an integer.  This excludes a
nonzero primitive-six remainder divisible by five. -/
theorem z180_k18_m6_phi6_phi36_kernel
    (X0 X1 X2 W0 W1 W2 x0 x1 x2 : Int)
    (eX0 eX1 eX2 k60 k61 : Int)
    (hX0 : Z180K18M12ThreeFiberBalance X0 W0 eX0)
    (hX1 : Z180K18M12ThreeFiberBalance X1 W1 eX1)
    (hX2 : Z180K18M12ThreeFiberBalance X2 W2 eX2)
    (hX0triple : X0 = 3 * x0)
    (hX1triple : X1 = 3 * x1)
    (hX2triple : X2 = 3 * x2)
    (h60 : 2 * (W0 - W2) = 5 * k60)
    (h61 : 2 * (W1 + W2) = 5 * k61)
    (hne : Z180K18M6TwoRemaindersNonzero
      (2 * (W0 - W2)) (2 * (W1 + W2))) :
    False := by
  dsimp only [Z180K18M12ThreeFiberBalance,
    Z180K18M6TwoRemaindersNonzero] at hX0 hX1 hX2 hne
  have hX0lo : -3 ≤ X0 := by omega
  have hX0hi : X0 ≤ 3 := by omega
  have hX1lo : -3 ≤ X1 := by omega
  have hX1hi : X1 ≤ 3 := by omega
  have hX2lo : -3 ≤ X2 := by omega
  have hX2hi : X2 ≤ 3 := by omega
  have hx0lo : -1 ≤ x0 := by omega
  have hx0hi : x0 ≤ 1 := by omega
  have hx1lo : -1 ≤ x1 := by omega
  have hx1hi : x1 ≤ 1 := by omega
  have hx2lo : -1 ≤ x2 := by omega
  have hx2hi : x2 ≤ 1 := by omega
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> omega

#print axioms z180_k18_m6_phi6_phi2_kernel
#print axioms z180_k18_m6_phi6_phi12_kernel
#print axioms z180_k18_m6_phi6_phi18_kernel
#print axioms z180_k18_m6_phi6_phi36_kernel

end Fuglede
