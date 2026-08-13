import Mathlib.Tactic

/-!
# Small Presburger kernels for the residual `m = 12` envelope DPs

These statements contain only bounded integer arithmetic.  They replace the
four canonical packed DP families `(12,4)`, `(12,6)`, `(12,18)`, and
`(12,36)` after the set-side projection has produced the displayed data.
-/

namespace Fuglede

set_option maxHeartbeats 0

/-- Common nonvanishing spelling for the four `Phi_12` coordinates. -/
def Z180K18M12FourRemaindersNonzero
    (r0 r1 r2 r3 : Int) : Prop :=
  ¬ (r0 = 0 ∧ r1 = 0 ∧ r2 = 0 ∧ r3 = 0)

/-- Algebraic replacement for the canonical `(12,4)` packed DP. -/
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

/-- Shared aggregate constraints for one three-fibre block.  The four
inequalities say `abs X + abs W <= 3`; the last equality says `X+W` is odd. -/
def Z180K18M12ThreeFiberBalance
    (X W parityWitness : Int) : Prop :=
  X + W ≤ 3 ∧ X - W ≤ 3 ∧
    -X + W ≤ 3 ∧ -X - W ≤ 3 ∧
    X + W = 1 + 2 * parityWitness

/-- One-fibre form underlying the aggregate constraint. -/
def Z180K18M12OneFiberBalance
    (x z parityWitness : Int) : Prop :=
  x + z ≤ 1 ∧ x - z ≤ 1 ∧
    -x + z ≤ 1 ∧ -x - z ≤ 1 ∧
    x + z = 1 + 2 * parityWitness

/-- A zero-one pair, oriented from its first entry to its second, gives one
of the four possible local balance states. -/
theorem z180_k18_m12_oneFiberBalance_left
    (a c : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Z180K18M12OneFiberBalance (a - c) (a + c - 1) (a - 1) := by
  dsimp only [Z180K18M12OneFiberBalance]
  omega

/-- The reverse orientation of `z180_k18_m12_oneFiberBalance_left`. -/
theorem z180_k18_m12_oneFiberBalance_right
    (a c : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Z180K18M12OneFiberBalance (c - a) (a + c - 1) (c - 1) := by
  dsimp only [Z180K18M12OneFiberBalance]
  omega

/-- In a zero-one four-fibre of mass two, the complementary pair has the
same balance coordinate, with the first orientation. -/
theorem z180_k18_m12_oneFiberBalance_complement_left
    (a b c d : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hmass : a + b + c + d = 2) :
    Z180K18M12OneFiberBalance
      (b - d) (a + c - 1) (a + b + c - 2) := by
  dsimp only [Z180K18M12OneFiberBalance]
  omega

/-- Reverse orientation of the complementary pair in a mass-two fibre. -/
theorem z180_k18_m12_oneFiberBalance_complement_right
    (a b c d : Int)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hmass : a + b + c + d = 2) :
    Z180K18M12OneFiberBalance (d - b) (a + c - 1) (-b) := by
  dsimp only [Z180K18M12OneFiberBalance]
  omega

/-- Three one-fibre constraints add to the signed aggregate used by the
order-six and order-eighteen kernels. -/
theorem z180_k18_m12_threeFiberBalance_of_oneFiber
    (x0 x1 x2 z0 z1 z2 e0 e1 e2 : Int)
    (h0 : Z180K18M12OneFiberBalance x0 z0 e0)
    (h1 : Z180K18M12OneFiberBalance x1 z1 e1)
    (h2 : Z180K18M12OneFiberBalance x2 z2 e2) :
    ∃ e : Int, Z180K18M12ThreeFiberBalance
      (x0 + x1 + x2) (z0 - z1 + z2) e := by
  refine ⟨e0 + e1 - z1 + e2 + 1, ?_⟩
  dsimp only [Z180K18M12OneFiberBalance] at h0 h1 h2
  dsimp only [Z180K18M12ThreeFiberBalance]
  omega

/-- Algebraic replacement for the canonical `(12,6)` packed DP. -/
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

/-- Algebraic replacement for the canonical `(12,18)` packed DP. -/
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
  dsimp only [Z180K18M12ThreeFiberBalance,
    Z180K18M12FourRemaindersNonzero] at hX0 hX1 hX2 hY0 hY1 hY2 hne
  omega

/-- Algebraic replacement for the canonical `(12,36)` packed DP after the
twelve short `Phi_36` equations identify each local triple. -/
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

#print axioms z180_k18_m12_phi12_phi4_kernel
#print axioms z180_k18_m12_oneFiberBalance_left
#print axioms z180_k18_m12_oneFiberBalance_right
#print axioms z180_k18_m12_oneFiberBalance_complement_left
#print axioms z180_k18_m12_oneFiberBalance_complement_right
#print axioms z180_k18_m12_threeFiberBalance_of_oneFiber
#print axioms z180_k18_m12_phi12_phi6_kernel
#print axioms z180_k18_m12_phi12_phi18_kernel
#print axioms z180_k18_m12_phi12_phi36_kernel

end Fuglede
