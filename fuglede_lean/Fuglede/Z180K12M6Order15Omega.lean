import Mathlib.Tactic

/-! # Compact Presburger kernel for an order-fifteen zero at `k = 12` -/

namespace Fuglede

namespace Z180K12HighOrder

set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- If three nonnegative aggregate counts have total six and their two
differences from the third count become multiples of five after doubling,
then all three counts agree.  This is the tiny arithmetic core behind the
order-fifteen exclusion. -/
private theorem order15_balanced_aggregate
    (u v w p q : Int)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hsum : u + v + w = 6)
    (huw : 2 * (u - w) = 5 * p)
    (hvw : 2 * (v - w) = 5 * q) :
    u - w = 0 ∧ v - w = 0 := by
  omega

theorem z180_k12_m6_order15_count_impossible
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Int)
    (k0 k1 t0 t1 : Int)
    (hc0lo : 0 ≤ c0) (hc0hi : c0 ≤ 3)
    (hc1lo : 0 ≤ c1) (hc1hi : c1 ≤ 3)
    (hc2lo : 0 ≤ c2) (hc2hi : c2 ≤ 3)
    (hc3lo : 0 ≤ c3) (hc3hi : c3 ≤ 3)
    (hc4lo : 0 ≤ c4) (hc4hi : c4 ≤ 3)
    (hc5lo : 0 ≤ c5) (hc5hi : c5 ≤ 3)
    (hc6lo : 0 ≤ c6) (hc6hi : c6 ≤ 3)
    (hc7lo : 0 ≤ c7) (hc7hi : c7 ≤ 3)
    (hc8lo : 0 ≤ c8) (hc8hi : c8 ≤ 3)
    (hc9lo : 0 ≤ c9) (hc9hi : c9 ≤ 3)
    (hc10lo : 0 ≤ c10) (hc10hi : c10 ≤ 3)
    (hc11lo : 0 ≤ c11) (hc11hi : c11 ≤ 3)
    (hmod4_0 : c0 + c4 + c8 = 3)
    (hmod4_1 : c1 + c5 + c9 = 3)
    (hmod4_2 : c2 + c6 + c10 = 3)
    (hmod4_3 : c3 + c7 + c11 = 3)
    (hphi3_0 : c0 - c2 + c3 - c5 + c6 - c8 + c9 - c11 = 5 * t0)
    (hphi3_1 : c1 - c2 + c4 - c5 + c7 - c8 + c10 - c11 = 5 * t1)
    (hphi6_0 : c0 - c2 - c3 + c5 + c6 - c8 - c9 + c11 = 5 * k0)
    (hphi6_1 : c1 + c2 - c4 - c5 + c7 + c8 - c10 - c11 = 5 * k1)
    (hphi6_ne :
      c0 - c2 - c3 + c5 + c6 - c8 - c9 + c11 ≠ 0 ∨
      c1 + c2 - c4 - c5 + c7 + c8 - c10 - c11 ≠ 0) :
    False := by
  have huA : 0 ≤ c0 + c6 := by omega
  have hvA : 0 ≤ c4 + c10 := by omega
  have hwA : 0 ≤ c8 + c2 := by omega
  have hsumA : (c0 + c6) + (c4 + c10) + (c8 + c2) = 6 := by
    linarith only [hmod4_0, hmod4_2]
  have hdoubleA0 :
      2 * ((c0 + c6) - (c8 + c2)) = 5 * (t0 + k0) := by
    linear_combination hphi3_0 + hphi6_0
  have hdoubleA1 :
      2 * ((c4 + c10) - (c8 + c2)) = 5 * (t1 - k1) := by
    linear_combination hphi3_1 - hphi6_1
  obtain ⟨hA0, hA1⟩ := order15_balanced_aggregate
    (c0 + c6) (c4 + c10) (c8 + c2) (t0 + k0) (t1 - k1)
    huA hvA hwA hsumA hdoubleA0 hdoubleA1
  have huB : 0 ≤ c9 + c3 := by omega
  have hvB : 0 ≤ c1 + c7 := by omega
  have hwB : 0 ≤ c5 + c11 := by omega
  have hsumB : (c9 + c3) + (c1 + c7) + (c5 + c11) = 6 := by
    linarith only [hmod4_1, hmod4_3]
  have hdoubleB0 :
      2 * ((c9 + c3) - (c5 + c11)) = 5 * (t0 - k0) := by
    linear_combination hphi3_0 - hphi6_0
  have hdoubleB1 :
      2 * ((c1 + c7) - (c5 + c11)) = 5 * (t1 + k1) := by
    linear_combination hphi3_1 + hphi6_1
  obtain ⟨hB0, hB1⟩ := order15_balanced_aggregate
    (c9 + c3) (c1 + c7) (c5 + c11) (t0 - k0) (t1 + k1)
    huB hvB hwB hsumB hdoubleB0 hdoubleB1
  rcases hphi6_ne with hne | hne
  · apply hne
    linarith only [hA0, hB0]
  · apply hne
    linarith only [hA1, hB1]

#print axioms z180_k12_m6_order15_count_impossible

end Z180K12HighOrder

end Fuglede
