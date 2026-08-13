import Mathlib.Tactic

/-!
# Presburger kernels for the cardinality-twelve `m = 6` zero sieve

The projected set has three points in each residue class modulo four.  For
orders three and twelve its Fourier-zero condition depends only on the twelve
residue counts.  This file isolates the resulting integer arithmetic; every
leaf is discharged by the kernel-checked `omega` tactic.

The equations are the small-order part of the deterministic audit payload
`d3e848721aa27eba1bb63aa29af8fab9cc95b255be768d1fb08fbebaf16c7185`.
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option linter.unusedVariables false

private theorem k12_phi6_multiplier_bounds
    (x0 x1 x2 x3 x4 x5 x6 x7 k : Int)
    (hx0lo : 0 <= x0) (hx0hi : x0 <= 3)
    (hx1lo : 0 <= x1) (hx1hi : x1 <= 3)
    (hx2lo : 0 <= x2) (hx2hi : x2 <= 3)
    (hx3lo : 0 <= x3) (hx3hi : x3 <= 3)
    (hx4lo : 0 <= x4) (hx4hi : x4 <= 3)
    (hx5lo : 0 <= x5) (hx5hi : x5 <= 3)
    (hx6lo : 0 <= x6) (hx6hi : x6 <= 3)
    (hx7lo : 0 <= x7) (hx7hi : x7 <= 3)
    (hrem : x0 - x1 - x2 + x3 + x4 - x5 - x6 + x7 = 5 * k) :
    -2 <= k ∧ k <= 2 := by
  omega

private theorem k12_five_diff_eq_six_mul_forces_eq
    (k0 k1 t : Int)
    (hk0lo : -2 <= k0) (hk0hi : k0 <= 2)
    (hk1lo : -2 <= k1) (hk1hi : k1 <= 2)
    (hdiv : -5 * k0 + 5 * k1 = 6 * t) :
    k0 = k1 := by
  omega

private theorem k12_q3_bounds_force_multiplier_zero
    (k c3 c4 c9 c10 : Int)
    (hklo : -2 <= k) (hkhi : k <= 2)
    (hc3lo : 0 <= c3) (hc3hi : c3 <= 3)
    (hc4lo : 0 <= c4) (hc4hi : c4 <= 3)
    (hc9lo : 0 <= c9) (hc9hi : c9 <= 3)
    (hc10lo : 0 <= c10) (hc10hi : c10 <= 3)
    (hupper : 15 * k = 6 * (2 - c4 - c10))
    (hlower : 15 * k = 6 * (2 - c3 - c9)) :
    k = 0 := by
  omega

private theorem k12_q12_bounds_force_multiplier_zero
    (k c1 c3 c10 c11 : Int)
    (hklo : -2 <= k) (hkhi : k <= 2)
    (hc1lo : 0 <= c1) (hc1hi : c1 <= 3)
    (hc3lo : 0 <= c3) (hc3hi : c3 <= 3)
    (hc10lo : 0 <= c10) (hc10hi : c10 <= 3)
    (hc11lo : 0 <= c11) (hc11hi : c11 <= 3)
    (hupper : 15 * k = 6 * (c1 - c10))
    (hlower : 15 * k = 6 * (3 - c3 - c10 - c11)) :
    k = 0 := by
  omega

/-- Under uniform projection modulo four and a primitive-third-root zero, a
pair of integral `Phi_6` remainder coefficients divisible by five must be
zero.  The final disjunction states the defect assumption that at least one
coefficient is nonzero. -/
theorem z180_k12_m6_count_order3_impossible
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 k0 k1 : Int)
    (hc0lo : 0 <= c0) (hc0hi : c0 <= 3)
    (hc1lo : 0 <= c1) (hc1hi : c1 <= 3)
    (hc2lo : 0 <= c2) (hc2hi : c2 <= 3)
    (hc3lo : 0 <= c3) (hc3hi : c3 <= 3)
    (hc4lo : 0 <= c4) (hc4hi : c4 <= 3)
    (hc5lo : 0 <= c5) (hc5hi : c5 <= 3)
    (hc6lo : 0 <= c6) (hc6hi : c6 <= 3)
    (hc7lo : 0 <= c7) (hc7hi : c7 <= 3)
    (hc8lo : 0 <= c8) (hc8hi : c8 <= 3)
    (hc9lo : 0 <= c9) (hc9hi : c9 <= 3)
    (hc10lo : 0 <= c10) (hc10hi : c10 <= 3)
    (hc11lo : 0 <= c11) (hc11hi : c11 <= 3)
    (hmod4_0 : c0 + c4 + c8 = 3)
    (hmod4_1 : c1 + c5 + c9 = 3)
    (hmod4_2 : c2 + c6 + c10 = 3)
    (hmod4_3 : c3 + c7 + c11 = 3)
    (hphi3_0 : c0 - c2 + c3 - c5 + c6 - c8 + c9 - c11 = 0)
    (hphi3_1 : c1 - c2 + c4 - c5 + c7 - c8 + c10 - c11 = 0)
    (hphi6_0 : c0 - c2 - c3 + c5 + c6 - c8 - c9 + c11 = 5 * k0)
    (hphi6_1 : c1 + c2 - c4 - c5 + c7 + c8 - c10 - c11 = 5 * k1)
    (hphi6_ne :
      c0 - c2 - c3 + c5 + c6 - c8 - c9 + c11 ≠ 0 \/
      c1 + c2 - c4 - c5 + c7 + c8 - c10 - c11 ≠ 0) :
    False := by
  obtain ⟨hk0lo, hk0hi⟩ := k12_phi6_multiplier_bounds
    c0 c2 c3 c5 c6 c8 c9 c11 k0
    hc0lo hc0hi hc2lo hc2hi hc3lo hc3hi hc5lo hc5hi
    hc6lo hc6hi hc8lo hc8hi hc9lo hc9hi hc11lo hc11hi hphi6_0
  obtain ⟨hk1lo, hk1hi⟩ := k12_phi6_multiplier_bounds
    c1 c4 c5 c2 c7 c10 c11 c8 k1
    hc1lo hc1hi hc4lo hc4hi hc5lo hc5hi hc2lo hc2hi
    hc7lo hc7hi hc10lo hc10hi hc11lo hc11hi hc8lo hc8hi (by linarith)
  have hdiv1 :
      -5 * k0 + 5 * k1 = 6 * (c1 - c11 + c9 - 1) := by
    linarith
  have hk : k0 = k1 :=
    k12_five_diff_eq_six_mul_forces_eq
      k0 k1 (c1 - c11 + c9 - 1)
      hk0lo hk0hi hk1lo hk1hi hdiv1
  subst k1
  have hupper : 15 * k0 = 6 * (2 - c4 - c10) := by
    linarith
  have hlower : 15 * k0 = 6 * (2 - c3 - c9) := by
    linarith
  have hkzero : k0 = 0 :=
    k12_q3_bounds_force_multiplier_zero
      k0 c3 c4 c9 c10 hk0lo hk0hi
      hc3lo hc3hi hc4lo hc4hi hc9lo hc9hi hc10lo hc10hi
      hupper hlower
  subst k0
  norm_num at hphi6_0 hphi6_1
  rcases hphi6_ne with hne0 | hne1
  · exact hne0 hphi6_0
  · exact hne1 hphi6_1

/-- The analogous count kernel for a primitive-twelfth-root zero. -/
theorem z180_k12_m6_count_order12_impossible
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 k0 k1 : Int)
    (hc0lo : 0 <= c0) (hc0hi : c0 <= 3)
    (hc1lo : 0 <= c1) (hc1hi : c1 <= 3)
    (hc2lo : 0 <= c2) (hc2hi : c2 <= 3)
    (hc3lo : 0 <= c3) (hc3hi : c3 <= 3)
    (hc4lo : 0 <= c4) (hc4hi : c4 <= 3)
    (hc5lo : 0 <= c5) (hc5hi : c5 <= 3)
    (hc6lo : 0 <= c6) (hc6hi : c6 <= 3)
    (hc7lo : 0 <= c7) (hc7hi : c7 <= 3)
    (hc8lo : 0 <= c8) (hc8hi : c8 <= 3)
    (hc9lo : 0 <= c9) (hc9hi : c9 <= 3)
    (hc10lo : 0 <= c10) (hc10hi : c10 <= 3)
    (hc11lo : 0 <= c11) (hc11hi : c11 <= 3)
    (hmod4_0 : c0 + c4 + c8 = 3)
    (hmod4_1 : c1 + c5 + c9 = 3)
    (hmod4_2 : c2 + c6 + c10 = 3)
    (hmod4_3 : c3 + c7 + c11 = 3)
    (hphi12_0 : c0 - c4 - c6 + c10 = 0)
    (hphi12_1 : c1 - c5 - c7 + c11 = 0)
    (hphi12_2 : c2 + c4 - c8 - c10 = 0)
    (hphi12_3 : c3 + c5 - c9 - c11 = 0)
    (hphi6_0 : c0 - c2 - c3 + c5 + c6 - c8 - c9 + c11 = 5 * k0)
    (hphi6_1 : c1 + c2 - c4 - c5 + c7 + c8 - c10 - c11 = 5 * k1)
    (hphi6_ne :
      c0 - c2 - c3 + c5 + c6 - c8 - c9 + c11 ≠ 0 \/
      c1 + c2 - c4 - c5 + c7 + c8 - c10 - c11 ≠ 0) :
    False := by
  obtain ⟨hk0lo, hk0hi⟩ := k12_phi6_multiplier_bounds
    c0 c2 c3 c5 c6 c8 c9 c11 k0
    hc0lo hc0hi hc2lo hc2hi hc3lo hc3hi hc5lo hc5hi
    hc6lo hc6hi hc8lo hc8hi hc9lo hc9hi hc11lo hc11hi hphi6_0
  obtain ⟨hk1lo, hk1hi⟩ := k12_phi6_multiplier_bounds
    c1 c4 c5 c2 c7 c10 c11 c8 k1
    hc1lo hc1hi hc4lo hc4hi hc5lo hc5hi hc2lo hc2hi
    hc7lo hc7hi hc10lo hc10hi hc11lo hc11hi hc8lo hc8hi (by linarith)
  have hdiv0 :
      5 * k0 - 5 * k1 = 6 * (c0 + c10 + c11 - 3) := by
    linarith
  have hk : k0 = k1 := by
    apply k12_five_diff_eq_six_mul_forces_eq
      k0 k1 (-(c0 + c10 + c11 - 3))
      hk0lo hk0hi hk1lo hk1hi
    linarith
  subst k1
  have hupper : 15 * k0 = 6 * (c1 - c10) := by
    linarith
  have hlower : 15 * k0 = 6 * (3 - c3 - c10 - c11) := by
    linarith
  have hkzero : k0 = 0 :=
    k12_q12_bounds_force_multiplier_zero
      k0 c1 c3 c10 c11 hk0lo hk0hi
      hc1lo hc1hi hc3lo hc3hi hc10lo hc10hi hc11lo hc11hi
      hupper hlower
  subst k0
  norm_num at hphi6_0 hphi6_1
  rcases hphi6_ne with hne0 | hne1
  · exact hne0 hphi6_0
  · exact hne1 hphi6_1

#print axioms z180_k12_m6_count_order3_impossible
#print axioms z180_k12_m6_count_order12_impossible

end Fuglede
