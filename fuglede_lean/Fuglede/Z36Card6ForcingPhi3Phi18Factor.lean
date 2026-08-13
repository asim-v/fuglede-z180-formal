import Fuglede.Z180K6LowOrderPhi23Compact
import Fuglede.Z36Card6ForcingPhi36BlockBridge
import Mathlib.Tactic

/-! A uniform mod-six profile supplies both low-order cyclotomic factors. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z36_mod6_blocks_one_forces_phi2_phi6
    (b : Fin 36 → Int)
    (h0 : z36Mod6Block b 0 = 1)
    (h1 : z36Mod6Block b 1 = 1)
    (h2 : z36Mod6Block b 2 = 1)
    (h3 : z36Mod6Block b 3 = 1)
    (h4 : z36Mod6Block b 4 = 1)
    (h5 : z36Mod6Block b 5 = 1) :
    cyclotomic 2 Int ∣ projection36IndicatorMask b ∧
      cyclotomic 6 Int ∣ projection36IndicatorMask b := by
  have hv0 : ZMod.val (0 : ZMod 6) = 0 := by decide
  have hv1 : ZMod.val (1 : ZMod 6) = 1 := by decide
  have hv2 : ZMod.val (2 : ZMod 6) = 2 := by decide
  have hv3 : ZMod.val (3 : ZMod 6) = 3 := by decide
  have hv4 : ZMod.val (4 : ZMod 6) = 4 := by decide
  have hv5 : ZMod.val (5 : ZMod 6) = 5 := by decide
  have r0 : z180K6ResidueSixSum b 0 = 1 := by
    norm_num [z180K6ResidueSixSum, hv0, z36_mod6_block_0]
    simpa [z36_mod6_block_0] using h0
  have r1 : z180K6ResidueSixSum b 1 = 1 := by
    norm_num [z180K6ResidueSixSum, hv1, z36_mod6_block_1]
    simpa [z36_mod6_block_1] using h1
  have r2 : z180K6ResidueSixSum b 2 = 1 := by
    norm_num [z180K6ResidueSixSum, hv2, z36_mod6_block_2]
    simpa [z36_mod6_block_2] using h2
  have r3 : z180K6ResidueSixSum b 3 = 1 := by
    norm_num [z180K6ResidueSixSum, hv3, z36_mod6_block_3]
    simpa [z36_mod6_block_3] using h3
  have r4 : z180K6ResidueSixSum b 4 = 1 := by
    norm_num [z180K6ResidueSixSum, hv4, z36_mod6_block_4]
    simpa [z36_mod6_block_4] using h4
  have r5 : z180K6ResidueSixSum b 5 = 1 := by
    norm_num [z180K6ResidueSixSum, hv5, z36_mod6_block_5]
    simpa [z36_mod6_block_5] using h5
  have hpoly : z180K6ResiduePolynomial6 b =
      1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 := by
    rw [z180K6ResiduePolynomial6, r0, r1, r2, r3, r4, r5]
    simp only [monomial_one_right_eq_X_pow, pow_zero, pow_one]
  have hdifference2 : cyclotomic 2 Int ∣
      projection36IndicatorMask b - projection36ResidueMask6 b :=
    cyclotomic_dvd_projection36Indicator_sub_residue6 b 2 (by norm_num)
  have hdifference6 : cyclotomic 6 Int ∣
      projection36IndicatorMask b - projection36ResidueMask6 b :=
    cyclotomic_dvd_projection36Indicator_sub_residue6 b 6 (by norm_num)
  have hresidue2 : cyclotomic 2 Int ∣ projection36ResidueMask6 b := by
    rw [projection36ResidueMask6_eq_k6ResiduePolynomial6, hpoly]
    refine ⟨X ^ 4 + X ^ 2 + 1, ?_⟩
    rw [cyclotomic_two]
    ring
  have hresidue6 : cyclotomic 6 Int ∣ projection36ResidueMask6 b := by
    rw [projection36ResidueMask6_eq_k6ResiduePolynomial6, hpoly]
    refine ⟨X ^ 3 + 2 * X ^ 2 + 2 * X + 1, ?_⟩
    rw [cyclotomic_six]
    ring
  constructor
  · simpa using dvd_add hdifference2 hresidue2
  · simpa using dvd_add hdifference6 hresidue6

#print axioms z36_mod6_blocks_one_forces_phi2_phi6

end Fuglede
