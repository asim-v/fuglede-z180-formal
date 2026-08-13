import Fuglede.Z180K6LowOrderPhi23Compact
import Fuglede.Z36Card6ForcingPhi36BlockBridge
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-! A balanced even/odd profile supplies the factor `Phi_2`. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z36_parity_balance_forces_phi2
    (b : Fin 36 → Int)
    (hbalance : z36Mod6Block b 0 + z36Mod6Block b 2 + z36Mod6Block b 4 =
      z36Mod6Block b 1 + z36Mod6Block b 3 + z36Mod6Block b 5) :
    cyclotomic 2 Int ∣ projection36IndicatorMask b := by
  have hv0 : ZMod.val (0 : ZMod 6) = 0 := by decide
  have hv1 : ZMod.val (1 : ZMod 6) = 1 := by decide
  have hv2 : ZMod.val (2 : ZMod 6) = 2 := by decide
  have hv3 : ZMod.val (3 : ZMod 6) = 3 := by decide
  have hv4 : ZMod.val (4 : ZMod 6) = 4 := by decide
  have hv5 : ZMod.val (5 : ZMod 6) = 5 := by decide
  let c0 := z180K6ResidueSixSum b 0
  let c1 := z180K6ResidueSixSum b 1
  let c2 := z180K6ResidueSixSum b 2
  let c3 := z180K6ResidueSixSum b 3
  let c4 := z180K6ResidueSixSum b 4
  let c5 := z180K6ResidueSixSum b 5
  have hc0 : c0 = z36Mod6Block b 0 := by
    dsimp only [c0]
    norm_num [z180K6ResidueSixSum, hv0]
    symm
    exact z36_mod6_block_0 b
  have hc1 : c1 = z36Mod6Block b 1 := by
    dsimp only [c1]
    norm_num [z180K6ResidueSixSum, hv1]
    symm
    exact z36_mod6_block_1 b
  have hc2 : c2 = z36Mod6Block b 2 := by
    dsimp only [c2]
    norm_num [z180K6ResidueSixSum, hv2]
    symm
    exact z36_mod6_block_2 b
  have hc3 : c3 = z36Mod6Block b 3 := by
    dsimp only [c3]
    norm_num [z180K6ResidueSixSum, hv3]
    symm
    exact z36_mod6_block_3 b
  have hc4 : c4 = z36Mod6Block b 4 := by
    dsimp only [c4]
    norm_num [z180K6ResidueSixSum, hv4]
    symm
    exact z36_mod6_block_4 b
  have hc5 : c5 = z36Mod6Block b 5 := by
    dsimp only [c5]
    norm_num [z180K6ResidueSixSum, hv5]
    symm
    exact z36_mod6_block_5 b
  have hcBalance : c0 + c2 + c4 = c1 + c3 + c5 := by
    linarith only [hbalance, hc0, hc1, hc2, hc3, hc4, hc5]
  have hroot : IsRoot (z180K6ResiduePolynomial6 b) (-1 : Int) := by
    rw [IsRoot, z180K6ResiduePolynomial6]
    simp only [eval_add, eval_monomial]
    norm_num
    dsimp only [c0, c1, c2, c3, c4, c5] at hcBalance
    linarith only [hcBalance]
  have hresidue : cyclotomic 2 Int ∣ projection36ResidueMask6 b := by
    rw [projection36ResidueMask6_eq_k6ResiduePolynomial6]
    have hdvd : X - C (-1 : Int) ∣ z180K6ResiduePolynomial6 b :=
      dvd_iff_isRoot.mpr hroot
    simpa [cyclotomic_two] using hdvd
  have hdifference : cyclotomic 2 Int ∣
      projection36IndicatorMask b - projection36ResidueMask6 b :=
    cyclotomic_dvd_projection36Indicator_sub_residue6 b 2 (by norm_num)
  simpa using dvd_add hdifference hresidue

#print axioms z36_parity_balance_forces_phi2

end Fuglede
