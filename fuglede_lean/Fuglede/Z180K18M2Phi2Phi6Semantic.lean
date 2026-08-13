import Fuglede.Z180K18M2Phi2Phi6Bridge
import Fuglede.Z180K18M12PairFibresLowOrder
import Fuglede.Z180K18M12PairFibresHighOrderCombinatorial
import Fuglede.Z180K12M6HighOrderModFive
import Fuglede.Z180K18DescentImages
import Mathlib.Tactic

/-!
# Semantic realization of the (m=2), ((Phi_2,Phi_6)) kernel

This module connects the genuine set-side hypotheses to the three bounded
integers consumed by `z180_k18_m2_phi2_phi6_pairRemainder_kernel`.

The already-proved `Phi_3/Phi_9` fibre theorem gives mass two over each
residue modulo nine.  Injectivity modulo 36 makes the projected occupancy a
zero-one function.  In each four-point fibre its parity balance is twice one
of `-1,0,1`.  Grouping the nine balances by the residue modulo three gives
the three integers `alpha,beta,gamma`.

`Phi_10/not-Phi_2` makes the total `Phi_2` remainder a nonzero multiple
of five.  A putative `Phi_6` or `Phi_30` zero makes the two `Phi_6`
remainders multiples of five.  The explicit remainder identities are then
exactly the three equations in the small arithmetic kernel.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Explicit integral remainder modulo `Phi_2 = X+1`. -/
def z180K18ProjectionPhi2R0 (b : Fin 36 → Int) : Int :=
  b 0 - b 1 + b 2 - b 3 + b 4 - b 5 +
    b 6 - b 7 + b 8 - b 9 + b 10 - b 11 +
    b 12 - b 13 + b 14 - b 15 + b 16 - b 17 +
    b 18 - b 19 + b 20 - b 21 + b 22 - b 23 +
    b 24 - b 25 + b 26 - b 27 + b 28 - b 29 +
    b 30 - b 31 + b 32 - b 33 + b 34 - b 35

/-- The generic monic-remainder coefficient used by the mod-five framework
is the displayed parity balance. -/
theorem projection36_phi2_remainderCoeff_eq
    (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 2 b 0 =
      z180K18ProjectionPhi2R0 b := by
  rw [projection36CyclotomicRemainderCoeff]
  have htwo :
      cyclotomic 2 Int = X - C (-1 : Int) := by
    rw [cyclotomic_two]
    norm_num
  rw [htwo, modByMonic_X_sub_C_eq_C_eval]
  simp only [coeff_C, if_pos]
  let bn : Nat → Int := fun n =>
    b ⟨n % 36, Nat.mod_lt n (by norm_num)⟩
  have hbn (i : Fin 36) : bn i.val = b i := by
    apply congrArg b
    apply Fin.ext
    simp [bn, Nat.mod_eq_of_lt i.isLt]
  have hbn0 : bn 0 = b 0 := by simpa using hbn (0 : Fin 36)
  have hbn1 : bn 1 = b 1 := by simpa using hbn (1 : Fin 36)
  have hbn2 : bn 2 = b 2 := by simpa using hbn (2 : Fin 36)
  have hbn3 : bn 3 = b 3 := by simpa using hbn (3 : Fin 36)
  have hbn4 : bn 4 = b 4 := by simpa using hbn (4 : Fin 36)
  have hbn5 : bn 5 = b 5 := by simpa using hbn (5 : Fin 36)
  have hbn6 : bn 6 = b 6 := by simpa using hbn (6 : Fin 36)
  have hbn7 : bn 7 = b 7 := by simpa using hbn (7 : Fin 36)
  have hbn8 : bn 8 = b 8 := by simpa using hbn (8 : Fin 36)
  have hbn9 : bn 9 = b 9 := by simpa using hbn (9 : Fin 36)
  have hbn10 : bn 10 = b 10 := by simpa using hbn (10 : Fin 36)
  have hbn11 : bn 11 = b 11 := by simpa using hbn (11 : Fin 36)
  have hbn12 : bn 12 = b 12 := by simpa using hbn (12 : Fin 36)
  have hbn13 : bn 13 = b 13 := by simpa using hbn (13 : Fin 36)
  have hbn14 : bn 14 = b 14 := by simpa using hbn (14 : Fin 36)
  have hbn15 : bn 15 = b 15 := by simpa using hbn (15 : Fin 36)
  have hbn16 : bn 16 = b 16 := by simpa using hbn (16 : Fin 36)
  have hbn17 : bn 17 = b 17 := by simpa using hbn (17 : Fin 36)
  have hbn18 : bn 18 = b 18 := by simpa using hbn (18 : Fin 36)
  have hbn19 : bn 19 = b 19 := by simpa using hbn (19 : Fin 36)
  have hbn20 : bn 20 = b 20 := by simpa using hbn (20 : Fin 36)
  have hbn21 : bn 21 = b 21 := by simpa using hbn (21 : Fin 36)
  have hbn22 : bn 22 = b 22 := by simpa using hbn (22 : Fin 36)
  have hbn23 : bn 23 = b 23 := by simpa using hbn (23 : Fin 36)
  have hbn24 : bn 24 = b 24 := by simpa using hbn (24 : Fin 36)
  have hbn25 : bn 25 = b 25 := by simpa using hbn (25 : Fin 36)
  have hbn26 : bn 26 = b 26 := by simpa using hbn (26 : Fin 36)
  have hbn27 : bn 27 = b 27 := by simpa using hbn (27 : Fin 36)
  have hbn28 : bn 28 = b 28 := by simpa using hbn (28 : Fin 36)
  have hbn29 : bn 29 = b 29 := by simpa using hbn (29 : Fin 36)
  have hbn30 : bn 30 = b 30 := by simpa using hbn (30 : Fin 36)
  have hbn31 : bn 31 = b 31 := by simpa using hbn (31 : Fin 36)
  have hbn32 : bn 32 = b 32 := by simpa using hbn (32 : Fin 36)
  have hbn33 : bn 33 = b 33 := by simpa using hbn (33 : Fin 36)
  have hbn34 : bn 34 = b 34 := by simpa using hbn (34 : Fin 36)
  have hbn35 : bn 35 = b 35 := by simpa using hbn (35 : Fin 36)
  have heval :
      (projection36IndicatorMask b).eval (-1) =
        ∑ i : Fin 36, (-1 : Int) ^ i.val * bn i.val := by
    rw [projection36IndicatorMask, eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [eval_monomial, hbn i]
    exact mul_comm _ _
  rw [heval]
  rw [Fin.sum_univ_eq_sum_range
    (fun n => (-1 : Int) ^ n * bn n) 36]
  norm_num [Finset.sum_range_succ]
  simp only [hbn0, hbn1, hbn2, hbn3, hbn4, hbn5, hbn6, hbn7,
    hbn8, hbn9, hbn10, hbn11, hbn12, hbn13, hbn14, hbn15,
    hbn16, hbn17, hbn18, hbn19, hbn20, hbn21, hbn22, hbn23,
    hbn24, hbn25, hbn26, hbn27, hbn28, hbn29, hbn30, hbn31,
    hbn32, hbn33, hbn34, hbn35]
  dsimp only [z180K18ProjectionPhi2R0]
  ring

private theorem pair_sum_sub_one_bounds
    (x y : Int) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    -1 ≤ x + y - 1 ∧ x + y - 1 ≤ 1 := by
  omega

/-- The semantic set-to-remainder bridge for both orders 6 and 30. -/
theorem z180_k18_m2_phi2Phi6Bridge :
    Z180K18M2Phi2Phi6BridgeInterface := by
  intro A L hSpec hcard hcore hdefect q hq hqzero
  let b : Fin 36 → Int := z180K12ProjectionIndicator A
  have hlo : ∀ i : Fin 36, 0 ≤ b i := by
    intro i
    exact z180K12ProjectionIndicator_nonneg A i
  have hinj0 := z180_k18_projection36_injOn hSpec hcard
  have hinj :
      Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
        (A : Set (ZMod 180)) := by
    intro x hx y hy hxy
    apply hinj0 hx hy
    simpa only [z180K18Projection36_apply] using hxy
  have hhi : ∀ i : Fin 36, b i ≤ 1 := by
    intro i
    exact z180K12ProjectionIndicator_le_one_of_injOn hinj i

  have hfreq60 : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
  have hfreq20 : frequencyOrder 180 (20 : ZMod 180) = 9 := by decide
  have h3 : cyclotomic 3 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq60] using hcore.1
  have h9 : cyclotomic 9 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq20] using hcore.2.1
  have hnine :=
    z180_k18_m12_nineFibres_card_two_of_phi3_phi9 A hcard h3 h9
  have hmass0 :=
    z180_k18_m12_projection_mass_two_of_card_two A hnine
  have hmass : ∀ r : ZMod 9, z180K18M12NineFiberMass b r = 2 := by
    simpa [b, Z180K18M12ProjectionNineFibresHaveMassTwo] using hmass0

  have hm0 : b 0 + b 9 + b 18 + b 27 = 2 := by
    have h := hmass (0 : ZMod 9)
    norm_num [z180K18M12NineFiberMass] at h
    exact h
  have hm1 : b 1 + b 10 + b 19 + b 28 = 2 := by
    have h := hmass (1 : ZMod 9)
    norm_num [z180K18M12NineFiberMass] at h
    exact h
  have hm2 : b 2 + b 11 + b 20 + b 29 = 2 := by
    have h := hmass (2 : ZMod 9)
    norm_num [z180K18M12NineFiberMass] at h
    exact h
  have hm3 : b 3 + b 12 + b 21 + b 30 = 2 := by
    have h := hmass (3 : ZMod 9)
    norm_num [z180K18M12NineFiberMass] at h
    exact h
  have hm4 : b 4 + b 13 + b 22 + b 31 = 2 := by
    have h := hmass (4 : ZMod 9)
    norm_num [z180K18M12NineFiberMass] at h
    exact h
  have hm5 : b 5 + b 14 + b 23 + b 32 = 2 := by
    have h := hmass (5 : ZMod 9)
    norm_num [z180K18M12NineFiberMass] at h
    exact h
  have hm6 : b 6 + b 15 + b 24 + b 33 = 2 := by
    have h := hmass (6 : ZMod 9)
    norm_num [z180K18M12NineFiberMass] at h
    exact h
  have hm7 : b 7 + b 16 + b 25 + b 34 = 2 := by
    have h := hmass (7 : ZMod 9)
    norm_num [z180K18M12NineFiberMass] at h
    exact h
  have hm8 : b 8 + b 17 + b 26 + b 35 = 2 := by
    have h := hmass (8 : ZMod 9)
    norm_num [z180K18M12NineFiberMass] at h
    exact h

  let t0 := b 0 + b 18 - 1
  let t1 := b 10 + b 28 - 1
  let t2 := b 2 + b 20 - 1
  let t3 := b 12 + b 30 - 1
  let t4 := b 4 + b 22 - 1
  let t5 := b 14 + b 32 - 1
  let t6 := b 6 + b 24 - 1
  let t7 := b 16 + b 34 - 1
  let t8 := b 8 + b 26 - 1
  let alpha := t0 + t3 + t6
  let beta := t1 + t4 + t7
  let gamma := t2 + t5 + t8

  obtain ⟨ht0lo, ht0hi⟩ := pair_sum_sub_one_bounds
    (b 0) (b 18) (hlo 0) (hhi 0) (hlo 18) (hhi 18)
  obtain ⟨ht1lo, ht1hi⟩ := pair_sum_sub_one_bounds
    (b 10) (b 28) (hlo 10) (hhi 10) (hlo 28) (hhi 28)
  obtain ⟨ht2lo, ht2hi⟩ := pair_sum_sub_one_bounds
    (b 2) (b 20) (hlo 2) (hhi 2) (hlo 20) (hhi 20)
  obtain ⟨ht3lo, ht3hi⟩ := pair_sum_sub_one_bounds
    (b 12) (b 30) (hlo 12) (hhi 12) (hlo 30) (hhi 30)
  obtain ⟨ht4lo, ht4hi⟩ := pair_sum_sub_one_bounds
    (b 4) (b 22) (hlo 4) (hhi 4) (hlo 22) (hhi 22)
  obtain ⟨ht5lo, ht5hi⟩ := pair_sum_sub_one_bounds
    (b 14) (b 32) (hlo 14) (hhi 14) (hlo 32) (hhi 32)
  obtain ⟨ht6lo, ht6hi⟩ := pair_sum_sub_one_bounds
    (b 6) (b 24) (hlo 6) (hhi 6) (hlo 24) (hhi 24)
  obtain ⟨ht7lo, ht7hi⟩ := pair_sum_sub_one_bounds
    (b 16) (b 34) (hlo 16) (hhi 16) (hlo 34) (hhi 34)
  obtain ⟨ht8lo, ht8hi⟩ := pair_sum_sub_one_bounds
    (b 8) (b 26) (hlo 8) (hhi 8) (hlo 26) (hhi 26)
  have halphaLo : -3 ≤ alpha := by
    dsimp only [alpha, t0, t3, t6]
    omega
  have halphaHi : alpha ≤ 3 := by
    dsimp only [alpha, t0, t3, t6]
    omega
  have hbetaLo : -3 ≤ beta := by
    dsimp only [beta, t1, t4, t7]
    omega
  have hbetaHi : beta ≤ 3 := by
    dsimp only [beta, t1, t4, t7]
    omega
  have hgammaLo : -3 ≤ gamma := by
    dsimp only [gamma, t2, t5, t8]
    omega
  have hgammaHi : gamma ≤ 3 := by
    dsimp only [gamma, t2, t5, t8]
    omega

  have hR2 :
      z180K18ProjectionPhi2R0 b = 2 * (alpha + beta + gamma) := by
    dsimp only [z180K18ProjectionPhi2R0, alpha, beta, gamma,
      t0, t1, t2, t3, t4, t5, t6, t7, t8]
    omega
  have hR60 :
      projection36Phi6R0 b = 2 * (alpha - gamma) := by
    dsimp only [projection36Phi6R0, alpha, gamma,
      t0, t2, t3, t5, t6, t8]
    omega
  have hR61 :
      projection36Phi6R1 b = 2 * (-beta + gamma) := by
    dsimp only [projection36Phi6R1, beta, gamma,
      t1, t2, t4, t5, t7, t8]
    omega

  obtain ⟨l1, hl1, l2, hl2, hne, hbase, horder,
    h10, hnot2⟩ := hdefect
  have hmod2 :=
    cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 2) (by norm_num) (by norm_num) (by simpa using h10)
  obtain ⟨k2, hk2⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hmod2 0
  have hcoeff2 :=
    projection36_phi2_remainderCoeff_eq b
  have hnotIndicator :
      ¬ cyclotomic 2 Int ∣ projection36IndicatorMask b := by
    intro hind
    apply hnot2
    apply (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (m := 2) (by norm_num)).1
    simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator] using hind
  have hcoeff2ne :
      projection36CyclotomicRemainderCoeff 2 b 0 ≠ 0 := by
    intro hz
    apply hnotIndicator
    apply cyclotomic_dvd_projection36Indicator_of_remainderCoeff_zero b
    intro j hj
    have hj0 : j = 0 := by
      norm_num at hj
      omega
    subst j
    exact hz

  have h6multipliers :
      ∃ k60 k61 : Int,
        projection36Phi6R0 b = 5 * k60 ∧
        projection36Phi6R1 b = 5 * k61 := by
    simp only [z180K18M2Phi2Phi6ExcludedOrders, Finset.mem_insert,
      Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · have hprojected :
          cyclotomic 6 Int ∣ z180Projection36Mask A :=
        (cyclotomic_dvd_projection36Mask_iff_dvd_mask
          (m := 6) (by norm_num)).2 hqzero
      have hindicator :
          cyclotomic 6 Int ∣ projection36IndicatorMask b := by
        simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
          using hprojected
      obtain ⟨hr0, hr1⟩ :=
        (projection36_phi6_dvd_iff_remainders_zero b).1 hindicator
      exact ⟨0, 0, by simpa using hr0, by simpa using hr1⟩
    · have hmod6 :=
        cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
          (A := A) (m := 6) (by norm_num) (by norm_num)
            (by simpa using hqzero)
      exact projection36_phi6_five_multipliers b hmod6
  obtain ⟨k60, k61, hk60, hk61⟩ := h6multipliers

  have h2final : 2 * (alpha + beta + gamma) = 5 * k2 := by
    rw [← hR2, ← hcoeff2]
    exact hk2
  have h60final : 2 * (alpha - gamma) = 5 * k60 := by
    rw [← hR60]
    exact hk60
  have h61final : 2 * (-beta + gamma) = 5 * k61 := by
    rw [← hR61]
    exact hk61
  have h2finalNe : 2 * (alpha + beta + gamma) ≠ 0 := by
    rw [← hR2, ← hcoeff2]
    exact hcoeff2ne
  exact ⟨alpha, beta, gamma, k2, k60, k61,
    halphaLo, halphaHi, hbetaLo, hbetaHi, hgammaLo, hgammaHi,
    h2final, h60final, h61final, h2finalNe⟩

/-- The `m=2` envelope now has only the four explicitly named far
exclusions `15,18,45,90` left. -/
theorem z180_k18_m2_residual_of_far
    (hfar : Z180K18M2FarResidualEnvelopeInterface) :
    Z180K18M2ResidualEnvelopeInterface :=
  z180_k18_m2_residual_of_phi2Phi6Bridge
    z180_k18_m2_phi2Phi6Bridge hfar

/-- Direct assembly into the public envelope interface from that four-order
frontier. -/
theorem z180_k18_m2_envelope_of_far
    (hfar : Z180K18M2FarResidualEnvelopeInterface) :
    Z180K18M2EnvelopeInterface :=
  z180_k18_m2_envelope_of_residual
    (z180_k18_m2_residual_of_far hfar)

#print axioms projection36_phi2_remainderCoeff_eq
#print axioms z180_k18_m2_phi2Phi6Bridge
#print axioms z180_k18_m2_envelope_of_far

end Fuglede
