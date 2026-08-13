import Fuglede.Z180K18EnvelopeReducedFrontier
import Fuglede.Z180K12M6HighOrderRemainders18Shard
import Mathlib.Tactic

/-!
# Semantic closure of the final `m = 2` envelope frontier

The two residual orders `18` and `90` share the same projected
`Phi_18` remainder block.  For order `18` the six integral remainders
vanish directly; for order `90` they vanish after reduction modulo five
because the projected occupancy is zero-one.

The `Phi_3/Phi_9` core gives mass two in every residue class modulo nine.
Writing the parity imbalance in each such class as twice a number
`t_i in {-1,0,1}`, the six `Phi_18` equations identify

`t_0 = t_3 = t_6`, `t_1 = t_4 = t_7`, and `t_2 = t_5 = t_8`.

Hence the projected `Phi_2` remainder is
`6 * (t_0 + t_1 + t_2)`.  The defect supplies `Phi_10` but not `Phi_2`,
so this remainder is simultaneously a nonzero multiple of five.  Its
bounds make that impossible.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- The canonical `(2,18)` arithmetic closes both final `m = 2` orders. -/
theorem z180_k18_m2_finalDP :
    Z180K18M2FinalDPEnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect q hq hqzero
  let b : Fin 36 → Int := z180K12ProjectionIndicator A
  have hlo : ∀ i : Fin 36, 0 ≤ b i := by
    intro i
    exact z180K12ProjectionIndicator_nonneg A i
  have hinj0 := z180_k18_projection36_injOn hSpec hcard
  have hinj :
      Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
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

  obtain ⟨l1, hl1, l2, hl2, hne, hbase, horder, h10, hnot2⟩ := hdefect
  have hmod2 :=
    cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 2) (by norm_num) (by norm_num) (by simpa using h10)
  obtain ⟨k2, hk2⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hmod2 0
  have hcoeff2 := projection36_phi2_remainderCoeff_eq b
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

  have hremainders :
      b 0 - b 6 - b 9 + b 15 + b 18 - b 24 - b 27 + b 33 = 0 ∧
      b 1 - b 7 - b 10 + b 16 + b 19 - b 25 - b 28 + b 34 = 0 ∧
      b 2 - b 8 - b 11 + b 17 + b 20 - b 26 - b 29 + b 35 = 0 ∧
      b 3 + b 6 - b 12 - b 15 + b 21 + b 24 - b 30 - b 33 = 0 ∧
      b 4 + b 7 - b 13 - b 16 + b 22 + b 25 - b 31 - b 34 = 0 ∧
      b 5 + b 8 - b 14 - b 17 + b 23 + b 26 - b 32 - b 35 = 0 := by
    simp only [z180K18M2FinalDPExcludedOrders, Finset.mem_insert,
      Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · have hprojected :
          cyclotomic 18 Int ∣ z180Projection36Mask A :=
        (cyclotomic_dvd_projection36Mask_iff_dvd_mask
          (m := 18) (by norm_num)).2 hqzero
      have hindicator :
          cyclotomic 18 Int ∣ projection36IndicatorMask b := by
        simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator]
          using hprojected
      exact projection36_phi18_remainders b
        (by simpa [projection36IndicatorMask] using hindicator)
    · have hmod18 :=
        cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
          (A := A) (m := 18) (by norm_num) (by norm_num)
            (by simpa using hqzero)
      have hz :=
        Z180K12HighOrder.projection36_phi18_remainders_zero_of_mod_five_dvd_high
          b hlo hhi hmod18
      simpa only [Z180K12HighOrder.projection36Phi18R0,
        Z180K12HighOrder.projection36Phi18R1,
        Z180K12HighOrder.projection36Phi18R2,
        Z180K12HighOrder.projection36Phi18R3,
        Z180K12HighOrder.projection36Phi18R4,
        Z180K12HighOrder.projection36Phi18R5] using hz
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ := hremainders

  let t0 : Int := b 0 + b 18 - 1
  let t1 : Int := b 10 + b 28 - 1
  let t2 : Int := b 2 + b 20 - 1
  let t3 : Int := b 12 + b 30 - 1
  let t4 : Int := b 4 + b 22 - 1
  let t5 : Int := b 14 + b 32 - 1
  let t6 : Int := b 6 + b 24 - 1
  let t7 : Int := b 16 + b 34 - 1
  let t8 : Int := b 8 + b 26 - 1

  -- `omega` instantiates the pointwise zero-one bounds occurring in the
  -- goal, but the complementary terms used through `hm6`--`hm8` are not
  -- goal subterms.  Keep those six bounds explicit at this finite frontier.
  have hb15lo : 0 ≤ b 15 := hlo 15
  have hb15hi : b 15 ≤ 1 := hhi 15
  have hb33lo : 0 ≤ b 33 := hlo 33
  have hb33hi : b 33 ≤ 1 := hhi 33
  have hb16lo : 0 ≤ b 16 := hlo 16
  have hb16hi : b 16 ≤ 1 := hhi 16
  have hb34lo : 0 ≤ b 34 := hlo 34
  have hb34hi : b 34 ≤ 1 := hhi 34
  have hb17lo : 0 ≤ b 17 := hlo 17
  have hb17hi : b 17 ≤ 1 := hhi 17
  have hb35lo : 0 ≤ b 35 := hlo 35
  have hb35hi : b 35 ≤ 1 := hhi 35

  have ht0lo : -1 ≤ t0 := by
    dsimp only [t0]
    omega
  have ht0hi : t0 ≤ 1 := by
    dsimp only [t0]
    omega
  have ht1lo : -1 ≤ t1 := by
    dsimp only [t1]
    omega
  have ht1hi : t1 ≤ 1 := by
    dsimp only [t1]
    omega
  have ht2lo : -1 ≤ t2 := by
    dsimp only [t2]
    omega
  have ht2hi : t2 ≤ 1 := by
    dsimp only [t2]
    omega

  have ht06 : t0 = t6 := by
    dsimp only [t0, t6]
    omega
  have ht36 : t3 = t6 := by
    dsimp only [t3, t6]
    omega
  have ht17 : t1 = t7 := by
    dsimp only [t1, t7]
    omega
  have ht47 : t4 = t7 := by
    dsimp only [t4, t7]
    omega
  have ht28 : t2 = t8 := by
    dsimp only [t2, t8]
    omega
  have ht58 : t5 = t8 := by
    dsimp only [t5, t8]
    omega

  have hR2base :
      z180K18ProjectionPhi2R0 b =
        2 * (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8) := by
    dsimp only [z180K18ProjectionPhi2R0,
      t0, t1, t2, t3, t4, t5, t6, t7, t8]
    omega
  have hR2 :
      z180K18ProjectionPhi2R0 b = 6 * (t0 + t1 + t2) := by
    rw [hR2base]
    omega

  have hmultiple : 6 * (t0 + t1 + t2) = 5 * k2 := by
    rw [← hR2, ← hcoeff2]
    exact hk2
  have hnonzero : 6 * (t0 + t1 + t2) ≠ 0 := by
    rw [← hR2, ← hcoeff2]
    exact hcoeff2ne
  omega

/-- Public `m = 2` envelope assembled from the closed final frontier. -/
theorem z180_k18_m2_envelope : Z180K18M2EnvelopeInterface :=
  z180_k18_m2_envelope_of_finalDP z180_k18_m2_finalDP

#print axioms z180_k18_m2_finalDP
#print axioms z180_k18_m2_envelope

end Fuglede
