import Fuglede.Z180K18M6DPSemanticDefs

/-! Set-level construction of the common residual `m = 6` projection data. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def z180_k18_m6_dp_baseData
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 6 A L) :
    Z180K18M6DPBaseData (z180K12ProjectionIndicator A) := by
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
  have hfactorPair :
      cyclotomic 30 Int ∣ maskPolynomial 180 A ∧
        ¬ cyclotomic 6 Int ∣ maskPolynomial 180 A := by
    rcases hdefect with
      ⟨l1, hl1, l2, hl2, hne, hbase, horder, h30, hnot6⟩
    exact ⟨by simpa using h30, by simpa using hnot6⟩
  have h30 := hfactorPair.1
  have hnot6 := hfactorPair.2
  have hmod6 :=
    cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 6) (by norm_num) (by norm_num) (by simpa using h30)
  have hmultipliers := projection36_phi6_five_multipliers b hmod6
  let k60 : Int := Classical.choose hmultipliers
  have hmultipliers1 := Classical.choose_spec hmultipliers
  let k61 : Int := Classical.choose hmultipliers1
  have hks := Classical.choose_spec hmultipliers1
  have hnotIndicator :
      ¬ cyclotomic 6 Int ∣ projection36IndicatorMask b := by
    intro hind
    apply hnot6
    apply (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (m := 6) (by norm_num)).1
    simpa [b, projection36IndicatorMask_z180K12ProjectionIndicator] using hind
  have hphi6ne :
      Z180K18M6TwoRemaindersNonzero
        (projection36Phi6R0 b) (projection36Phi6R1 b) := by
    dsimp only [Z180K18M6TwoRemaindersNonzero]
    intro hz
    exact hnotIndicator
      ((projection36_phi6_dvd_iff_remainders_zero b).2 hz)
  change Z180K18M6DPBaseData b
  exact {
    lo := hlo
    hi := hhi
    mass0 := hm0
    mass1 := hm1
    mass2 := hm2
    mass3 := hm3
    mass4 := hm4
    mass5 := hm5
    mass6 := hm6
    mass7 := hm7
    mass8 := hm8
    k60 := k60
    k61 := k61
    mul60 := hks.1
    mul61 := hks.2
    nonzero := hphi6ne }

#print axioms z180_k18_m6_dp_baseData

end Fuglede
