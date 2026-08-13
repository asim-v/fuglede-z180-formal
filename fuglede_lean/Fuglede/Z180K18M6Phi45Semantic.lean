import Fuglede.Z180K18M6Phi45Arithmetic
import Fuglede.Z180K18M6EnvelopeInterfaces
import Fuglede.Z180K18EnvelopeLevelSizeSemantic
import Fuglede.Z180K18M12PairFibresHighOrderCombinatorial
import Mathlib.Tactic

/-!
# Semantic closure of the `k = 18`, `m = 6`, `q = 45` frontier

This is the primitive-six analogue of the structural base-order-twelve
certificate.  Four size-three `Phi_9` levels must share one primitive-six
signature under `Phi_30`; the three possible signature types are disjoint,
so the four levels would overfill a global modulo-nine fibre of mass two.
-/

namespace Fuglede

open Polynomial
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem z180_k18_m6_sum_level_nineFiberMass
    (A : Finset (ZMod 180)) (r : ZMod 9) :
    (∑ c : ZMod 5,
      z180K18M12NineFiberMass (z180K18M12LevelIndicator A c) r) =
      z180K18M12NineFiberMass (z180K12ProjectionIndicator A) r := by
  classical
  calc
    (∑ c : ZMod 5,
        z180K18M12NineFiberMass (z180K18M12LevelIndicator A c) r) =
        ∑ c : ZMod 5, (∑ i ∈ z180K18M12NineFiberIndices r,
          z180K18M12LevelIndicator A c i) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (sum_z180K18M12NineFiberIndices
        (z180K18M12LevelIndicator A c) r).symm
    _ = ∑ i ∈ z180K18M12NineFiberIndices r,
        ∑ c : ZMod 5, z180K18M12LevelIndicator A c i := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ z180K18M12NineFiberIndices r,
        z180K12ProjectionIndicator A i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_z180K18M12LevelIndicator A i
    _ = z180K18M12NineFiberMass
        (z180K12ProjectionIndicator A) r :=
      sum_z180K18M12NineFiberIndices (z180K12ProjectionIndicator A) r

theorem z180_k18_m6_not_phi45_structural
    {A L : Finset (ZMod 180)}
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 6 A L) :
    ¬ cyclotomic 45 Int ∣ maskPolynomial 180 A := by
  intro h45
  obtain ⟨l₁, hl₁, l₂, hl₂, hlne, hbase, horder,
    hhigh, hnotlow⟩ := hdefect
  have h30 : cyclotomic 30 Int ∣ maskPolynomial 180 A := by
    simpa using hhigh
  have hnot6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 A := by
    simpa using hnotlow
  have hfreq60 : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
  have hfreq20 : frequencyOrder 180 (20 : ZMod 180) = 9 := by decide
  have h3 : cyclotomic 3 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq60]
      using hcore.1
  have h9 : cyclotomic 9 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq20]
      using hcore.2.1
  have hpos : ∀ c : ZMod 5, 0 < z180FifthFiberCard A c :=
    z180_k18_fifthFiberCard_pos_of_fiveFactorDefect
      A z180OrderSixBaseFrequency 6
      z180OrderSixBaseFrequency_fifthCoord
      z180OrderSixBaseFrequency_order (by simpa using h30) hnot6
  have hlevelPhi9 : ∀ c : ZMod 5,
      cyclotomic 9 Int ∣
        maskPolynomial 180 (z180K18M12FifthLevel A c) := by
    intro c
    exact z180_k18_fifthLevel_factor_of_low_and_five_mul
      A z180K18OrderNineBaseFrequency c 9
      z180K18OrderNineBaseFrequency_fifthCoord
      z180K18OrderNineBaseFrequency_order (by simpa using h45) h9
  have hthree : ∀ c : ZMod 5, 3 ∣ z180FifthFiberCard A c := by
    intro c
    change 3 ∣ (z180K18M12FifthLevel A c).card
    apply prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask
      (by norm_num) 1
    exact hlevelPhi9 c
  have hlevelProjectedPhi9 : ∀ c : ZMod 5,
      cyclotomic 9 Int ∣
        projection36IndicatorMask (z180K18M12LevelIndicator A c) := by
    intro c
    have hp : cyclotomic 9 Int ∣
        z180Projection36Mask (z180K18M12FifthLevel A c) :=
      (cyclotomic_dvd_projection36Mask_iff_dvd_mask
        (m := 9) (by norm_num)).2 (hlevelPhi9 c)
    simpa [z180K18M12LevelIndicator,
      projection36IndicatorMask_z180K12ProjectionIndicator] using hp
  have hprofile : ∀ c : ZMod 5,
      z180FifthFiberCard A c = 3 →
      ∃ t : Fin 3, Z180K18M6Phi45SingletonProfile
        (z180K18M12LevelIndicator A c) t := by
    intro c hc
    apply z180_k18_m6_phi45_singletonProfile_of_phi9
    · intro i
      exact z180K12ProjectionIndicator_nonneg
        (z180K18M12FifthLevel A c) i
    · rw [z180K18M12LevelIndicator,
        sum_z180K12ProjectionIndicator]
      have hc' : (z180K18M12FifthLevel A c).card = 3 := by
        simpa [z180FifthFiberCard, z180K18M12FifthLevel] using hc
      rw [hc']
      norm_num
    · exact hlevelProjectedPhi9 c
  have hsame : ∀ c c' : ZMod 5,
      Z180K18M6Phi45SameSignature
        (z180K18M12LevelIndicator A c)
        (z180K18M12LevelIndicator A c') := by
    intro c c'
    have hdiv := z180_k18_m12_level_sub_dvd_of_five_mul
      A z180OrderSixBaseFrequency c c' 6
      (by norm_num) (by norm_num)
      z180OrderSixBaseFrequency_fifthCoord
      z180OrderSixBaseFrequency_order (by simpa using h30)
    exact z180_k18_m6_phi45_sameSignature_of_phi6_sub_dvd
      (z180K18M12LevelIndicator A c)
      (z180K18M12LevelIndicator A c') hdiv
  have hlevelMassNonneg : ∀ c : ZMod 5, ∀ r : ZMod 9,
      0 ≤ z180K18M12NineFiberMass
        (z180K18M12LevelIndicator A c) r := by
    intro c
    apply z180_k18_m12_nineFiberMass_nonneg
    intro i
    exact z180K12ProjectionIndicator_nonneg
      (z180K18M12FifthLevel A c) i
  have hnine :=
    z180_k18_m12_nineFibres_card_two_of_phi3_phi9 A hcard h3 h9
  have hglobal0 :=
    z180_k18_m12_projection_mass_two_of_card_two A hnine
  have hglobal : ∀ r : ZMod 9,
      z180K18M12NineFiberMass
        (z180K12ProjectionIndicator A) r = 2 := by
    simpa [Z180K18M12ProjectionNineFibresHaveMassTwo] using hglobal0
  have hmassCanonical : ∀ r : ZMod 9,
      z180K18M12NineFiberMass (z180K18M12LevelIndicator A 0) r +
          z180K18M12NineFiberMass (z180K18M12LevelIndicator A 1) r +
          z180K18M12NineFiberMass (z180K18M12LevelIndicator A 2) r +
          z180K18M12NineFiberMass (z180K18M12LevelIndicator A 3) r +
          z180K18M12NineFiberMass (z180K18M12LevelIndicator A 4) r =
        z180K18M12NineFiberMass (z180K12ProjectionIndicator A) r := by
    intro r
    have h := z180_k18_m6_sum_level_nineFiberMass A r
    rw [sum_zmod_five_explicit_order20] at h
    exact h
  have himpossible
      (c0 c1 c2 c3 c4 : ZMod 5)
      (hc0 : z180FifthFiberCard A c0 = 3)
      (hc1 : z180FifthFiberCard A c1 = 3)
      (hc2 : z180FifthFiberCard A c2 = 3)
      (hc3 : z180FifthFiberCard A c3 = 3)
      (hmassSum : ∀ r : ZMod 9,
        z180K18M12NineFiberMass (z180K18M12LevelIndicator A c0) r +
            z180K18M12NineFiberMass (z180K18M12LevelIndicator A c1) r +
            z180K18M12NineFiberMass (z180K18M12LevelIndicator A c2) r +
            z180K18M12NineFiberMass (z180K18M12LevelIndicator A c3) r +
            z180K18M12NineFiberMass (z180K18M12LevelIndicator A c4) r =
          z180K18M12NineFiberMass (z180K12ProjectionIndicator A) r) : False := by
    exact z180_k18_m6_phi45_four_singletons_impossible
      (z180K18M12LevelIndicator A c0)
      (z180K18M12LevelIndicator A c1)
      (z180K18M12LevelIndicator A c2)
      (z180K18M12LevelIndicator A c3)
      (z180K18M12LevelIndicator A c4)
      (z180K12ProjectionIndicator A)
      (hprofile c0 hc0) (hprofile c1 hc1)
      (hprofile c2 hc2) (hprofile c3 hc3)
      (hsame c0 c1) (hsame c0 c2) (hsame c0 c3)
      (hlevelMassNonneg c4) hmassSum hglobal
  obtain ⟨t0, ht0⟩ := hthree 0
  obtain ⟨t1, ht1⟩ := hthree 1
  obtain ⟨t2, ht2⟩ := hthree 2
  obtain ⟨t3, ht3⟩ := hthree 3
  obtain ⟨t4, ht4⟩ := hthree 4
  have hsum := sum_z180FifthFiberCard A
  rw [sum_zmod_five_explicit_order20, hcard] at hsum
  have hcases := z180_k18_m12_phi45_level_size_cases
    (z180FifthFiberCard A 0) (z180FifthFiberCard A 1)
    (z180FifthFiberCard A 2) (z180FifthFiberCard A 3)
    (z180FifthFiberCard A 4) t0 t1 t2 t3 t4
    (hpos 0) (hpos 1) (hpos 2) (hpos 3) (hpos 4)
    ht0 ht1 ht2 ht3 ht4 hsum
  rcases hcases with
    ⟨hs0, hs1, hs2, hs3, hs4⟩ |
    ⟨hs0, hs1, hs2, hs3, hs4⟩ |
    ⟨hs0, hs1, hs2, hs3, hs4⟩ |
    ⟨hs0, hs1, hs2, hs3, hs4⟩ |
    ⟨hs0, hs1, hs2, hs3, hs4⟩
  · apply himpossible 1 2 3 4 0 hs1 hs2 hs3 hs4
    intro r
    have h := hmassCanonical r
    linear_combination h
  · apply himpossible 0 2 3 4 1 hs0 hs2 hs3 hs4
    intro r
    have h := hmassCanonical r
    linear_combination h
  · apply himpossible 0 1 3 4 2 hs0 hs1 hs3 hs4
    intro r
    have h := hmassCanonical r
    linear_combination h
  · apply himpossible 0 1 2 4 3 hs0 hs1 hs2 hs4
    intro r
    have h := hmassCanonical r
    linear_combination h
  · apply himpossible 0 1 2 3 4 hs0 hs1 hs2 hs3
    exact hmassCanonical

theorem z180_k18_m6_phi45_envelope :
    Z180K18M6Phi45EnvelopeInterface := by
  intro A L hSpec hcard hcore hdefect
  exact z180_k18_m6_not_phi45_structural hcard hcore hdefect

#print axioms z180_k18_m6_sum_level_nineFiberMass
#print axioms z180_k18_m6_not_phi45_structural
#print axioms z180_k18_m6_phi45_envelope

end Fuglede
