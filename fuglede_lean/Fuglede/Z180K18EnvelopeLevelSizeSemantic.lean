import Fuglede.Z180K18EnvelopeResidualInterfaces
import Fuglede.Z180K18EnvelopeFiniteKernels
import Fuglede.Z180K18M12HighOrderLevels
import Fuglede.Z180K12M6Order20LevelDefs
import Fuglede.Z180ExactOrderTransform
import Mathlib.Tactic

/-!
# Table-free level-size exclusions for the cardinality-eighteen envelopes

This module realizes the semantic bridge behind the three entries labelled
"positive level-size arithmetic" in the external envelope audit:

* `(m,q) = (2,15)`;
* `(m,q) = (2,45)`;
* `(m,q) = (4,15)`.

The argument is uniform.  The `Phi_(5m)`/not-`Phi_m` defect makes all five
fifth-coordinate levels nonempty.  A simultaneous `Phi_r` and `Phi_(5r)`
zero, with `r=3` or `r=9`, makes every level cardinality divisible by three.
Finally `Phi_(5m)` makes all five cardinalities congruent modulo
`Phi_m(1)=2`.  Five positive multiples of three with the same parity cannot
sum to eighteen; the last step is
`z180_k18_five_level_sizes_impossible`.

No finite table, `native_decide`, or external certificate is used here.
-/

namespace Fuglede

open Polynomial
open scoped BigOperators

set_option maxHeartbeats 0

/-- Exact-order-three base frequency with zero fifth coordinate. -/
noncomputable def z180K18OrderThreeBaseFrequency : CRT180 :=
  toCRT180 (60 : ZMod 180)

/-- Exact-order-nine base frequency with zero fifth coordinate. -/
noncomputable def z180K18OrderNineBaseFrequency : CRT180 :=
  toCRT180 (20 : ZMod 180)

@[simp] theorem z180K18OrderThreeBaseFrequency_fifthCoord :
    crt180FifthCoord z180K18OrderThreeBaseFrequency = 0 := by
  change (ZMod.cast (60 : ZMod 180) : ZMod 5) = 0
  decide

@[simp] theorem z180K18OrderThreeBaseFrequency_order :
    frequencyOrder 180 (fromCRT180 z180K18OrderThreeBaseFrequency) = 3 := by
  rw [z180K18OrderThreeBaseFrequency, fromCRT180_toCRT180]
  decide

@[simp] theorem z180K18OrderNineBaseFrequency_fifthCoord :
    crt180FifthCoord z180K18OrderNineBaseFrequency = 0 := by
  change (ZMod.cast (20 : ZMod 180) : ZMod 5) = 0
  decide

@[simp] theorem z180K18OrderNineBaseFrequency_order :
    frequencyOrder 180 (fromCRT180 z180K18OrderNineBaseFrequency) = 9 := by
  rw [z180K18OrderNineBaseFrequency, fromCRT180_toCRT180]
  decide

/-- A zero of one fifth-level Fourier sum gives the corresponding
cyclotomic divisor of that level mask. -/
theorem z180_k18_cyclotomic_dvd_fifthLevelMask_of_fourier_zero
    (A : Finset (ZMod 180)) (u : CRT180) (c : ZMod 5) (r : Nat)
    (horder : frequencyOrder 180 (fromCRT180 u) = r)
    (hzero : z180FiveLevelFourierSum A u c = 0) :
    cyclotomic r Int ∣
      maskPolynomial 180 (z180K18M12FifthLevel A c) := by
  have hfourier :
      fourierSum (z180K18M12FifthLevel A c) (fromCRT180 u) = 0 := by
    rw [← z180K18M12_fiveLevelFourierSum_eq_fourierSum]
    exact hzero
  have hcyclo : CyclotomicZero 180
      (z180K18M12FifthLevel A c) (fromCRT180 u) :=
    (cyclotomicZero_iff_fourierSum_zero _ _).2 hfourier
  unfold CyclotomicZero at hcyclo
  rwa [horder] at hcyclo

/-- If both `Phi_r` and `Phi_(5r)` divide the full mask, then `Phi_r`
divides every fifth-coordinate level mask. -/
theorem z180_k18_fifthLevel_factor_of_low_and_five_mul
    (A : Finset (ZMod 180)) (u : CRT180) (c : ZMod 5) (r : Nat)
    (hu : crt180FifthCoord u = 0)
    (horder : frequencyOrder 180 (fromCRT180 u) = r)
    (hhigh : cyclotomic (r * 5) Int ∣ maskPolynomial 180 A)
    (hlow : cyclotomic r Int ∣ maskPolynomial 180 A) :
    cyclotomic r Int ∣
      maskPolynomial 180 (z180K18M12FifthLevel A c) := by
  have heq := z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
    A u r hu horder hhigh
  have hbaseCyclo : CyclotomicZero 180 A (fromCRT180 u) := by
    unfold CyclotomicZero
    rwa [horder]
  have hbaseFourier : fourierSum A (fromCRT180 u) = 0 :=
    (cyclotomicZero_iff_fourierSum_zero _ _).1 hbaseCyclo
  have hsum :
      (∑ d : ZMod 5, z180FiveLevelFourierSum A u d) = 0 := by
    rw [sum_z180FiveLevelFourierSum_eq,
      z180StandardCRTFourierSum_eq_fourierSum]
    exact hbaseFourier
  rw [sum_zmod_five_explicit_order20] at hsum
  rw [heq 0 c, heq 1 c, heq 2 c, heq 3 c, heq 4 c] at hsum
  have hc : z180FiveLevelFourierSum A u c = 0 := by
    have hfive :
        (5 : ℂ) * z180FiveLevelFourierSum A u c = 0 := by
      linear_combination hsum
    exact (mul_eq_zero.mp hfive).resolve_left (by norm_num)
  exact z180_k18_cyclotomic_dvd_fifthLevelMask_of_fourier_zero
    A u c r horder hc

/-- A five-factor defect makes every fifth-coordinate level positive. -/
theorem z180_k18_fifthFiberCard_pos_of_fiveFactorDefect
    (A : Finset (ZMod 180)) (u : CRT180) (m : Nat)
    (hu : crt180FifthCoord u = 0)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (hhigh : cyclotomic (m * 5) Int ∣ maskPolynomial 180 A)
    (hlow : ¬ cyclotomic m Int ∣ maskPolynomial 180 A) :
    ∀ c : ZMod 5, 0 < z180FifthFiberCard A c := by
  have hnonempty := z180FiveLevelsNonempty_of_cyclotomic_defect
    A u m hu horder hhigh hlow
  intro c
  obtain ⟨x, hx, hxc⟩ := hnonempty c
  change 0 <
    (A.filter fun y => crt180FifthCoord (toCRT180 y) = c).card
  exact Finset.card_pos.mpr
    ⟨x, Finset.mem_filter.mpr ⟨hx, hxc⟩⟩

/-- Evaluating the `Phi_(5m)` equality of two level Fourier sums at one
shows that their cardinalities differ by a multiple of `Phi_m(1)`.  This
specialized form records the only value used below, namely two. -/
theorem z180_k18_fifthFiberCard_sub_eq_two_mul_of_five_mul
    (A : Finset (ZMod 180)) (u : CRT180) (c c' : ZMod 5) (m : Nat)
    (hm : 0 < m)
    (hu : crt180FifthCoord u = 0)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (hhigh : cyclotomic (m * 5) Int ∣ maskPolynomial 180 A)
    (heval : Polynomial.eval (1 : Int) (cyclotomic m Int) = 2) :
    ∃ e : Int,
      (z180FifthFiberCard A c : Int) -
          (z180FifthFiberCard A c' : Int) = 2 * e := by
  have heq := z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
    A u m hu horder hhigh c c'
  have hdiv :=
    z180_k18_m12_cyclotomic_dvd_levelMask_sub_of_fourier_eq
      A u c c' m hm horder heq
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨Polynomial.eval 1 Q, ?_⟩
  have hEval := congrArg (Polynomial.eval (1 : Int)) hQ
  simpa [z180FifthFiberCard, z180K18M12FifthLevel,
    eval_one_maskPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, heval] using hEval

theorem z180_k18_eval_one_cyclotomic_two :
    Polynomial.eval (1 : Int) (cyclotomic 2 Int) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  convert (eval_one_cyclotomic_prime_pow
    (R := Int) (p := 2) 0) using 1 <;> norm_num

theorem z180_k18_eval_one_cyclotomic_four :
    Polynomial.eval (1 : Int) (cyclotomic 4 Int) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  convert (eval_one_cyclotomic_prime_pow
    (R := Int) (p := 2) 1) using 1 <;> norm_num

/-- Semantic wrapper around the common Presburger endpoint. -/
theorem z180_k18_five_level_sizes_impossible_of_data
    (A : Finset (ZMod 180)) (hcard : A.card = 18)
    (hpos : ∀ c : ZMod 5, 0 < z180FifthFiberCard A c)
    (hthree : ∀ c : ZMod 5, 3 ∣ z180FifthFiberCard A c)
    (hparity : ∀ c : ZMod 5, ∃ e : Int,
      (z180FifthFiberCard A c : Int) -
          (z180FifthFiberCard A 0 : Int) = 2 * e) :
    False := by
  obtain ⟨t0, ht0⟩ := hthree 0
  obtain ⟨t1, ht1⟩ := hthree 1
  obtain ⟨t2, ht2⟩ := hthree 2
  obtain ⟨t3, ht3⟩ := hthree 3
  obtain ⟨t4, ht4⟩ := hthree 4
  obtain ⟨e1, he1⟩ := hparity 1
  obtain ⟨e2, he2⟩ := hparity 2
  obtain ⟨e3, he3⟩ := hparity 3
  obtain ⟨e4, he4⟩ := hparity 4
  have hs0 : (0 : Int) < z180FifthFiberCard A 0 := by
    exact_mod_cast (hpos 0)
  have hs1 : (0 : Int) < z180FifthFiberCard A 1 := by
    exact_mod_cast (hpos 1)
  have hs2 : (0 : Int) < z180FifthFiberCard A 2 := by
    exact_mod_cast (hpos 2)
  have hs3 : (0 : Int) < z180FifthFiberCard A 3 := by
    exact_mod_cast (hpos 3)
  have hs4 : (0 : Int) < z180FifthFiberCard A 4 := by
    exact_mod_cast (hpos 4)
  have ht0' : (z180FifthFiberCard A 0 : Int) = 3 * (t0 : Int) := by
    exact_mod_cast ht0
  have ht1' : (z180FifthFiberCard A 1 : Int) = 3 * (t1 : Int) := by
    exact_mod_cast ht1
  have ht2' : (z180FifthFiberCard A 2 : Int) = 3 * (t2 : Int) := by
    exact_mod_cast ht2
  have ht3' : (z180FifthFiberCard A 3 : Int) = 3 * (t3 : Int) := by
    exact_mod_cast ht3
  have ht4' : (z180FifthFiberCard A 4 : Int) = 3 * (t4 : Int) := by
    exact_mod_cast ht4
  have hsumNat := sum_z180FifthFiberCard A
  rw [sum_zmod_five_explicit_order20, hcard] at hsumNat
  have hsum :
      (z180FifthFiberCard A 0 : Int) +
        z180FifthFiberCard A 1 + z180FifthFiberCard A 2 +
        z180FifthFiberCard A 3 + z180FifthFiberCard A 4 = 18 := by
    exact_mod_cast hsumNat
  exact z180_k18_five_level_sizes_impossible
    (z180FifthFiberCard A 0) (z180FifthFiberCard A 1)
    (z180FifthFiberCard A 2) (z180FifthFiberCard A 3)
    (z180FifthFiberCard A 4)
    t0 t1 t2 t3 t4 e1 e2 e3 e4
    hs0 hs1 hs2 hs3 hs4 ht0' ht1' ht2' ht3' ht4'
    he1 he2 he3 he4 hsum

/-- The `m=2` defect excludes `Phi_15` without a finite table. -/
theorem z180_k18_m2_not_phi15_of_level_sizes
    {A L : Finset (ZMod 180)}
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 2 A L) :
    ¬ cyclotomic 15 Int ∣ maskPolynomial 180 A := by
  intro h15
  obtain ⟨l1, hl1, l2, hl2, hne, hbase, horder,
    hhigh, hnotlow⟩ := hdefect
  have h10 : cyclotomic 10 Int ∣ maskPolynomial 180 A := by
    simpa using hhigh
  have hnot2 : ¬ cyclotomic 2 Int ∣ maskPolynomial 180 A := by
    simpa using hnotlow
  have hfreq60 : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
  have h3 : cyclotomic 3 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq60]
      using hcore.1
  have hpos : ∀ c : ZMod 5, 0 < z180FifthFiberCard A c :=
    z180_k18_fifthFiberCard_pos_of_fiveFactorDefect
      A z180K18M12OrderTwoBaseFrequency 2
      z180K18M12OrderTwoBaseFrequency_fifthCoord
      z180K18M12OrderTwoBaseFrequency_order (by simpa using h10) hnot2
  have hthree : ∀ c : ZMod 5, 3 ∣ z180FifthFiberCard A c := by
    intro c
    apply prime_dvd_card_of_cyclotomic_dvd_mask (by norm_num)
    exact z180_k18_fifthLevel_factor_of_low_and_five_mul
      A z180K18OrderThreeBaseFrequency c 3
      z180K18OrderThreeBaseFrequency_fifthCoord
      z180K18OrderThreeBaseFrequency_order (by simpa using h15) h3
  have hparity : ∀ c : ZMod 5, ∃ e : Int,
      (z180FifthFiberCard A c : Int) -
          (z180FifthFiberCard A 0 : Int) = 2 * e := by
    intro c
    exact z180_k18_fifthFiberCard_sub_eq_two_mul_of_five_mul
      A z180K18M12OrderTwoBaseFrequency c 0 2 (by norm_num)
      z180K18M12OrderTwoBaseFrequency_fifthCoord
      z180K18M12OrderTwoBaseFrequency_order (by simpa using h10)
      z180_k18_eval_one_cyclotomic_two
  exact z180_k18_five_level_sizes_impossible_of_data
    A hcard hpos hthree hparity

/-- The `m=2` defect excludes `Phi_45` without a finite table. -/
theorem z180_k18_m2_not_phi45_of_level_sizes
    {A L : Finset (ZMod 180)}
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 2 A L) :
    ¬ cyclotomic 45 Int ∣ maskPolynomial 180 A := by
  intro h45
  obtain ⟨l1, hl1, l2, hl2, hne, hbase, horder,
    hhigh, hnotlow⟩ := hdefect
  have h10 : cyclotomic 10 Int ∣ maskPolynomial 180 A := by
    simpa using hhigh
  have hnot2 : ¬ cyclotomic 2 Int ∣ maskPolynomial 180 A := by
    simpa using hnotlow
  have hfreq20 : frequencyOrder 180 (20 : ZMod 180) = 9 := by decide
  have h9 : cyclotomic 9 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq20]
      using hcore.2.1
  have hpos : ∀ c : ZMod 5, 0 < z180FifthFiberCard A c :=
    z180_k18_fifthFiberCard_pos_of_fiveFactorDefect
      A z180K18M12OrderTwoBaseFrequency 2
      z180K18M12OrderTwoBaseFrequency_fifthCoord
      z180K18M12OrderTwoBaseFrequency_order (by simpa using h10) hnot2
  have hthree : ∀ c : ZMod 5, 3 ∣ z180FifthFiberCard A c := by
    intro c
    change 3 ∣ (z180K18M12FifthLevel A c).card
    apply prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask
      (by norm_num) 1
    simpa using z180_k18_fifthLevel_factor_of_low_and_five_mul
      A z180K18OrderNineBaseFrequency c 9
      z180K18OrderNineBaseFrequency_fifthCoord
      z180K18OrderNineBaseFrequency_order (by simpa using h45) h9
  have hparity : ∀ c : ZMod 5, ∃ e : Int,
      (z180FifthFiberCard A c : Int) -
          (z180FifthFiberCard A 0 : Int) = 2 * e := by
    intro c
    exact z180_k18_fifthFiberCard_sub_eq_two_mul_of_five_mul
      A z180K18M12OrderTwoBaseFrequency c 0 2 (by norm_num)
      z180K18M12OrderTwoBaseFrequency_fifthCoord
      z180K18M12OrderTwoBaseFrequency_order (by simpa using h10)
      z180_k18_eval_one_cyclotomic_two
  exact z180_k18_five_level_sizes_impossible_of_data
    A hcard hpos hthree hparity

/-- The `m=4` defect excludes `Phi_15` without a finite table. -/
theorem z180_k18_m4_not_phi15_of_level_sizes
    {A L : Finset (ZMod 180)}
    (hcard : A.card = 18)
    (hcore : Z180K18CorePhi3Phi9Zeros A L)
    (hdefect : Z180K18FiveFactorDefectAt 4 A L) :
    ¬ cyclotomic 15 Int ∣ maskPolynomial 180 A := by
  intro h15
  obtain ⟨l1, hl1, l2, hl2, hne, hbase, horder,
    hhigh, hnotlow⟩ := hdefect
  have h20 : cyclotomic 20 Int ∣ maskPolynomial 180 A := by
    simpa using hhigh
  have hnot4 : ¬ cyclotomic 4 Int ∣ maskPolynomial 180 A := by
    simpa using hnotlow
  have hfreq60 : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
  have h3 : cyclotomic 3 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq60]
      using hcore.1
  have hpos : ∀ c : ZMod 5, 0 < z180FifthFiberCard A c :=
    z180_k18_fifthFiberCard_pos_of_fiveFactorDefect
      A z180OrderFourBaseFrequency 4
      z180OrderFourBaseFrequency_fifthCoord
      z180OrderFourBaseFrequency_order (by simpa using h20) hnot4
  have hthree : ∀ c : ZMod 5, 3 ∣ z180FifthFiberCard A c := by
    intro c
    apply prime_dvd_card_of_cyclotomic_dvd_mask (by norm_num)
    exact z180_k18_fifthLevel_factor_of_low_and_five_mul
      A z180K18OrderThreeBaseFrequency c 3
      z180K18OrderThreeBaseFrequency_fifthCoord
      z180K18OrderThreeBaseFrequency_order (by simpa using h15) h3
  have hparity : ∀ c : ZMod 5, ∃ e : Int,
      (z180FifthFiberCard A c : Int) -
          (z180FifthFiberCard A 0 : Int) = 2 * e := by
    intro c
    exact z180_k18_fifthFiberCard_sub_eq_two_mul_of_five_mul
      A z180OrderFourBaseFrequency c 0 4 (by norm_num)
      z180OrderFourBaseFrequency_fifthCoord
      z180OrderFourBaseFrequency_order (by simpa using h20)
      z180_k18_eval_one_cyclotomic_four
  exact z180_k18_five_level_sizes_impossible_of_data
    A hcard hpos hthree hparity

#print axioms z180_k18_cyclotomic_dvd_fifthLevelMask_of_fourier_zero
#print axioms z180_k18_fifthLevel_factor_of_low_and_five_mul
#print axioms z180_k18_fifthFiberCard_sub_eq_two_mul_of_five_mul
#print axioms z180_k18_m2_not_phi15_of_level_sizes
#print axioms z180_k18_m2_not_phi45_of_level_sizes
#print axioms z180_k18_m4_not_phi15_of_level_sizes

end Fuglede
