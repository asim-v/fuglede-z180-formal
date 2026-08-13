import Fuglede.CRT180Ramanujan
import Fuglede.CRT180OrderFactorization
import Fuglede.ZModDFTSupport
import Mathlib.Tactic

/-!
# Fourier descent through the fifth CRT coordinate of `ZMod 180`

This module turns vanishing at the four nonzero frequencies in the `ZMod 5`
coordinate into equality of the five corresponding level sums.  It is the
kernel-checked Fourier-inversion core shared by the remaining `k = 6, 12, 18`
descent arguments.
-/

namespace Fuglede

open scoped BigOperators

/-- Insert a value into the fifth CRT coordinate.  Naming this specialised
map avoids dependent-type coercions around `Pi.single`. -/
def crt180FifthSingle (a : ZMod 5) : CRT180 :=
  Pi.single (2 : Fin 3) a

@[simp]
theorem crt180FifthSingle_apply_two (a : ZMod 5) :
    crt180FifthSingle a 2 = a := by
  simp [crt180FifthSingle]

@[simp]
theorem crt180FifthSingle_zero :
    crt180FifthSingle 0 = (0 : CRT180) := by
  funext i
  fin_cases i <;> simp [crt180FifthSingle] <;> rfl

/-- Read the fifth CRT coordinate with its simplified type. -/
def crt180FifthCoord (z : CRT180) : ZMod 5 :=
  z 2

@[simp]
theorem crt180FifthCoord_apply (z : CRT180) :
    crt180FifthCoord z = z 2 := rfl

@[simp]
theorem crt180FifthCoord_toCRT180 (x : ZMod 180) :
    crt180FifthCoord (toCRT180 x) = (ZMod.cast x : ZMod 5) := by
  change toCRT180 x 2 =
    (ZMod.cast x : ZMod (crt180Modulus (2 : Fin 3)))
  exact toCRT180_apply x 2

/-- A nonzero element of the prime cyclic fifth coordinate has order five. -/
theorem zmod5_frequencyOrder_eq_five_of_ne_zero
    {b : ZMod 5} (hb : b ≠ 0) :
    frequencyOrder 5 b = 5 := by
  have hdiv := frequencyOrder_dvd_modulus b
  have hone : 1 < frequencyOrder 5 b :=
    one_lt_frequencyOrder_of_ne_zero (by norm_num) hb
  exact (Nat.dvd_prime_two_le (by norm_num) (by omega)).mp hdiv

/-- Extending a base CRT frequency whose fifth coordinate is zero by a
nonzero fifth-coordinate frequency multiplies its order by five. -/
theorem frequencyOrder_fromCRT180_add_fifth
    (u : CRT180) (hu : crt180FifthCoord u = 0)
    {b : ZMod 5} (hb : b ≠ 0) :
    frequencyOrder 180 (fromCRT180 (u + crt180FifthSingle b)) =
      frequencyOrder 180 (fromCRT180 u) * 5 := by
  have hb5 : frequencyOrder 5 b = 5 :=
    zmod5_frequencyOrder_eq_five_of_ne_zero hb
  have h0 :
      frequencyOrder (crt180Modulus 0)
          ((u + crt180FifthSingle b) 0) =
        frequencyOrder (crt180Modulus 0) (u 0) := by
    congr 1
    change u 0 + 0 = u 0
    exact add_zero _
  have h1 :
      frequencyOrder (crt180Modulus 1)
          ((u + crt180FifthSingle b) 1) =
        frequencyOrder (crt180Modulus 1) (u 1) := by
    congr 1
    change u 1 + 0 = u 1
    exact add_zero _
  have h2 :
      frequencyOrder (crt180Modulus 2)
          ((u + crt180FifthSingle b) 2) = 5 := by
    change frequencyOrder 5 (crt180FifthCoord u + b) = 5
    rw [hu, zero_add, hb5]
  have h2zero :
      frequencyOrder (crt180Modulus 2) (u 2) = 1 := by
    change frequencyOrder 5 (crt180FifthCoord u) = 1
    rw [hu]
    exact (frequencyOrder_eq_one_iff (by norm_num) 0).2 rfl
  have h1' :
      frequencyOrder (crt180Modulus (Fin.succ 0))
          ((u + crt180FifthSingle b) (Fin.succ 0)) =
        frequencyOrder (crt180Modulus (Fin.succ 0)) (u (Fin.succ 0)) := by
    have hi : Fin.succ 0 = (1 : Fin 3) := by decide
    rw [hi]
    exact h1
  have h2' :
      frequencyOrder (crt180Modulus (Fin.succ (Fin.succ 0)))
          ((u + crt180FifthSingle b) (Fin.succ (Fin.succ 0))) = 5 := by
    have hi : Fin.succ (Fin.succ 0) = (2 : Fin 3) := by decide
    rw [hi]
    exact h2
  have h2zero' :
      frequencyOrder (crt180Modulus (Fin.succ (Fin.succ 0)))
          (u (Fin.succ (Fin.succ 0))) = 1 := by
    have hi : Fin.succ (Fin.succ 0) = (2 : Fin 3) := by decide
    rw [hi]
    exact h2zero
  rw [frequencyOrder_fromCRT180_eq_prod,
    frequencyOrder_fromCRT180_eq_prod]
  simp only [Fin.prod_univ_succ]
  rw [h0, h1', h2', h2zero']
  simp [Nat.mul_assoc]

/-- The third CRT idempotent is `36`: it is zero modulo `4` and `9`, and one
modulo `5`. -/
theorem fromCRT180_fifthSingle (a : ZMod 5) :
    fromCRT180 (crt180FifthSingle a) =
      (36 : ZMod 180) * (a.val : ZMod 180) := by
  apply toCRT180_injective
  rw [toCRT180_fromCRT180]
  funext i
  fin_cases i
  · change 0 =
      (ZMod.cast ((36 : ZMod 180) * (a.val : ZMod 180)) : ZMod 4)
    rw [ZMod.cast_mul (by norm_num : 4 ∣ 180)]
    have h36 : (ZMod.cast (36 : ZMod 180) : ZMod 4) = 0 := by
      decide
    rw [h36, zero_mul]
  · change 0 =
      (ZMod.cast ((36 : ZMod 180) * (a.val : ZMod 180)) : ZMod 9)
    rw [ZMod.cast_mul (by norm_num : 9 ∣ 180)]
    have h36 : (ZMod.cast (36 : ZMod 180) : ZMod 9) = 0 := by
      decide
    rw [h36, zero_mul]
  · change a =
      (ZMod.cast ((36 : ZMod 180) * (a.val : ZMod 180)) : ZMod 5)
    rw [ZMod.cast_mul (by norm_num : 5 ∣ 180)]
    have h36 : (ZMod.cast (36 : ZMod 180) : ZMod 5) = 1 := by
      decide
    rw [h36, one_mul]
    exact (ZMod.cast_cast_zmod_of_le (by norm_num : 5 ≤ 180) a).symm

/-- On the fifth CRT factor, the character inherited from `ZMod 180` is the
ordinary standard character of `ZMod 5`. -/
theorem stdAddChar_fromCRT180_fifthSingle (a : ZMod 5) :
    ZMod.stdAddChar (fromCRT180 (crt180FifthSingle a)) =
      ZMod.stdAddChar a := by
  rw [fromCRT180_fifthSingle]
  have hprod :
      (36 : ZMod 180) * (a.val : ZMod 180) =
        ((36 * (a.val : ℤ) : ℤ) : ZMod 180) := by
    push_cast
    rfl
  calc
    ZMod.stdAddChar ((36 : ZMod 180) * (a.val : ZMod 180)) =
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((36 * (a.val : ℤ) : ℤ) : ℂ)) / (180 : ℂ)) := by
          rw [hprod]
          exact ZMod.stdAddChar_coe (N := 180) (36 * (a.val : ℤ))
    _ = Complex.exp
        (2 * Real.pi * Complex.I * (((a.val : ℤ) : ℂ)) / (5 : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = ZMod.stdAddChar ((a.val : ℤ) : ZMod 5) := by
      symm
      exact ZMod.stdAddChar_coe (N := 5) (a.val : ℤ)
    _ = ZMod.stdAddChar a := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Adding a frequency in the fifth CRT coordinate multiplies the character
pairing by the ordinary `ZMod 5` character. -/
theorem z180StandardCRTCharacterPairing_add_piSingle_two
    (z u : CRT180) (b : ZMod 5) :
    z180StandardCRTCharacterPairing z
        (u + crt180FifthSingle b) =
      z180StandardCRTCharacterPairing z u *
        ZMod.stdAddChar (b * crt180FifthCoord z) := by
  have hmul :
      (u + crt180FifthSingle b) * z =
        u * z + crt180FifthSingle
          (b * crt180FifthCoord z) := by
    funext i
    fin_cases i
    · change (u 0 + 0) * z 0 = u 0 * z 0 + 0
      rw [add_zero, add_zero]
    · change (u 1 + 0) * z 1 = u 1 * z 1 + 0
      rw [add_zero, add_zero]
    · change (crt180FifthCoord u + b) * crt180FifthCoord z =
        crt180FifthCoord u * crt180FifthCoord z +
          b * crt180FifthCoord z
      exact add_mul (crt180FifthCoord u) b (crt180FifthCoord z)
  rw [z180StandardCRTCharacterPairing,
    z180StandardCRTCharacterPairing, hmul]
  change ZMod.stdAddChar
      (crt180AddEquiv.symm
        (u * z + crt180FifthSingle
          (b * crt180FifthCoord z))) = _
  rw [crt180AddEquiv.symm.map_add, AddChar.map_add_eq_mul]
  change ZMod.stdAddChar (fromCRT180 (u * z)) *
      ZMod.stdAddChar
        (fromCRT180 (crt180FifthSingle (b * crt180FifthCoord z))) = _
  rw [stdAddChar_fromCRT180_fifthSingle]

/-- Contribution of one fifth-coordinate fibre at a fixed base frequency.
The condition `u 2 = 0` is imposed only by the theorems using this definition;
keeping the definition total makes its finite-sum algebra simple. -/
noncomputable def z180FiveLevelFourierSum
    (X : Finset (ZMod 180)) (u : CRT180) (c : ZMod 5) : ℂ :=
  ∑ x ∈ X.filter (fun x ↦ crt180FifthCoord (toCRT180 x) = c),
    z180StandardCRTCharacterPairing (toCRT180 x) u

/-- Varying the fifth frequency is exactly the ordinary DFT of the five level
sums.  The minus sign matches Mathlib's convention for `ZMod.dft`. -/
theorem z180StandardCRTFourierSum_add_fifth_eq_dft
    (X : Finset (ZMod 180)) (u : CRT180) (b : ZMod 5) :
    z180StandardCRTFourierSum X (u + crt180FifthSingle (-b)) =
      ZMod.dft (z180FiveLevelFourierSum X u) b := by
  classical
  let coord : ZMod 180 → ZMod 5 :=
    fun x ↦ crt180FifthCoord (toCRT180 x)
  let weight : ZMod 180 → ℂ := fun x ↦
    z180StandardCRTCharacterPairing (toCRT180 x) u *
      ZMod.stdAddChar ((-b) * coord x)
  have hfiber :
      (∑ c : ZMod 5, ∑ x ∈ X.filter (fun x ↦ coord x = c), weight x) =
        ∑ x ∈ X, weight x := by
    simpa using Finset.sum_fiberwise X coord weight
  calc
    z180StandardCRTFourierSum X (u + crt180FifthSingle (-b)) =
        ∑ x ∈ X, weight x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [z180StandardCRTCharacterPairing_add_piSingle_two]
    _ = ∑ c : ZMod 5,
        ∑ x ∈ X.filter (fun x ↦ coord x = c), weight x := hfiber.symm
    _ = ∑ c : ZMod 5,
        ZMod.stdAddChar (-(c * b)) * z180FiveLevelFourierSum X u c := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [z180FiveLevelFourierSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hcoord : coord x = c := (Finset.mem_filter.mp hx).2
      simp only [weight]
      rw [hcoord]
      have harg : (-b) * c = -(c * b) := by ring
      rw [harg, mul_comm]
    _ = ZMod.dft (z180FiveLevelFourierSum X u) b := by
      rw [ZMod.dft_apply]
      simp only [smul_eq_mul]

/-- Summing the five level contributions recovers the base-frequency Fourier
sum. -/
theorem sum_z180FiveLevelFourierSum_eq
    (X : Finset (ZMod 180)) (u : CRT180) :
    (∑ c : ZMod 5, z180FiveLevelFourierSum X u c) =
      z180StandardCRTFourierSum X u := by
  have h := z180StandardCRTFourierSum_add_fifth_eq_dft X u 0
  rw [neg_zero, crt180FifthSingle_zero, add_zero,
    ZMod.dft_apply_zero] at h
  exact h.symm

/-- If the four nonzero fifth-coordinate frequency extensions vanish, all
five level sums at the base frequency are equal. -/
theorem z180FiveLevelFourierSum_eq_of_vanishing_extensions
    (X : Finset (ZMod 180)) (u : CRT180)
    (hzero : ∀ b : ZMod 5, b ≠ 0 →
      z180StandardCRTFourierSum X (u + crt180FifthSingle (-b)) = 0) :
    ∀ c c' : ZMod 5,
      z180FiveLevelFourierSum X u c =
        z180FiveLevelFourierSum X u c' := by
  apply eq_of_dft_eq_zero_off_zero (z180FiveLevelFourierSum X u)
  intro b hb
  rw [← z180StandardCRTFourierSum_add_fifth_eq_dft]
  exact hzero b hb

/-- Cyclotomic-zero form of the five-level descent. -/
theorem z180FiveLevelFourierSum_eq_of_cyclotomicZero_extensions
    (X : Finset (ZMod 180)) (u : CRT180)
    (hzero : ∀ b : ZMod 5, b ≠ 0 →
      CyclotomicZero 180 X
        (fromCRT180 (u + crt180FifthSingle (-b)))) :
    ∀ c c' : ZMod 5,
      z180FiveLevelFourierSum X u c =
        z180FiveLevelFourierSum X u c' := by
  apply z180FiveLevelFourierSum_eq_of_vanishing_extensions X u
  intro b hb
  rw [z180StandardCRTFourierSum_eq_fourierSum]
  exact (cyclotomicZero_iff_fourierSum_zero X _).1 (hzero b hb)

/-- A cyclotomic divisor at five times the base order supplies all four
nonzero fifth-coordinate extensions automatically. -/
theorem z180FiveLevelFourierSum_eq_of_cyclotomic_mul_five
    (X : Finset (ZMod 180)) (u : CRT180)
    (hu : crt180FifthCoord u = 0)
    (hdiv : Polynomial.cyclotomic
        (frequencyOrder 180 (fromCRT180 u) * 5) ℤ ∣
      maskPolynomial 180 X) :
    ∀ c c' : ZMod 5,
      z180FiveLevelFourierSum X u c =
        z180FiveLevelFourierSum X u c' := by
  apply z180FiveLevelFourierSum_eq_of_cyclotomicZero_extensions X u
  intro b hb
  unfold CyclotomicZero
  rw [frequencyOrder_fromCRT180_add_fifth u hu (neg_ne_zero.mpr hb)]
  exact hdiv

/-- Named-order form used by the concrete `Phi_(5m)` descent branches. -/
theorem z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
    (X : Finset (ZMod 180)) (u : CRT180) (m : Nat)
    (hu : crt180FifthCoord u = 0)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (hdiv : Polynomial.cyclotomic (m * 5) ℤ ∣ maskPolynomial 180 X) :
    ∀ c c' : ZMod 5,
      z180FiveLevelFourierSum X u c =
        z180FiveLevelFourierSum X u c' := by
  apply z180FiveLevelFourierSum_eq_of_cyclotomic_mul_five X u hu
  rwa [horder]

/-- In a genuine `Phi_(5m)`/not-`Phi_m` defect, the common level sum is
nonzero.  This is the exact analytic content needed before classifying the
five level cardinalities. -/
theorem z180FiveLevelFourierSum_ne_zero_of_cyclotomic_defect
    (X : Finset (ZMod 180)) (u : CRT180) (m : Nat)
    (hu : crt180FifthCoord u = 0)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (hhigh : Polynomial.cyclotomic (m * 5) ℤ ∣ maskPolynomial 180 X)
    (hlow : ¬ Polynomial.cyclotomic m ℤ ∣ maskPolynomial 180 X) :
    ∀ c : ZMod 5, z180FiveLevelFourierSum X u c ≠ 0 := by
  have heq := z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
    X u m hu horder hhigh
  have hbase : z180StandardCRTFourierSum X u ≠ 0 := by
    intro hzero
    apply hlow
    have hfourier : fourierSum X (fromCRT180 u) = 0 := by
      rw [← z180StandardCRTFourierSum_eq_fourierSum]
      exact hzero
    have hcyclo : CyclotomicZero 180 X (fromCRT180 u) :=
      (cyclotomicZero_iff_fourierSum_zero X _).2 hfourier
    unfold CyclotomicZero at hcyclo
    rwa [horder] at hcyclo
  intro c hc
  apply hbase
  rw [← sum_z180FiveLevelFourierSum_eq]
  apply Finset.sum_eq_zero
  intro c' hc'
  rw [heq c' c, hc]

/-- The defect therefore makes every fifth-coordinate fibre nonempty. -/
theorem z180FiveLevelsNonempty_of_cyclotomic_defect
    (X : Finset (ZMod 180)) (u : CRT180) (m : Nat)
    (hu : crt180FifthCoord u = 0)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (hhigh : Polynomial.cyclotomic (m * 5) ℤ ∣ maskPolynomial 180 X)
    (hlow : ¬ Polynomial.cyclotomic m ℤ ∣ maskPolynomial 180 X) :
    ∀ c : ZMod 5, ∃ x ∈ X, crt180FifthCoord (toCRT180 x) = c := by
  classical
  have hne := z180FiveLevelFourierSum_ne_zero_of_cyclotomic_defect
    X u m hu horder hhigh hlow
  intro c
  by_contra hnot
  have hempty :
      X.filter (fun x ↦ crt180FifthCoord (toCRT180 x) = c) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact hnot ⟨x, hx'.1, hx'.2⟩
  apply hne c
  unfold z180FiveLevelFourierSum
  rw [hempty]
  simp

/-! ## The concrete `Phi_30`/not-`Phi_6` branch -/

/-- Frequency `30` has order six and zero fifth coordinate. -/
noncomputable def z180OrderSixBaseFrequency : CRT180 :=
  toCRT180 (30 : ZMod 180)

@[simp]
theorem z180OrderSixBaseFrequency_fifthCoord :
    crt180FifthCoord z180OrderSixBaseFrequency = 0 := by
  change (ZMod.cast (30 : ZMod 180) : ZMod 5) = 0
  decide

@[simp]
theorem z180OrderSixBaseFrequency_order :
    frequencyOrder 180 (fromCRT180 z180OrderSixBaseFrequency) = 6 := by
  rw [z180OrderSixBaseFrequency, fromCRT180_toCRT180]
  decide

/-- `Phi_30` without `Phi_6` makes the five primitive-six level sums equal. -/
theorem z180_phi30_defect_fiveLevelSums_eq
    (X : Finset (ZMod 180))
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X) :
    ∀ c c' : ZMod 5,
      z180FiveLevelFourierSum X z180OrderSixBaseFrequency c =
        z180FiveLevelFourierSum X z180OrderSixBaseFrequency c' := by
  apply z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
    X z180OrderSixBaseFrequency 6
  · exact z180OrderSixBaseFrequency_fifthCoord
  · exact z180OrderSixBaseFrequency_order
  · simpa using h30

/-- In the same defect, every common primitive-six level sum is nonzero. -/
theorem z180_phi30_defect_fiveLevelSums_ne_zero
    (X : Finset (ZMod 180))
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    (h6 : ¬ Polynomial.cyclotomic 6 ℤ ∣ maskPolynomial 180 X) :
    ∀ c : ZMod 5,
      z180FiveLevelFourierSum X z180OrderSixBaseFrequency c ≠ 0 := by
  apply z180FiveLevelFourierSum_ne_zero_of_cyclotomic_defect
    X z180OrderSixBaseFrequency 6
  · exact z180OrderSixBaseFrequency_fifthCoord
  · exact z180OrderSixBaseFrequency_order
  · simpa using h30
  · exact h6

/-- Concrete set-level consequence used by both the size-six and size-twelve
branches: all five residue classes modulo five occur. -/
theorem z180_phi30_defect_fiveLevels_nonempty
    (X : Finset (ZMod 180))
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    (h6 : ¬ Polynomial.cyclotomic 6 ℤ ∣ maskPolynomial 180 X) :
    ∀ c : ZMod 5, ∃ x ∈ X, (ZMod.cast x : ZMod 5) = c := by
  have h := z180FiveLevelsNonempty_of_cyclotomic_defect
    X z180OrderSixBaseFrequency 6
      z180OrderSixBaseFrequency_fifthCoord
      z180OrderSixBaseFrequency_order (by simpa using h30) h6
  intro c
  obtain ⟨x, hx, hxc⟩ := h c
  refine ⟨x, hx, ?_⟩
  calc
    (ZMod.cast x : ZMod 5) = crt180FifthCoord (toCRT180 x) :=
      (crt180FifthCoord_toCRT180 x).symm
    _ = c := hxc

end Fuglede
