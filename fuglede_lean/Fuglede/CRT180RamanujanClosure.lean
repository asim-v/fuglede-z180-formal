import Fuglede.CRT180OrderFactorization
import Fuglede.CRT180Ramanujan

/-!
# Closing the Ramanujan identity at modulus 180

This module joins the two independent halves of the computation:

* `CRT180OrderFactorization` identifies a global exact-order frequency orbit
  with the product of its `4`, `9`, and `5` local orbits;
* `CRT180Ramanujan` computes the three local character kernels and identifies
  the generated integer transform with the corresponding pair kernel.

The result discharges `Z180RamanujanIdentity` for every finite subset of
`ZMod 180`.
-/

namespace Fuglede

open scoped BigOperators ComplexConjugate

private theorem z180_divisors_explicit_closure :
    (180).divisors =
      {1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} := by
  decide

set_option maxHeartbeats 0 in
private theorem z180LocalCharacterKernel_orderPart_coeff
    (z : CRT180) {e : Nat} (he : e ∈ (180).divisors) (i : Fin 3) :
    z180LocalCharacterKernel z i (crt180OrderPart e i) =
      (z180LocalRamanujanCoeff i (crt180OrderPart e i)
        (frequencyOrder (crt180Modulus i) (z i)) : ℂ) := by
  rw [z180_divisors_explicit_closure] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases i <;>
    simp only [crt180OrderPart] <;>
    norm_num [z180LocalRamanujanCoeff] <;>
    first
    | exact z180LocalCharacterKernel_four_one_coeff z
    | exact z180LocalCharacterKernel_four_two_coeff z
    | exact z180LocalCharacterKernel_four_four_coeff z
    | exact z180LocalCharacterKernel_nine_one_coeff z
    | exact z180LocalCharacterKernel_nine_three_coeff z
    | exact z180LocalCharacterKernel_nine_nine_coeff z
    | exact z180LocalCharacterKernel_five_one_coeff z
    | exact z180LocalCharacterKernel_five_five_coeff z

private theorem z180_prod_localCharacterKernel_eq_ramanujanCoeff
    (z : CRT180) {e : Nat} (he : e ∈ (180).divisors) :
    (∏ i, z180LocalCharacterKernel z i (crt180OrderPart e i)) =
      (z180RamanujanCoeff e
        (frequencyOrder 180 (fromCRT180 z)) : ℂ) := by
  have hr : frequencyOrder 180 (fromCRT180 z) ∈ (180).divisors :=
    Nat.mem_divisors.mpr
      ⟨frequencyOrder_dvd_modulus (fromCRT180 z), by norm_num⟩
  have hlocal :=
    (frequencyOrder_fromCRT180_eq_iff_local (d := z) hr).mp rfl
  calc
    (∏ i, z180LocalCharacterKernel z i (crt180OrderPart e i)) =
        ∏ i, (z180LocalRamanujanCoeff i (crt180OrderPart e i)
          (frequencyOrder (crt180Modulus i) (z i)) : ℂ) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact z180LocalCharacterKernel_orderPart_coeff z he i
    _ = (z180RamanujanCoeff e
        (frequencyOrder 180 (fromCRT180 z)) : ℂ) := by
      rw [Fin.prod_univ_three]
      simp only [z180LocalRamanujanCoeff]
      rw [hlocal 0, hlocal 1, hlocal 2]
      change
        (z180RamanujanFour (Nat.gcd e 4)
              (Nat.gcd (frequencyOrder 180 (fromCRT180 z)) 4) : ℂ) *
            (z180RamanujanNine (Nat.gcd e 9)
              (Nat.gcd (frequencyOrder 180 (fromCRT180 z)) 9) : ℂ) *
          (z180RamanujanFive (Nat.gcd e 5)
            (Nat.gcd (frequencyOrder 180 (fromCRT180 z)) 5) : ℂ) =
        ((z180RamanujanFour (Nat.gcd e 4)
              (Nat.gcd (frequencyOrder 180 (fromCRT180 z)) 4) *
            z180RamanujanNine (Nat.gcd e 9)
              (Nat.gcd (frequencyOrder 180 (fromCRT180 z)) 9) *
          z180RamanujanFive (Nat.gcd e 5)
            (Nat.gcd (frequencyOrder 180 (fromCRT180 z)) 5) : Int) : ℂ)
      push_cast
      rfl

/-- The character sum over one global exact-order orbit is its product
Ramanujan coefficient, evaluated at the order of the spatial difference. -/
theorem sum_exactCRTFrequencies180_standardCharacterPairing
    (z : CRT180) {e : Nat} (he : e ∈ (180).divisors) :
    ∑ d ∈ exactCRTFrequencies180 e,
        z180StandardCRTCharacterPairing z d =
      (z180RamanujanCoeff e
        (frequencyOrder 180 (fromCRT180 z)) : ℂ) := by
  classical
  rw [exactCRTFrequencies180_eq_piFinset he]
  calc
    (∑ d ∈ Fintype.piFinset (fun i ↦
          exactOrderFrequencies (N := crt180Modulus i)
            (crt180OrderPart e i)),
        z180StandardCRTCharacterPairing z d) =
        ∑ d ∈ Fintype.piFinset (fun i ↦
          exactOrderFrequencies (N := crt180Modulus i)
            (crt180OrderPart e i)),
          ∏ i, z180StandardCoordinateChar z i (d i) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact z180StandardCRTCharacterPairing_eq_prod z d
    _ = ∏ i, ∑ a ∈
          exactOrderFrequencies (N := crt180Modulus i)
            (crt180OrderPart e i),
          z180StandardCoordinateChar z i a := by
      exact (Finset.prod_univ_sum
        (fun i ↦ exactOrderFrequencies (N := crt180Modulus i)
          (crt180OrderPart e i))
        (fun i a ↦ z180StandardCoordinateChar z i a)).symm
    _ = ∏ i, z180LocalCharacterKernel z i (crt180OrderPart e i) := by
      rfl
    _ = (z180RamanujanCoeff e
        (frequencyOrder 180 (fromCRT180 z)) : ℂ) :=
      z180_prod_localCharacterKernel_eq_ramanujanCoeff z he

/-! ## Fourier energy and the integer pair kernel -/

/-- Complex Fourier energy over the CRT parametrization of one exact-order
frequency orbit. -/
noncomputable def z180CRTExactEnergyComplex
    (X : Finset (ZMod 180)) (e : Nat) : ℂ :=
  ∑ d ∈ exactCRTFrequencies180 e,
    z180StandardCRTFourierSum X d *
      star (z180StandardCRTFourierSum X d)

/-- Expanding each squared Fourier coefficient and interchanging the two
finite sums gives exactly the integer pair kernel. -/
theorem z180CRTExactEnergyComplex_eq_pairKernelSum
    (X : Finset (ZMod 180)) {e : Nat} (he : e ∈ (180).divisors) :
    z180CRTExactEnergyComplex X e = (z180PairKernelSum X e : ℂ) := by
  rw [z180CRTExactEnergyComplex]
  simp_rw [z180StandardCRTFourierSum_mul_star]
  calc
    (∑ d ∈ exactCRTFrequencies180 e,
        ∑ p ∈ X ×ˢ X,
          z180StandardCRTCharacterPairing
            (toCRT180 (p.1 - p.2)) d) =
        ∑ p ∈ X ×ˢ X,
          ∑ d ∈ exactCRTFrequencies180 e,
            z180StandardCRTCharacterPairing
              (toCRT180 (p.1 - p.2)) d := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ X ×ˢ X,
          (z180RamanujanCoeff e
            (frequencyOrder 180 (p.1 - p.2)) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      simpa only [fromCRT180_toCRT180] using
        (sum_exactCRTFrequencies180_standardCharacterPairing
          (toCRT180 (p.1 - p.2)) he)
    _ = (z180PairKernelSum X e : ℂ) := by
      rw [z180PairKernelSum]
      push_cast
      rfl

/-- Real-valued form: the integer pair kernel is the analytic exact-order
Fourier energy used by `Z180RamanujanIdentity`. -/
theorem z180PairKernelSum_cast_real_eq_exactOrderFourierEnergy
    (X : Finset (ZMod 180)) {e : Nat} (he : e ∈ (180).divisors) :
    (z180PairKernelSum X e : ℝ) = exactOrderFourierEnergy X e := by
  have hcomplex :
      (∑ d ∈ exactCRTFrequencies180 e,
          (Complex.normSq
            (fourierSum X (fromCRT180 d)) : ℂ)) =
        (z180PairKernelSum X e : ℂ) := by
    rw [← z180CRTExactEnergyComplex_eq_pairKernelSum X he]
    rw [z180CRTExactEnergyComplex]
    apply Finset.sum_congr rfl
    intro d hd
    rw [z180StandardCRTFourierSum_eq_fourierSum, mul_comm]
    exact Complex.normSq_eq_conj_mul_self
      (z := fourierSum X (fromCRT180 d))
  have hre := congrArg Complex.re hcomplex
  calc
    (z180PairKernelSum X e : ℝ) =
        ∑ d ∈ exactCRTFrequencies180 e,
          Complex.normSq (fourierSum X (fromCRT180 d)) := by
      simpa using hre.symm
    _ = exactOrderFourierEnergy X e := by
      rw [exactOrderFourierEnergy,
        ← map_exactCRTFrequencies180_fromCRT180 e]
      simp
      rfl

/-- The explicit integer transform is unconditionally the exact-order
Fourier energy at every divisor of `180`. -/
theorem z180RamanujanIdentity (X : Finset (ZMod 180)) :
    Z180RamanujanIdentity X := by
  intro e he
  rw [z180ExactOrderTransform_eq_pairKernelSum X he]
  exact z180PairKernelSum_cast_real_eq_exactOrderFourierEnergy X he

/-- Uniform endpoint, convenient for clients that need both sides of a
spectral pair. -/
theorem z180RamanujanIdentity_all :
    ∀ X : Finset (ZMod 180), Z180RamanujanIdentity X :=
  z180RamanujanIdentity

end Fuglede
