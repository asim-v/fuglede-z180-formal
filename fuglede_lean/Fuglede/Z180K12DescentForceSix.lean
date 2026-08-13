import Fuglede.Z180K12DescentDefect
import Fuglede.Z180K12DescentOrder3Kernel
import Fuglede.Z180K12DescentOrder9Kernel
import Fuglede.Z180K12DescentMixedKernelClosure
import Fuglede.Z180K12NonTilerM6FiveLevelBridge
import Mathlib.Tactic

/-!
# Every cardinality-twelve five-factor defect has base order six

The projected base order is a divisor of `36`.  Orders two and four are
already forced integral divisors by spectrality; orders three and nine are
the direct characteristic-five kernels; orders twelve, eighteen, and
thirty-six are the direct remainder-and-lift kernels.  Hence only order six
survives.
-/

namespace Fuglede

open Polynomial

private theorem z180_k12_descent_divisor_cases
    (m : Nat) (hmpos : 0 < m) (hm36 : m ∣ 36) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 9 ∨
      m = 12 ∨ m = 18 ∨ m = 36 := by
  have hmle : m ≤ 36 := Nat.le_of_dvd (by norm_num) hm36
  interval_cases m <;> norm_num at hm36 <;> simp

/-- A failed projected zero in a cardinality-twelve spectral pair is
exactly the `Phi_30`/not-`Phi_6` defect. -/
theorem z180_k12_phi30_defect_of_fiveFactorDefect
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 12)
    (hdefect : Z180K12Projection36FiveFactorDefect A L) :
    cyclotomic 30 Int ∣ maskPolynomial 180 A ∧
      ¬ cyclotomic 6 Int ∣ maskPolynomial 180 A := by
  obtain ⟨l1, hl1, l2, hl2, hne, hm36, hmgt, horderHigh,
    hhigh, hlow⟩ := hdefect
  let m : Nat := frequencyOrder 36
    (z180K12Projection36 l1 - z180K12Projection36 l2)
  change cyclotomic (5 * m) Int ∣ maskPolynomial 180 A at hhigh
  change ¬ cyclotomic m Int ∣ maskPolynomial 180 A at hlow
  have hinj := z180_k12_projection36_injOn_of_spectral hSpec hcard
  have hforced := z180_k12_forced_transform_zeros_of_spectral hSpec hcard
  have htransform2 := hforced.1
  have htransform4 := hforced.2.1
  have hmask2 : cyclotomic 2 Int ∣ maskPolynomial 180 A :=
    z180_cyclotomic_dvd_mask_of_transform_zero
      (A := A) (e := 2) (u := 90) (by norm_num) (by decide) htransform2
  have hmask4 : cyclotomic 4 Int ∣ maskPolynomial 180 A :=
    z180_cyclotomic_dvd_mask_of_transform_zero
      (A := A) (e := 4) (u := 45) (by norm_num) (by decide) htransform4
  have hmpos : 0 < m := by omega
  have hm6 : m = 6 := by
    rcases z180_k12_descent_divisor_cases m hmpos hm36 with
      h1 | h2 | h3 | h4 | h6 | h9 | h12 | h18 | h36
    · omega
    · exfalso
      apply hlow
      simpa [h2] using hmask2
    · exfalso
      apply Z180K12HighOrder.z180_k12_descent_order3_kernel
        A hcard hinj htransform2 htransform4
      · simpa [h3, Nat.mul_comm] using hhigh
      · simpa [h3] using hlow
    · exfalso
      apply hlow
      simpa [h4] using hmask4
    · exact h6
    · exfalso
      apply Z180K12HighOrder.z180_k12_descent_order9_kernel
        A hcard hinj htransform2 htransform4
      · simpa [h9, Nat.mul_comm] using hhigh
      · simpa [h9] using hlow
    · exfalso
      apply Z180K12HighOrder.z180_k12_descent_order12_kernel
        A hcard hinj htransform2 htransform4
      · simpa [h12, Nat.mul_comm] using hhigh
      · simpa [h12] using hlow
    · exfalso
      apply Z180K12HighOrder.z180_k12_descent_order18_kernel
        A hcard hinj htransform2 htransform4
      · simpa [h18, Nat.mul_comm] using hhigh
      · simpa [h18] using hlow
    · exfalso
      apply Z180K12HighOrder.z180_k12_descent_order36_kernel
        A hcard hinj htransform2 htransform4
      · simpa [h36, Nat.mul_comm] using hhigh
      · simpa [h36] using hlow
  constructor
  · simpa [hm6] using hhigh
  · simpa [hm6] using hlow

/-- The sole logical descent interface is now discharged directly from
spectrality and the proved cardinality-twelve theorem in `ZMod 36`. -/
theorem z180_k12_nonTiler_cyclotomicM6Reduction_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 12) :
    Z180K12NonTilerCyclotomicM6Reduction A := by
  intro hnot
  have hdefect := z180_k12_fiveFactorDefect_of_non_tiler
    hSpec hcard z36_spectral_card12_implies_tile hnot
  exact z180_k12_phi30_defect_of_fiveFactorDefect hSpec hcard hdefect

/-- Full five-level form consumed by the cardinality-twelve exact sieve. -/
theorem z180_k12_nonTilerM6Reduction_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 12) :
    Z180K12NonTilerM6Reduction A :=
  z180_k12_nonTilerM6Reduction_of_cyclotomic_reduction
    (z180_k12_nonTiler_cyclotomicM6Reduction_of_spectral hSpec hcard)

#print axioms z180_k12_phi30_defect_of_fiveFactorDefect
#print axioms z180_k12_nonTiler_cyclotomicM6Reduction_of_spectral
#print axioms z180_k12_nonTilerM6Reduction_of_spectral

end Fuglede
