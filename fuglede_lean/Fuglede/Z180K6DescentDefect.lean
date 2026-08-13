import Fuglede.Z180K6DescentImages
import Fuglede.Z180K12Projection36Mask
import Fuglede.FrequencyOrder
import Mathlib.Tactic

/-!
# A failed `180 -> 36` zero descent produces a five-factor defect

The order of a frequency in `ZMod 180` is either the order of its image in
`ZMod 36`, or five times that order.  Together with equality of the projected
and image masks (under the automatic injectivity gateway), this converts a
failed projected cyclotomic zero into an exact
`Phi_(5m)`/not-`Phi_m` defect with `m | 36`.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Under injectivity, reducing the exponents modulo 36 is exactly the mask
polynomial of the projected image. -/
theorem maskPolynomial_projection36_image_eq
    {A : Finset (ZMod 180)}
    (hinj : Set.InjOn z180K6Projection36 (A : Set (ZMod 180))) :
    maskPolynomial 36 (A.image z180K6Projection36) =
      z180Projection36Mask A := by
  classical
  rw [maskPolynomial, Finset.sum_image]
  · rw [z180Projection36Mask]
    apply Finset.sum_congr rfl
    intro x hx
    rw [monomial_one_right_eq_X_pow]
    congr 1
  · intro x hx y hy hxy
    exact hinj hx hy hxy

/-- Quotienting `ZMod 180` by its order-five kernel either preserves the
frequency order or removes exactly one factor of five. -/
theorem z180_frequencyOrder_projection36_cases (d : ZMod 180) :
    frequencyOrder 180 d = frequencyOrder 36 (z180K6Projection36 d) ∨
      frequencyOrder 180 d =
        5 * frequencyOrder 36 (z180K6Projection36 d) := by
  have hlt : d.val < 180 := d.val_lt
  unfold frequencyOrder
  rw [z180K6Projection36_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  interval_cases hv : d.val <;> norm_num [hv]

/-- Exact algebraic shape of one failed projected zero. -/
def Z180K6Projection36FiveFactorDefect
    (A L : Finset (ZMod 180)) : Prop :=
  ∃ l₁ ∈ L, ∃ l₂ ∈ L, l₁ ≠ l₂ ∧
    let m := frequencyOrder 36
      (z180K6Projection36 l₁ - z180K6Projection36 l₂)
    m ∣ 36 ∧ 1 < m ∧
      frequencyOrder 180 (l₁ - l₂) = 5 * m ∧
      cyclotomic (5 * m) Int ∣ maskPolynomial 180 A ∧
      ¬ cyclotomic m Int ∣ maskPolynomial 180 A

/-- A failure of exact zero descent is precisely strong enough to produce a
five-factor cyclotomic defect on the original mask. -/
theorem z180_k6_fiveFactorDefect_of_not_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hnotdesc : ¬ Z180K6Projection36ZeroDescends A L) :
    Z180K6Projection36FiveFactorDefect A L := by
  classical
  simp only [Z180K6Projection36ZeroDescends, not_forall,
    _root_.not_imp] at hnotdesc
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hnotzero⟩ := hnotdesc
  let d : ZMod 180 := l₁ - l₂
  let d36 : ZMod 36 := z180K6Projection36 l₁ - z180K6Projection36 l₂
  let m : Nat := frequencyOrder 36 d36
  have hinjL := z180_k6_projection36_spectrum_injOn hSpec hcard
  have hd36ne : d36 ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    exact hne (hinjL hl₁ hl₂ heq)
  have hmgt : 1 < m := by
    exact one_lt_frequencyOrder_of_ne_zero (by norm_num) hd36ne
  have hm36 : m ∣ 36 := by
    exact frequencyOrder_dvd_modulus d36
  have hinjA := z180_k6_projection36_injOn hSpec hcard
  have hnotlow : ¬ cyclotomic m Int ∣ maskPolynomial 180 A := by
    intro hlow
    apply hnotzero
    unfold CyclotomicZero
    change cyclotomic m Int ∣
      maskPolynomial 36 (A.image z180K6Projection36)
    rw [maskPolynomial_projection36_image_eq hinjA]
    exact (cyclotomic_dvd_projection36Mask_iff_dvd_mask hm36).2 hlow
  have horiginal : CyclotomicZero 180 A d :=
    hSpec.2.2 l₁ hl₁ l₂ hl₂ hne
  have hmap : z180K6Projection36 d = d36 := by
    simp [d, d36, map_sub]
  have horderCases := z180_frequencyOrder_projection36_cases d
  rw [hmap] at horderCases
  have horderHigh : frequencyOrder 180 d = 5 * m := by
    rcases horderCases with heq | heq
    · exfalso
      apply hnotlow
      simpa [CyclotomicZero, d, m, heq] using horiginal
    · exact heq
  have hhigh : cyclotomic (5 * m) Int ∣ maskPolynomial 180 A := by
    simpa [CyclotomicZero, d, horderHigh] using horiginal
  exact ⟨l₁, hl₁, l₂, hl₂, hne, hm36, hmgt,
    horderHigh, hhigh, hnotlow⟩

/-- Conditional non-tiler endpoint: the only smaller-modulus input is the
exact size-six theorem in `ZMod 36`. -/
theorem z180_k6_fiveFactorDefect_of_non_tiler
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hInduction : Z36SpectralCard6ImpliesTile)
    (hnot : ¬ ∃ B : Finset (ZMod 180), Tiles A B) :
    Z180K6Projection36FiveFactorDefect A L := by
  apply z180_k6_fiveFactorDefect_of_not_zero_descent hSpec hcard
  exact z180_k6_not_zero_descent_of_non_tiler
    hSpec hcard hInduction hnot

#print axioms maskPolynomial_projection36_image_eq
#print axioms z180_frequencyOrder_projection36_cases
#print axioms z180_k6_fiveFactorDefect_of_not_zero_descent
#print axioms z180_k6_fiveFactorDefect_of_non_tiler

end Fuglede
