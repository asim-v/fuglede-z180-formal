import Fuglede.Z180K10Projection20Mixed
import Fuglede.Z180ModThreeCyclotomic
import Mathlib.Tactic

/-!
# Spectral differences and characteristic-three factors at cardinality ten

A difference of exact order `m` after projection modulo twenty lifts to an
order `m`, `3m`, or `9m` in `ZMod 180`.  Spectral duality supplies the
corresponding integer cyclotomic divisor of the spectrum mask, and the
characteristic-three bridge then supplies `Phi_m` in the projected mask.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- Removing the three-primary coordinate from an order in `ZMod 180`
leaves the order of its image in `ZMod 20`. -/
theorem z180_frequencyOrder_eq_projection20_order_or_three_or_nine
    (d : ZMod 180) :
    frequencyOrder 180 d =
        frequencyOrder 20 (z180K10Projection20 d) ∨
      frequencyOrder 180 d =
        3 * frequencyOrder 20 (z180K10Projection20 d) ∨
      frequencyOrder 180 d =
        9 * frequencyOrder 20 (z180K10Projection20 d) := by
  revert d
  set_option maxRecDepth 100000 in
    decide

/-- One exact difference order in the projected set forces the matching
cyclotomic factor in the characteristic-three projected spectrum mask. -/
theorem z180_k10_projection20_difference_order_forces_spectrum_factor
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    {m : Nat} (hm3 : ¬ 3 ∣ m) (hm20 : m ∣ 20)
    (horder : Z20K10HasDifferenceOrder
      (A.image z180K10Projection20) m) :
    cyclotomic m (ZMod 3) ∣ z180Projection20MaskModThree L := by
  rcases horder with ⟨x, hx, y, hy, hxy, hprojectedOrder⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := by
    intro h
    subst b
    exact hxy rfl
  have hzero : CyclotomicZero 180 L (a - b) :=
    (cyclotomicSpectrum_dual hSpec).2.2 a ha b hb hab
  have hprojectedOrder' :
      frequencyOrder 20 (z180K10Projection20 (a - b)) = m := by
    simpa only [map_sub] using hprojectedOrder
  have hindexCases :
      frequencyOrder 180 (a - b) = m ∨
        frequencyOrder 180 (a - b) = 3 * m ∨
        frequencyOrder 180 (a - b) = 9 * m := by
    have hindexCases' :=
      z180_frequencyOrder_eq_projection20_order_or_three_or_nine (a - b)
    rw [hprojectedOrder'] at hindexCases'
    exact hindexCases'
  apply cyclotomic_dvd_projection20MaskModThree_of_index_cases_dvd_mask
    hm3 hm20 hindexCases
  simpa [CyclotomicZero] using hzero

/-- The five difference orders forced by a mixed pair produce all five
nontrivial cyclotomic factors of `X^20 - 1` in the projected spectrum mask. -/
theorem z180_k10_all_projection20_spectrum_factors_of_all_difference_orders
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (horders :
      Z20K10HasDifferenceOrder (A.image z180K10Projection20) 2 ∧
      Z20K10HasDifferenceOrder (A.image z180K10Projection20) 4 ∧
      Z20K10HasDifferenceOrder (A.image z180K10Projection20) 5 ∧
      Z20K10HasDifferenceOrder (A.image z180K10Projection20) 10 ∧
      Z20K10HasDifferenceOrder (A.image z180K10Projection20) 20) :
    (cyclotomic 2 (ZMod 3) ∣ z180Projection20MaskModThree L) ∧
      (cyclotomic 4 (ZMod 3) ∣ z180Projection20MaskModThree L) ∧
      (cyclotomic 5 (ZMod 3) ∣ z180Projection20MaskModThree L) ∧
      (cyclotomic 10 (ZMod 3) ∣ z180Projection20MaskModThree L) ∧
      (cyclotomic 20 (ZMod 3) ∣ z180Projection20MaskModThree L) := by
  rcases horders with ⟨h2, h4, h5, h10, h20⟩
  exact ⟨
    z180_k10_projection20_difference_order_forces_spectrum_factor
      hSpec (by norm_num) (by norm_num) h2,
    z180_k10_projection20_difference_order_forces_spectrum_factor
      hSpec (by norm_num) (by norm_num) h4,
    z180_k10_projection20_difference_order_forces_spectrum_factor
      hSpec (by norm_num) (by norm_num) h5,
    z180_k10_projection20_difference_order_forces_spectrum_factor
      hSpec (by norm_num) (by norm_num) h10,
    z180_k10_projection20_difference_order_forces_spectrum_factor
      hSpec (by norm_num) (by norm_num) h20⟩

#print axioms z180_k10_all_projection20_spectrum_factors_of_all_difference_orders

end Fuglede
