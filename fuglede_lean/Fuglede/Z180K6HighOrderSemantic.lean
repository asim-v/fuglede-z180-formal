import Fuglede.Z180K6HighOrderArithmetic
import Fuglede.Z180K6ResiduePattern
import Fuglede.Z180K12Projection36Remainders3_12
import Fuglede.Z180K12Projection36Remainders36

/-!
# Semantic high-order exclusions in the cardinality-six defect branch

This module connects the small arithmetic kernels to genuine divisibility
of a `ZMod 180` mask.  The order-thirty-six exclusion additionally consumes
injectivity modulo 36, exactly where zero-one occupancy bounds are needed.
-/

namespace Fuglede

open Polynomial

/-- A cardinality-six `Phi_30` defect with no `Phi_6` factor rules out a
`Phi_12` factor. -/
theorem z180_not_phi12_dvd_of_k6_phi30_defect
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 X)
    (h6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 X) :
    ¬ cyclotomic 12 Int ∣ maskPolynomial 180 X := by
  let b : Fin 36 → Int := fun i => (z180Projection36Occupancy X i : Int)
  have hpattern : Z180K6ResidueSixPattern b := by
    exact z180_k6_projection_residue_pattern_of_phi30_defect X hcard h30 h6
  intro hmask
  have hprojected : cyclotomic 12 Int ∣ z180Projection36Mask X :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (by norm_num : 12 ∣ 36)).2 hmask
  rw [z180Projection36Mask_eq_sum_occupancy] at hprojected
  obtain ⟨h0, h1, h2, h3⟩ :=
    projection36_phi12_count12_remainders b hprojected
  change (b 0 + b 12 + b 24) - (b 4 + b 16 + b 28) -
    (b 6 + b 18 + b 30) + (b 10 + b 22 + b 34) = 0 at h0
  change (b 1 + b 13 + b 25) - (b 5 + b 17 + b 29) -
    (b 7 + b 19 + b 31) + (b 11 + b 23 + b 35) = 0 at h1
  change (b 2 + b 14 + b 26) + (b 4 + b 16 + b 28) -
    (b 8 + b 20 + b 32) - (b 10 + b 22 + b 34) = 0 at h2
  change (b 3 + b 15 + b 27) + (b 5 + b 17 + b 29) -
    (b 9 + b 21 + b 33) - (b 11 + b 23 + b 35) = 0 at h3
  apply z180_k6_phi12_count12_remainders_impossible b hpattern
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- A cardinality-six `Phi_30` defect with no `Phi_6` factor rules out a
`Phi_18` factor. -/
theorem z180_not_phi18_dvd_of_k6_phi30_defect
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 X)
    (h6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 X) :
    ¬ cyclotomic 18 Int ∣ maskPolynomial 180 X := by
  let b : Fin 36 → Int := fun i => (z180Projection36Occupancy X i : Int)
  have hpattern : Z180K6ResidueSixPattern b := by
    exact z180_k6_projection_residue_pattern_of_phi30_defect X hcard h30 h6
  intro hmask
  have hprojected : cyclotomic 18 Int ∣ z180Projection36Mask X :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (by norm_num : 18 ∣ 36)).2 hmask
  rw [z180Projection36Mask_eq_sum_occupancy] at hprojected
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    projection36_phi18_remainders b hprojected
  exact z180_k6_phi18_remainders_impossible b hpattern
    h0 h1 h2 h3 h4 h5

/-- Under injectivity of the reduction modulo 36, a cardinality-six
`Phi_30` defect with no `Phi_6` factor also rules out `Phi_36`. -/
theorem z180_not_phi36_dvd_of_k6_phi30_defect
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      (X : Set (ZMod 180)))
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 X)
    (h6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 X) :
    ¬ cyclotomic 36 Int ∣ maskPolynomial 180 X := by
  let b : Fin 36 → Int := fun i => (z180Projection36Occupancy X i : Int)
  have hpattern : Z180K6ResidueSixPattern b := by
    exact z180_k6_projection_residue_pattern_of_phi30_defect X hcard h30 h6
  have hzero : ∀ i, 0 ≤ b i := by
    intro i
    change 0 ≤ (z180Projection36Occupancy X i : Int)
    exact_mod_cast Nat.zero_le (z180Projection36Occupancy X i)
  have hone : ∀ i, b i ≤ 1 := by
    intro i
    change (z180Projection36Occupancy X i : Int) ≤ 1
    exact_mod_cast z180Projection36Occupancy_le_one_of_injOn hinj i
  intro hmask
  have hprojected : cyclotomic 36 Int ∣ z180Projection36Mask X :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (by norm_num : 36 ∣ 36)).2 hmask
  rw [z180Projection36Mask_eq_sum_occupancy] at hprojected
  obtain ⟨h0, h1, h2, h3, h4, h5, h6', h7, h8, h9, h10, h11⟩ :=
    projection36_phi36_remainders b hprojected
  exact z180_k6_phi36_remainders_impossible b hpattern hzero hone
    h0 h1 h2 h3 h4 h5 h6' h7 h8 h9 h10 h11

#print axioms z180_not_phi12_dvd_of_k6_phi30_defect
#print axioms z180_not_phi18_dvd_of_k6_phi30_defect
#print axioms z180_not_phi36_dvd_of_k6_phi30_defect

end Fuglede
