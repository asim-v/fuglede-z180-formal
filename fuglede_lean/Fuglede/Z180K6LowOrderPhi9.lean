import Fuglede.Z180K6LowOrderArithmetic
import Fuglede.Z180K12Projection36Remainders

/-!
# Excluding an order-nine zero from the cardinality-six residue pattern

This is the typed polynomial adapter for the small arithmetic kernel.  It
turns genuine `Phi_9` divisibility of a `ZMod 180` mask into the six integral
remainder equations and derives a contradiction from the `(4,1,1)` pattern
of the projected occupancies modulo six.
-/

namespace Fuglede

open Polynomial

/-- A projected `(4,1,1)` residue pattern rules out `Phi_9` divisibility of
the original mask. -/
theorem z180_not_phi9_dvd_of_k6_projection_residue_pattern
    (X : Finset (ZMod 180))
    (hpattern : Z180K6ResidueSixPattern
      (fun i : Fin 36 => (z180Projection36Occupancy X i : Int))) :
    ¬ cyclotomic 9 Int ∣ maskPolynomial 180 X := by
  intro hmask
  have hprojected : cyclotomic 9 Int ∣ z180Projection36Mask X :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask
      (by norm_num : 9 ∣ 36)).2 hmask
  rw [z180Projection36Mask_eq_sum_occupancy] at hprojected
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    projection36_phi9_remainders
      (fun i : Fin 36 => (z180Projection36Occupancy X i : Int)) hprojected
  exact z180_k6_phi9_remainders_impossible
    (fun i : Fin 36 => (z180Projection36Occupancy X i : Int))
    hpattern h0 h1 h2 h3 h4 h5

#print axioms z180_not_phi9_dvd_of_k6_projection_residue_pattern

end Fuglede
