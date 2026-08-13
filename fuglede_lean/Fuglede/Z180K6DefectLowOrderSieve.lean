import Fuglede.Z180K6LowOrderPhi23Compact
import Fuglede.Z180K6LowOrderPhi9

/-!
# Low-order zero sieve in the cardinality-six defect branch

The `Phi_30`/not-`Phi_6` normal form gives an exact `(4,1,1)` residue
pattern modulo six.  The compact polynomial adapters then rule out genuine
mask factors `Phi_2`, `Phi_3`, and `Phi_9`.
-/

namespace Fuglede

open Polynomial

/-- The three low orders dividing `36` cannot occur as Fourier-zero orders
in the cardinality-six `Phi_30` defect branch. -/
theorem z180_k6_defect_low_order_sieve
    (X : Finset (ZMod 180)) (hcard : X.card = 6)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 X)
    (h6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 X) :
    (¬ cyclotomic 2 Int ∣ maskPolynomial 180 X) ∧
      (¬ cyclotomic 3 Int ∣ maskPolynomial 180 X) ∧
      (¬ cyclotomic 9 Int ∣ maskPolynomial 180 X) := by
  have hpattern :=
    z180_k6_projection_residue_pattern_of_phi30_defect X hcard h30 h6
  exact ⟨
    z180_not_phi2_dvd_of_k6_projection_residue_pattern_compact X hpattern,
    z180_not_phi3_dvd_of_k6_projection_residue_pattern_compact X hpattern,
    z180_not_phi9_dvd_of_k6_projection_residue_pattern X hpattern⟩

#print axioms z180_k6_defect_low_order_sieve

end Fuglede
