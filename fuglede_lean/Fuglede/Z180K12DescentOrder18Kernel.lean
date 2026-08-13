import Fuglede.Z180K12DescentMixedKernelInterfaces
import Fuglede.Z180K12DescentDirectCommon
import Fuglede.Z180K12M6HighOrderRemainders18Shard

/-! # Direct exclusion of base order eighteen at cardinality twelve -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

/-- A `Phi_90/Phi_18` defect cannot occur once the projection to `ZMod 36`
is injective.  Characteristic five first forces all six bounded projected
remainders to vanish; integral divisibility then lifts to the original mask. -/
theorem z180_k12_descent_order18_kernel :
    Z180K12DescentOrder18Kernel := by
  intro A hcard hinj htransform2 htransform4 hhigh hlow
  rcases z180_k12_descent_projection_indicator_data
      hcard hinj htransform2 htransform4 with ⟨hloIndicator, hhiIndicator, _⟩
  have hmodFive := z180_k12_descent_high_to_projected_mod_five
    (A := A) (m := 18) (by norm_num) (by norm_num) hhigh
  have hremainders :=
    projection36_phi18_remainders_zero_of_mod_five_dvd_high
      (z180K12ProjectionIndicator A) hloIndicator hhiIndicator hmodFive
  have hprojected :=
    cyclotomic_eighteen_dvd_projection36Indicator_of_remainders_zero_high
      (z180K12ProjectionIndicator A) hremainders
  exact z180_k12_descent_contradiction_of_projected_divisor
    (A := A) (m := 18) (by norm_num) hlow hprojected

#print axioms z180_k12_descent_order18_kernel

end Z180K12HighOrder

end Fuglede
