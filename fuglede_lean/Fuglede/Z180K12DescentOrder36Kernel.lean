import Fuglede.Z180K12DescentMixedKernelInterfaces
import Fuglede.Z180K12DescentDirectCommon
import Fuglede.Z180K12M6HighOrderRemainders36ZeroShard

/-! # Direct exclusion of base order thirty-six at cardinality twelve -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

/-- A `Phi_180/Phi_36` defect cannot occur once the projection to `ZMod 36`
is injective.  Each explicit projected remainder is a bounded multiple of
five, hence zero, and the resulting integral divisor lifts. -/
theorem z180_k12_descent_order36_kernel :
    Z180K12DescentOrder36Kernel := by
  intro A hcard hinj htransform2 htransform4 hhigh hlow
  rcases z180_k12_descent_projection_indicator_data
      hcard hinj htransform2 htransform4 with ⟨hloIndicator, hhiIndicator, _⟩
  have hmodFive := z180_k12_descent_high_to_projected_mod_five
    (A := A) (m := 36) (by norm_num) (by norm_num) hhigh
  have hremainders :=
    projection36_phi36_remainders_zero_of_mod_five_dvd_high
      (z180K12ProjectionIndicator A) hloIndicator hhiIndicator hmodFive
  have hprojected :=
    cyclotomic_thirtysix_dvd_projection36Indicator_of_remainders_zero_high
      (z180K12ProjectionIndicator A) hremainders
  exact z180_k12_descent_contradiction_of_projected_divisor
    (A := A) (m := 36) (by norm_num) hlow hprojected

#print axioms z180_k12_descent_order36_kernel

end Z180K12HighOrder

end Fuglede
