import Fuglede.Z180K12DescentMixedKernelInterfaces
import Fuglede.Z180K12DescentDirectCommon
import Fuglede.Z180K12M6HighOrderRemainders9Shard

/-! # Direct exclusion of base order nine at cardinality twelve -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

/-- A `Phi_45/Phi_9` defect cannot occur.  Characteristic five forces all
six bounded projected remainders to vanish, so integral `Phi_9` divisibility
lifts back to the original mask. -/
theorem z180_k12_descent_order9_kernel :
    Z180K12DescentOrderKernel 9 := by
  intro A hcard hinj htransform2 htransform4 hhigh hlow
  rcases z180_k12_descent_projection_indicator_data
      hcard hinj htransform2 htransform4 with ⟨hlo, hhi, _⟩
  have hmodFive := z180_k12_descent_high_to_projected_mod_five
    (A := A) (m := 9) (by norm_num) (by norm_num) hhigh
  have hremainders :=
    projection36_phi9_remainders_zero_of_mod_five_dvd_high
      (z180K12ProjectionIndicator A) hlo hhi hmodFive
  have hprojected :=
    cyclotomic_nine_dvd_projection36Indicator_of_remainders_zero_high
      (z180K12ProjectionIndicator A) hremainders
  exact z180_k12_descent_contradiction_of_projected_divisor
    (A := A) (m := 9) (by norm_num) hlow hprojected

#print axioms z180_k12_descent_order9_kernel

end Z180K12HighOrder

end Fuglede
