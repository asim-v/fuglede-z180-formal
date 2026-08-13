import Fuglede.Z180K12M6SemanticCommon

/-! # Lifting projected integral cyclotomic divisibility from `ZMod 36` -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

theorem projected_integer_divisor_lifts_high
    {A : Finset (ZMod 180)} {m : Nat} (hm36 : m ∣ 36)
    (hdiv : cyclotomic m Int ∣
      projection36IndicatorMask (z180K12ProjectionIndicator A)) :
    cyclotomic m Int ∣ maskPolynomial 180 A := by
  rw [projection36IndicatorMask_z180K12ProjectionIndicator] at hdiv
  exact (cyclotomic_dvd_projection36Mask_iff_dvd_mask hm36).1 hdiv

#print axioms projected_integer_divisor_lifts_high

end Z180K12HighOrder

end Fuglede
