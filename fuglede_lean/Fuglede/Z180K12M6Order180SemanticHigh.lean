import Fuglede.Z180K12M6HighOrderRemainders36ZeroShard
import Fuglede.Z180K12M6HighOrderProjectionLift
import Fuglede.Z180K12M6SemanticOrders
import Mathlib.Tactic

/-! # Set-level exclusion of cyclotomic order one hundred eighty at `k = 12` -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

set_option maxHeartbeats 0

theorem z180_k12_m6_not_cyclotomic_oneeighty_high
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 180 Int ∣ maskPolynomial 180 A := by
  intro h180
  obtain ⟨k0, k1, hlo, hhi, hmod4, h60, h61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hmod :=
    cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 36) (by norm_num) (by norm_num) (by simpa using h180)
  have hz := projection36_phi36_remainders_zero_of_mod_five_dvd_high _ hlo hhi hmod
  have hprojected :=
    cyclotomic_thirtysix_dvd_projection36Indicator_of_remainders_zero_high _ hz
  exact (z180_k12_m6_not_cyclotomic_thirtysix
    hcard hinj htransform2 htransform4 hdefect)
      (projected_integer_divisor_lifts_high (A := A) (by norm_num) hprojected)

#print axioms z180_k12_m6_not_cyclotomic_oneeighty_high

end Z180K12HighOrder

end Fuglede
