import Fuglede.Z180K12M6HighOrderCount12Adapter
import Fuglede.Z180K12M6Order60FinalKernel
import Mathlib.Tactic

/-! # Set-level exclusion of cyclotomic order sixty at `k = 12` -/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

set_option maxHeartbeats 0

private theorem order60_count_high_impossible
    (b : Fin 36 → Int) (k0 k1 t0 t1 t2 t3 : Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3)
    (hm0 : projection36Phi12R0 b = 5 * t0)
    (hm1 : projection36Phi12R1 b = 5 * t1)
    (hm2 : projection36Phi12R2 b = 5 * t2)
    (hm3 : projection36Phi12R3 b = 5 * t3)
    (h60 : projection36Phi6R0 b = 5 * k0)
    (h61 : projection36Phi6R1 b = 5 * k1)
    (hne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  obtain ⟨hp0, hp1, hp2, hp3⟩ := count12_mod4_high b hmod4
  obtain ⟨hs0, hs1⟩ := count12_phi6_high b k0 k1 h60 h61
  have hsne := hne
  rw [← hs0, ← hs1] at hsne
  apply z180_k12_m6_order60_count_impossible
    (projection36Count12 b 0) (projection36Count12 b 1)
    (projection36Count12 b 2) (projection36Count12 b 3)
    (projection36Count12 b 4) (projection36Count12 b 5)
    (projection36Count12 b 6) (projection36Count12 b 7)
    (projection36Count12 b 8) (projection36Count12 b 9)
    (projection36Count12 b 10) (projection36Count12 b 11)
    k0 k1 t0 t1 t2 t3
  all_goals first
    | exact count12_nonneg_high b hlo _
    | exact count12_le_three_high b hhi _
    | simpa [projection36Phi12R0] using hm0
    | simpa [projection36Phi12R1] using hm1
    | simpa [projection36Phi12R2] using hm2
    | simpa [projection36Phi12R3] using hm3
    | assumption

theorem z180_k12_m6_not_cyclotomic_sixty_high
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 60 Int ∣ maskPolynomial 180 A := by
  intro h60high
  obtain ⟨k0, k1, hlo, hhi, hmod4, h60, h61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hmod :=
    cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 12) (by norm_num) (by norm_num)
        (by simpa using h60high)
  obtain ⟨t0, t1, t2, t3, hm0, hm1, hm2, hm3⟩ :=
    projection36_phi12_five_multipliers_high _ hmod
  exact order60_count_high_impossible _ k0 k1 t0 t1 t2 t3
    hlo hhi hmod4 hm0 hm1 hm2 hm3 h60 h61 hne

#print axioms z180_k12_m6_not_cyclotomic_sixty_high

end Z180K12HighOrder

end Fuglede
