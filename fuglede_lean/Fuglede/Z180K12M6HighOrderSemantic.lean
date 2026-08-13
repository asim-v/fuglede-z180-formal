import Fuglede.Z180K12M6HighOrderRemainders
import Fuglede.Z180K12M6Order15Omega
import Fuglede.Z180K12M6Order60Omega
import Fuglede.Z180K12M6SemanticOrders
import Fuglede.Z180K12M6SemanticOrders3_12
import Mathlib.Tactic

/-!
# Set-level exclusion of orders 15, 45, 60, 90, and 180

These are consequences of the global characteristic-five projection.  The
order-twenty branch is intentionally separate: `Phi_4` is already forced,
so its mapped remainder supplies no contradiction and needs the fibre DP.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

private theorem count12_nonneg_high
    (b : Fin 36 → Int) (hlo : ∀ i, 0 ≤ b i) (r : Fin 12) :
    0 ≤ projection36Count12 b r := by
  rw [projection36Count12]
  linarith only [hlo ⟨r.val, by omega⟩,
    hlo ⟨r.val + 12, by omega⟩, hlo ⟨r.val + 24, by omega⟩]

private theorem count12_le_three_high
    (b : Fin 36 → Int) (hhi : ∀ i, b i ≤ 1) (r : Fin 12) :
    projection36Count12 b r ≤ 3 := by
  rw [projection36Count12]
  linarith only [hhi ⟨r.val, by omega⟩,
    hhi ⟨r.val + 12, by omega⟩, hhi ⟨r.val + 24, by omega⟩]

private theorem count12_mod4_high
    (b : Fin 36 → Int)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3) :
    projection36Count12 b 0 + projection36Count12 b 4 +
        projection36Count12 b 8 = 3 ∧
    projection36Count12 b 1 + projection36Count12 b 5 +
        projection36Count12 b 9 = 3 ∧
    projection36Count12 b 2 + projection36Count12 b 6 +
        projection36Count12 b 10 = 3 ∧
    projection36Count12 b 3 + projection36Count12 b 7 +
        projection36Count12 b 11 = 3 := by
  rcases hmod4 with ⟨h0, h1, h2, h3⟩
  dsimp only [projection36Count12]
  norm_num
  constructor
  · linarith only [h0]
  constructor
  · linarith only [h1]
  constructor
  · linarith only [h2]
  · linarith only [h3]

private theorem count12_phi6_high
    (b : Fin 36 → Int) (k0 k1 : Int)
    (h0 : projection36Phi6R0 b = 5 * k0)
    (h1 : projection36Phi6R1 b = 5 * k1) :
    projection36Count12 b 0 - projection36Count12 b 2 -
        projection36Count12 b 3 + projection36Count12 b 5 +
        projection36Count12 b 6 - projection36Count12 b 8 -
        projection36Count12 b 9 + projection36Count12 b 11 = 5 * k0 ∧
    projection36Count12 b 1 + projection36Count12 b 2 -
        projection36Count12 b 4 - projection36Count12 b 5 +
        projection36Count12 b 7 + projection36Count12 b 8 -
        projection36Count12 b 10 - projection36Count12 b 11 = 5 * k1 := by
  dsimp only [projection36Count12, projection36Phi6R0,
    projection36Phi6R1] at h0 h1 ⊢
  norm_num at h0 h1 ⊢
  constructor <;> linarith only [h0, h1]

private theorem order15_count_high_impossible
    (b : Fin 36 → Int) (k0 k1 t0 t1 : Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3)
    (hm0 : projection36Phi3R0 b = 5 * t0)
    (hm1 : projection36Phi3R1 b = 5 * t1)
    (h60 : projection36Phi6R0 b = 5 * k0)
    (h61 : projection36Phi6R1 b = 5 * k1)
    (hne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  obtain ⟨hp0, hp1, hp2, hp3⟩ := count12_mod4_high b hmod4
  obtain ⟨hs0, hs1⟩ := count12_phi6_high b k0 k1 h60 h61
  have hm0' :
      projection36Count12 b 0 - projection36Count12 b 2 +
        projection36Count12 b 3 - projection36Count12 b 5 +
        projection36Count12 b 6 - projection36Count12 b 8 +
        projection36Count12 b 9 - projection36Count12 b 11 = 5 * t0 := by
    simpa [projection36Phi3R0] using hm0
  have hm1' :
      projection36Count12 b 1 - projection36Count12 b 2 +
        projection36Count12 b 4 - projection36Count12 b 5 +
        projection36Count12 b 7 - projection36Count12 b 8 +
        projection36Count12 b 10 - projection36Count12 b 11 = 5 * t1 := by
    simpa [projection36Phi3R1] using hm1
  have hsne := hne
  rw [← hs0, ← hs1] at hsne
  apply z180_k12_m6_order15_count_impossible
    (projection36Count12 b 0) (projection36Count12 b 1)
    (projection36Count12 b 2) (projection36Count12 b 3)
    (projection36Count12 b 4) (projection36Count12 b 5)
    (projection36Count12 b 6) (projection36Count12 b 7)
    (projection36Count12 b 8) (projection36Count12 b 9)
    (projection36Count12 b 10) (projection36Count12 b 11)
    k0 k1 t0 t1
  all_goals first
    | exact count12_nonneg_high b hlo _
    | exact count12_le_three_high b hhi _
    | assumption

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

private theorem projected_integer_divisor_lifts
    {A : Finset (ZMod 180)} {m : Nat} (hm36 : m ∣ 36)
    (hdiv : cyclotomic m Int ∣
      projection36IndicatorMask (z180K12ProjectionIndicator A)) :
    cyclotomic m Int ∣ maskPolynomial 180 A := by
  rw [projection36IndicatorMask_z180K12ProjectionIndicator] at hdiv
  exact (cyclotomic_dvd_projection36Mask_iff_dvd_mask hm36).1 hdiv

theorem z180_k12_m6_not_cyclotomic_fifteen
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 15 Int ∣ maskPolynomial 180 A := by
  intro h15
  obtain ⟨k0, k1, hlo, hhi, hmod4, h60, h61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hmod :=
    cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 3) (by norm_num) (by norm_num) (by simpa using h15)
  obtain ⟨t0, t1, hm0, hm1⟩ :=
    projection36_phi3_five_multipliers _ hmod
  exact order15_count_high_impossible _ k0 k1 t0 t1
    hlo hhi hmod4 hm0 hm1 h60 h61 hne

theorem z180_k12_m6_not_cyclotomic_fortyfive
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 45 Int ∣ maskPolynomial 180 A := by
  intro h45
  obtain ⟨k0, k1, hlo, hhi, hmod4, h60, h61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hmod :=
    cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 9) (by norm_num) (by norm_num) (by simpa using h45)
  have hz := projection36_phi9_remainders_zero_of_mod_five_dvd _ hlo hhi hmod
  have hprojected :=
    cyclotomic_nine_dvd_projection36Indicator_of_remainders_zero _ hz
  exact (z180_k12_m6_not_cyclotomic_nine
    hcard hinj htransform2 htransform4 hdefect)
      (projected_integer_divisor_lifts (A := A) (by norm_num) hprojected)

theorem z180_k12_m6_not_cyclotomic_sixty
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
    projection36_phi12_five_multipliers _ hmod
  exact order60_count_high_impossible _ k0 k1 t0 t1 t2 t3
    hlo hhi hmod4 hm0 hm1 hm2 hm3 h60 h61 hne

theorem z180_k12_m6_not_cyclotomic_ninety
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 90 Int ∣ maskPolynomial 180 A := by
  intro h90
  obtain ⟨k0, k1, hlo, hhi, hmod4, h60, h61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hmod :=
    cyclotomic_mod_five_dvd_projection36Indicator_of_five_mul_dvd_mask
      (A := A) (m := 18) (by norm_num) (by norm_num) (by simpa using h90)
  have hz := projection36_phi18_remainders_zero_of_mod_five_dvd _ hlo hhi hmod
  have hprojected :=
    cyclotomic_eighteen_dvd_projection36Indicator_of_remainders_zero _ hz
  exact (z180_k12_m6_not_cyclotomic_eighteen
    hcard hinj htransform2 htransform4 hdefect)
      (projected_integer_divisor_lifts (A := A) (by norm_num) hprojected)

theorem z180_k12_m6_not_cyclotomic_oneeighty
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
  have hz := projection36_phi36_remainders_zero_of_mod_five_dvd _ hlo hhi hmod
  have hprojected :=
    cyclotomic_thirtysix_dvd_projection36Indicator_of_remainders_zero _ hz
  exact (z180_k12_m6_not_cyclotomic_thirtysix
    hcard hinj htransform2 htransform4 hdefect)
      (projected_integer_divisor_lifts (A := A) (by norm_num) hprojected)

theorem z180_k12_m6_cyclotomicZero_order_ne_high_five
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A)
    {d : ZMod 180} (hzero : CyclotomicZero 180 A d) :
    frequencyOrder 180 d ≠ 15 ∧ frequencyOrder 180 d ≠ 45 ∧
      frequencyOrder 180 d ≠ 60 ∧ frequencyOrder 180 d ≠ 90 ∧
      frequencyOrder 180 d ≠ 180 := by
  have h15 := z180_k12_m6_not_cyclotomic_fifteen
    hcard hinj htransform2 htransform4 hdefect
  have h45 := z180_k12_m6_not_cyclotomic_fortyfive
    hcard hinj htransform2 htransform4 hdefect
  have h60 := z180_k12_m6_not_cyclotomic_sixty
    hcard hinj htransform2 htransform4 hdefect
  have h90 := z180_k12_m6_not_cyclotomic_ninety
    hcard hinj htransform2 htransform4 hdefect
  have h180 := z180_k12_m6_not_cyclotomic_oneeighty
    hcard hinj htransform2 htransform4 hdefect
  constructor
  · intro horder
    exact h15 (by simpa [CyclotomicZero, horder] using hzero)
  constructor
  · intro horder
    exact h45 (by simpa [CyclotomicZero, horder] using hzero)
  constructor
  · intro horder
    exact h60 (by simpa [CyclotomicZero, horder] using hzero)
  constructor
  · intro horder
    exact h90 (by simpa [CyclotomicZero, horder] using hzero)
  · intro horder
    exact h180 (by simpa [CyclotomicZero, horder] using hzero)

#print axioms z180_k12_m6_not_cyclotomic_fifteen
#print axioms z180_k12_m6_not_cyclotomic_fortyfive
#print axioms z180_k12_m6_not_cyclotomic_sixty
#print axioms z180_k12_m6_not_cyclotomic_ninety
#print axioms z180_k12_m6_not_cyclotomic_oneeighty
#print axioms z180_k12_m6_cyclotomicZero_order_ne_high_five

end Fuglede
