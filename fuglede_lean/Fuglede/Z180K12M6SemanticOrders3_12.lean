import Fuglede.Z180K12M6SemanticCommon
import Fuglede.Z180K12M6CountOmega
import Fuglede.Z180K12Projection36Remainders3_12
import Mathlib.Tactic

/-!
# Semantic exclusions of projected orders 3 and 12

This is the set-level adapter from the genuine 36-coordinate projection to
the twelve-count Presburger kernels.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

private theorem projection36Count12_nonneg
    (b : Fin 36 → Int) (hlo : ∀ i, 0 ≤ b i) (r : Fin 12) :
    0 ≤ projection36Count12 b r := by
  rw [projection36Count12]
  linarith only [hlo ⟨r.val, by omega⟩,
    hlo ⟨r.val + 12, by omega⟩, hlo ⟨r.val + 24, by omega⟩]

private theorem projection36Count12_le_three
    (b : Fin 36 → Int) (hhi : ∀ i, b i ≤ 1) (r : Fin 12) :
    projection36Count12 b r ≤ 3 := by
  rw [projection36Count12]
  linarith only [hhi ⟨r.val, by omega⟩,
    hhi ⟨r.val + 12, by omega⟩, hhi ⟨r.val + 24, by omega⟩]

private theorem projection36Count12_mod4_profile
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
  change
    (b 0 + b 12 + b 24) + (b 4 + b 16 + b 28) +
        (b 8 + b 20 + b 32) = 3 ∧
    (b 1 + b 13 + b 25) + (b 5 + b 17 + b 29) +
        (b 9 + b 21 + b 33) = 3 ∧
    (b 2 + b 14 + b 26) + (b 6 + b 18 + b 30) +
        (b 10 + b 22 + b 34) = 3 ∧
    (b 3 + b 15 + b 27) + (b 7 + b 19 + b 31) +
        (b 11 + b 23 + b 35) = 3
  constructor
  · linarith only [h0]
  constructor
  · linarith only [h1]
  constructor
  · linarith only [h2]
  · linarith only [h3]

private theorem projection36Count12_phi6_remainders
    (b : Fin 36 → Int) (k0 k1 : Int)
    (hphi60 : projection36Phi6R0 b = 5 * k0)
    (hphi61 : projection36Phi6R1 b = 5 * k1) :
    projection36Count12 b 0 - projection36Count12 b 2 -
        projection36Count12 b 3 + projection36Count12 b 5 +
        projection36Count12 b 6 - projection36Count12 b 8 -
        projection36Count12 b 9 + projection36Count12 b 11 = 5 * k0 ∧
    projection36Count12 b 1 + projection36Count12 b 2 -
        projection36Count12 b 4 - projection36Count12 b 5 +
        projection36Count12 b 7 + projection36Count12 b 8 -
        projection36Count12 b 10 - projection36Count12 b 11 = 5 * k1 := by
  dsimp only [projection36Count12, projection36Phi6R0,
    projection36Phi6R1] at hphi60 hphi61 ⊢
  norm_num at hphi60 hphi61 ⊢
  change
    (b 0 + b 12 + b 24) - (b 2 + b 14 + b 26) -
        (b 3 + b 15 + b 27) + (b 5 + b 17 + b 29) +
        (b 6 + b 18 + b 30) - (b 8 + b 20 + b 32) -
        (b 9 + b 21 + b 33) + (b 11 + b 23 + b 35) = 5 * k0 ∧
    (b 1 + b 13 + b 25) + (b 2 + b 14 + b 26) -
        (b 4 + b 16 + b 28) - (b 5 + b 17 + b 29) +
        (b 7 + b 19 + b 31) + (b 8 + b 20 + b 32) -
        (b 10 + b 22 + b 34) - (b 11 + b 23 + b 35) = 5 * k1
  constructor
  · linarith only [hphi60]
  · linarith only [hphi61]

private theorem order3_count_indicator_impossible
    (b : Fin 36 → Int) (k0 k1 : Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3)
    (hrem :
      projection36Count12 b 0 - projection36Count12 b 2 +
          projection36Count12 b 3 - projection36Count12 b 5 +
          projection36Count12 b 6 - projection36Count12 b 8 +
          projection36Count12 b 9 - projection36Count12 b 11 = 0 ∧
      projection36Count12 b 1 - projection36Count12 b 2 +
          projection36Count12 b 4 - projection36Count12 b 5 +
          projection36Count12 b 7 - projection36Count12 b 8 +
          projection36Count12 b 10 - projection36Count12 b 11 = 0)
    (hphi60 : projection36Phi6R0 b = 5 * k0)
    (hphi61 : projection36Phi6R1 b = 5 * k1)
    (hne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  obtain ⟨hm0, hm1, hm2, hm3⟩ := projection36Count12_mod4_profile b hmod4
  obtain ⟨hr0, hr1⟩ := hrem
  obtain ⟨h60, h61⟩ :=
    projection36Count12_phi6_remainders b k0 k1 hphi60 hphi61
  have hcountNe :
      projection36Count12 b 0 - projection36Count12 b 2 -
          projection36Count12 b 3 + projection36Count12 b 5 +
          projection36Count12 b 6 - projection36Count12 b 8 -
          projection36Count12 b 9 + projection36Count12 b 11 ≠ 0 ∨
      projection36Count12 b 1 + projection36Count12 b 2 -
          projection36Count12 b 4 - projection36Count12 b 5 +
          projection36Count12 b 7 + projection36Count12 b 8 -
          projection36Count12 b 10 - projection36Count12 b 11 ≠ 0 := by
    rcases hne with hne0 | hne1
    · left
      rw [h60]
      exact hne0
    · right
      rw [h61]
      exact hne1
  apply z180_k12_m6_count_order3_impossible
    (projection36Count12 b 0) (projection36Count12 b 1)
    (projection36Count12 b 2) (projection36Count12 b 3)
    (projection36Count12 b 4) (projection36Count12 b 5)
    (projection36Count12 b 6) (projection36Count12 b 7)
    (projection36Count12 b 8) (projection36Count12 b 9)
    (projection36Count12 b 10) (projection36Count12 b 11) k0 k1
  all_goals first
    | exact projection36Count12_nonneg b hlo _
    | exact projection36Count12_le_three b hhi _
    | assumption

private theorem order12_count_indicator_impossible
    (b : Fin 36 → Int) (k0 k1 : Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3)
    (hrem :
      projection36Count12 b 0 - projection36Count12 b 4 -
          projection36Count12 b 6 + projection36Count12 b 10 = 0 ∧
      projection36Count12 b 1 - projection36Count12 b 5 -
          projection36Count12 b 7 + projection36Count12 b 11 = 0 ∧
      projection36Count12 b 2 + projection36Count12 b 4 -
          projection36Count12 b 8 - projection36Count12 b 10 = 0 ∧
      projection36Count12 b 3 + projection36Count12 b 5 -
          projection36Count12 b 9 - projection36Count12 b 11 = 0)
    (hphi60 : projection36Phi6R0 b = 5 * k0)
    (hphi61 : projection36Phi6R1 b = 5 * k1)
    (hne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  obtain ⟨hm0, hm1, hm2, hm3⟩ := projection36Count12_mod4_profile b hmod4
  obtain ⟨hr0, hr1, hr2, hr3⟩ := hrem
  obtain ⟨h60, h61⟩ :=
    projection36Count12_phi6_remainders b k0 k1 hphi60 hphi61
  have hcountNe :
      projection36Count12 b 0 - projection36Count12 b 2 -
          projection36Count12 b 3 + projection36Count12 b 5 +
          projection36Count12 b 6 - projection36Count12 b 8 -
          projection36Count12 b 9 + projection36Count12 b 11 ≠ 0 ∨
      projection36Count12 b 1 + projection36Count12 b 2 -
          projection36Count12 b 4 - projection36Count12 b 5 +
          projection36Count12 b 7 + projection36Count12 b 8 -
          projection36Count12 b 10 - projection36Count12 b 11 ≠ 0 := by
    rcases hne with hne0 | hne1
    · left
      rw [h60]
      exact hne0
    · right
      rw [h61]
      exact hne1
  apply z180_k12_m6_count_order12_impossible
    (projection36Count12 b 0) (projection36Count12 b 1)
    (projection36Count12 b 2) (projection36Count12 b 3)
    (projection36Count12 b 4) (projection36Count12 b 5)
    (projection36Count12 b 6) (projection36Count12 b 7)
    (projection36Count12 b 8) (projection36Count12 b 9)
    (projection36Count12 b 10) (projection36Count12 b 11) k0 k1
  all_goals first
    | exact projection36Count12_nonneg b hlo _
    | exact projection36Count12_le_three b hhi _
    | assumption

private theorem projected_raw_divisor_of_mask_divisor
    {A : Finset (ZMod 180)} {q : Nat} (hq36 : q ∣ 36)
    (hdiv : cyclotomic q Int ∣ maskPolynomial 180 A) :
    cyclotomic q Int ∣ ∑ i : Fin 36,
      monomial i.val (z180K12ProjectionIndicator A i) := by
  have hprojected : cyclotomic q Int ∣ z180Projection36Mask A :=
    (cyclotomic_dvd_projection36Mask_iff_dvd_mask hq36).2 hdiv
  rw [z180Projection36Mask_eq_sum_occupancy] at hprojected
  simpa only [z180K12ProjectionIndicator] using hprojected

theorem z180_k12_m6_not_cyclotomic_three
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 3 Int ∣ maskPolynomial 180 A := by
  intro hdiv
  obtain ⟨k0, k1, hlo, hhi, hmod4, hphi60, hphi61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hraw := projected_raw_divisor_of_mask_divisor (q := 3)
    (A := A) (by norm_num) hdiv
  have hrem := projection36_phi3_count12_remainders
    (z180K12ProjectionIndicator A) hraw
  exact order3_count_indicator_impossible _ k0 k1 hlo hhi hmod4 hrem
    hphi60 hphi61 hne

theorem z180_k12_m6_not_cyclotomic_twelve
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 12 Int ∣ maskPolynomial 180 A := by
  intro hdiv
  obtain ⟨k0, k1, hlo, hhi, hmod4, hphi60, hphi61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hraw := projected_raw_divisor_of_mask_divisor (q := 12)
    (A := A) (by norm_num) hdiv
  have hrem := projection36_phi12_count12_remainders
    (z180K12ProjectionIndicator A) hraw
  exact order12_count_indicator_impossible _ k0 k1 hlo hhi hmod4 hrem
    hphi60 hphi61 hne

theorem z180_k12_m6_cyclotomicZero_order_ne_three_twelve
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A)
    {d : ZMod 180} (hzero : CyclotomicZero 180 A d) :
    frequencyOrder 180 d ≠ 3 ∧ frequencyOrder 180 d ≠ 12 := by
  constructor
  · intro horder
    apply z180_k12_m6_not_cyclotomic_three
      hcard hinj htransform2 htransform4 hdefect
    simpa [CyclotomicZero, horder] using hzero
  · intro horder
    apply z180_k12_m6_not_cyclotomic_twelve
      hcard hinj htransform2 htransform4 hdefect
    simpa [CyclotomicZero, horder] using hzero

#print axioms z180_k12_m6_not_cyclotomic_three
#print axioms z180_k12_m6_not_cyclotomic_twelve
#print axioms z180_k12_m6_cyclotomicZero_order_ne_three_twelve

end Fuglede
