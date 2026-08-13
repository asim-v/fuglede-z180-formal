import Fuglede.Z180K12M6SemanticCommon
import Fuglede.Z180K12M6Order9CompactIndicator
import Fuglede.Z180K12M6Order18CompactIndicator
import Fuglede.Z180K12M6Order36CompactIndicator
import Fuglede.Z180K12Projection36Remainders36
import Mathlib.Tactic

/-!
# Semantic exclusions of projected orders 9, 18, and 36

The compact arithmetic kernels in the imported modules speak about 36 named
integer variables.  This file supplies those variables with the genuine
zero-one projection indicator of a subset of `ZMod 180` and obtains the
cyclotomic remainder equations from divisibility of its mask.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

private theorem order9_indicator_impossible
    (b : Fin 36 → Int) (k0 k1 : Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3)
    (hrem :
      b 0 - b 6 + b 9 - b 15 + b 18 - b 24 + b 27 - b 33 = 0 ∧
      b 1 - b 7 + b 10 - b 16 + b 19 - b 25 + b 28 - b 34 = 0 ∧
      b 2 - b 8 + b 11 - b 17 + b 20 - b 26 + b 29 - b 35 = 0 ∧
      b 3 - b 6 + b 12 - b 15 + b 21 - b 24 + b 30 - b 33 = 0 ∧
      b 4 - b 7 + b 13 - b 16 + b 22 - b 25 + b 31 - b 34 = 0 ∧
      b 5 - b 8 + b 14 - b 17 + b 23 - b 26 + b 32 - b 35 = 0)
    (hphi60 : projection36Phi6R0 b = 5 * k0)
    (hphi61 : projection36Phi6R1 b = 5 * k1)
    (hne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  rcases hmod4 with ⟨hm0, hm1, hm2, hm3⟩
  rcases hrem with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩
  dsimp only [projection36Phi6R0] at hphi60
  dsimp only [projection36Phi6R1] at hphi61
  apply z180_k12_m6_order9_compact_indicator_impossible
    (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8)
    (b 9) (b 10) (b 11) (b 12) (b 13) (b 14) (b 15) (b 16) (b 17)
    (b 18) (b 19) (b 20) (b 21) (b 22) (b 23) (b 24) (b 25) (b 26)
    (b 27) (b 28) (b 29) (b 30) (b 31) (b 32) (b 33) (b 34) (b 35)
    k0 k1
  all_goals first
    | exact hlo _
    | exact hhi _
    | assumption
    | (norm_num; linarith only [hr0, hr1, hr2, hr3, hr4, hr5,
        hphi60, hphi61])

private theorem order18_indicator_impossible
    (b : Fin 36 → Int) (k0 k1 : Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3)
    (hrem :
      b 0 - b 6 - b 9 + b 15 + b 18 - b 24 - b 27 + b 33 = 0 ∧
      b 1 - b 7 - b 10 + b 16 + b 19 - b 25 - b 28 + b 34 = 0 ∧
      b 2 - b 8 - b 11 + b 17 + b 20 - b 26 - b 29 + b 35 = 0 ∧
      b 3 + b 6 - b 12 - b 15 + b 21 + b 24 - b 30 - b 33 = 0 ∧
      b 4 + b 7 - b 13 - b 16 + b 22 + b 25 - b 31 - b 34 = 0 ∧
      b 5 + b 8 - b 14 - b 17 + b 23 + b 26 - b 32 - b 35 = 0)
    (hphi60 : projection36Phi6R0 b = 5 * k0)
    (hphi61 : projection36Phi6R1 b = 5 * k1)
    (hne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  rcases hmod4 with ⟨hm0, hm1, hm2, hm3⟩
  rcases hrem with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩
  dsimp only [projection36Phi6R0] at hphi60
  dsimp only [projection36Phi6R1] at hphi61
  apply z180_k12_m6_order18_compact_indicator_impossible
    (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8)
    (b 9) (b 10) (b 11) (b 12) (b 13) (b 14) (b 15) (b 16) (b 17)
    (b 18) (b 19) (b 20) (b 21) (b 22) (b 23) (b 24) (b 25) (b 26)
    (b 27) (b 28) (b 29) (b 30) (b 31) (b 32) (b 33) (b 34) (b 35)
    k0 k1
  all_goals first
    | exact hlo _
    | exact hhi _
    | assumption
    | (norm_num; linarith only [hr0, hr1, hr2, hr3, hr4, hr5,
        hphi60, hphi61])

private theorem order36_indicator_impossible
    (b : Fin 36 → Int) (k0 k1 : Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3)
    (hrem :
      b 0 - b 12 - b 18 + b 30 = 0 ∧
      b 1 - b 13 - b 19 + b 31 = 0 ∧
      b 2 - b 14 - b 20 + b 32 = 0 ∧
      b 3 - b 15 - b 21 + b 33 = 0 ∧
      b 4 - b 16 - b 22 + b 34 = 0 ∧
      b 5 - b 17 - b 23 + b 35 = 0 ∧
      b 6 + b 12 - b 24 - b 30 = 0 ∧
      b 7 + b 13 - b 25 - b 31 = 0 ∧
      b 8 + b 14 - b 26 - b 32 = 0 ∧
      b 9 + b 15 - b 27 - b 33 = 0 ∧
      b 10 + b 16 - b 28 - b 34 = 0 ∧
      b 11 + b 17 - b 29 - b 35 = 0)
    (hphi60 : projection36Phi6R0 b = 5 * k0)
    (hphi61 : projection36Phi6R1 b = 5 * k1)
    (hne : 5 * k0 ≠ 0 ∨ 5 * k1 ≠ 0) : False := by
  rcases hmod4 with ⟨hm0, hm1, hm2, hm3⟩
  rcases hrem with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8,
    hr9, hr10, hr11⟩
  dsimp only [projection36Phi6R0] at hphi60
  dsimp only [projection36Phi6R1] at hphi61
  apply z180_k12_m6_order36_compact_indicator_impossible
    (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8)
    (b 9) (b 10) (b 11) (b 12) (b 13) (b 14) (b 15) (b 16) (b 17)
    (b 18) (b 19) (b 20) (b 21) (b 22) (b 23) (b 24) (b 25) (b 26)
    (b 27) (b 28) (b 29) (b 30) (b 31) (b 32) (b 33) (b 34) (b 35)
    k0 k1
  all_goals first
    | exact hlo _
    | exact hhi _
    | assumption
    | (norm_num; linarith only [hr0, hr1, hr2, hr3, hr4, hr5,
        hr6, hr7, hr8, hr9, hr10, hr11, hphi60, hphi61])

private theorem projected_divisor_of_mask_divisor
    {A : Finset (ZMod 180)} {q : Nat} (hq36 : q ∣ 36)
    (hdiv : cyclotomic q Int ∣ maskPolynomial 180 A) :
    cyclotomic q Int ∣
      projection36IndicatorMask (z180K12ProjectionIndicator A) := by
  rw [projection36IndicatorMask_z180K12ProjectionIndicator]
  exact (cyclotomic_dvd_projection36Mask_iff_dvd_mask hq36).2 hdiv

/-- The cardinality-twelve `m = 6` package excludes a `Phi_9` factor. -/
theorem z180_k12_m6_not_cyclotomic_nine
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 9 Int ∣ maskPolynomial 180 A := by
  intro hdiv
  obtain ⟨k0, k1, hlo, hhi, hmod4, hphi60, hphi61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hprojected := projected_divisor_of_mask_divisor (q := 9)
    (A := A) (by norm_num) hdiv
  have hrem := projection36_phi9_remainders
    (z180K12ProjectionIndicator A)
    (by simpa [projection36IndicatorMask] using hprojected)
  exact order9_indicator_impossible _ k0 k1 hlo hhi hmod4 hrem
    hphi60 hphi61 hne

/-- The cardinality-twelve `m = 6` package excludes a `Phi_18` factor. -/
theorem z180_k12_m6_not_cyclotomic_eighteen
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 18 Int ∣ maskPolynomial 180 A := by
  intro hdiv
  obtain ⟨k0, k1, hlo, hhi, hmod4, hphi60, hphi61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hprojected := projected_divisor_of_mask_divisor (q := 18)
    (A := A) (by norm_num) hdiv
  have hrem := projection36_phi18_remainders
    (z180K12ProjectionIndicator A)
    (by simpa [projection36IndicatorMask] using hprojected)
  exact order18_indicator_impossible _ k0 k1 hlo hhi hmod4 hrem
    hphi60 hphi61 hne

/-- The cardinality-twelve `m = 6` package excludes a `Phi_36` factor. -/
theorem z180_k12_m6_not_cyclotomic_thirtysix
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 36 Int ∣ maskPolynomial 180 A := by
  intro hdiv
  obtain ⟨k0, k1, hlo, hhi, hmod4, hphi60, hphi61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hprojected := projected_divisor_of_mask_divisor (q := 36)
    (A := A) (by norm_num) hdiv
  have hrem := projection36_phi36_remainders
    (z180K12ProjectionIndicator A)
    (by simpa [projection36IndicatorMask] using hprojected)
  exact order36_indicator_impossible _ k0 k1 hlo hhi hmod4 hrem
    hphi60 hphi61 hne

/-- Set-level form consumed by the exact-order sieve: a cyclotomic zero in
the `m = 6` defect branch has none of the projected orders 9, 18, or 36. -/
theorem z180_k12_m6_cyclotomicZero_order_ne_nine_eighteen_thirtysix
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A)
    {d : ZMod 180} (hzero : CyclotomicZero 180 A d) :
    frequencyOrder 180 d ≠ 9 ∧
      frequencyOrder 180 d ≠ 18 ∧
      frequencyOrder 180 d ≠ 36 := by
  have h9 := z180_k12_m6_not_cyclotomic_nine
    hcard hinj htransform2 htransform4 hdefect
  have h18 := z180_k12_m6_not_cyclotomic_eighteen
    hcard hinj htransform2 htransform4 hdefect
  have h36 := z180_k12_m6_not_cyclotomic_thirtysix
    hcard hinj htransform2 htransform4 hdefect
  constructor
  · intro horder
    apply h9
    simpa [CyclotomicZero, horder] using hzero
  constructor
  · intro horder
    apply h18
    simpa [CyclotomicZero, horder] using hzero
  · intro horder
    apply h36
    simpa [CyclotomicZero, horder] using hzero

#print axioms z180_k12_m6_not_cyclotomic_nine
#print axioms z180_k12_m6_not_cyclotomic_eighteen
#print axioms z180_k12_m6_not_cyclotomic_thirtysix
#print axioms z180_k12_m6_cyclotomicZero_order_ne_nine_eighteen_thirtysix

end Fuglede
