import Fuglede.Z180TilingCard36Conditional
import Fuglede.CRT180RamanujanClosure
import Mathlib.Tactic

/-! # The order-six closure for a `36 × 5` tiling -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_transform_zero_of_cyclotomicZero
    {X : Finset (ZMod 180)} {e : Nat} {d : ZMod 180}
    (he : e ∈ (180).divisors) (horder : frequencyOrder 180 d = e)
    (hzero : CyclotomicZero 180 X d) :
    z180ExactOrderTransform X e = 0 := by
  apply z180ExactOrderTransform_eq_zero_of_fourierEnergy_eq_zero
    (z180RamanujanIdentity X) he
  exact exactOrderFourierEnergy_eq_zero_of_cyclotomicZero horder hzero

theorem z180_cyclotomicZero_of_transform_zero
    {X : Finset (ZMod 180)} {e : Nat} {d : ZMod 180}
    (he : e ∈ (180).divisors) (horder : frequencyOrder 180 d = e)
    (hzero : z180ExactOrderTransform X e = 0) :
    CyclotomicZero 180 X d := by
  have henergy : exactOrderFourierEnergy X e = 0 := by
    have hid := z180RamanujanIdentity X e he
    rw [← hid]
    exact_mod_cast hzero
  exact (exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero X e).mp
    henergy d horder

theorem z180_transform_zero_cover_of_tiles
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    {e : Nat} {d : ZMod 180} (he : e ∈ (180).divisors)
    (horder : frequencyOrder 180 d = e) (hd : d ≠ 0) :
    z180ExactOrderTransform A e = 0 ∨
      z180ExactOrderTransform B e = 0 := by
  rcases cyclotomic_zero_cover_of_tiles hTiles d hd with hA | hB
  · exact Or.inl (z180_transform_zero_of_cyclotomicZero he horder hA)
  · exact Or.inr (z180_transform_zero_of_cyclotomicZero he horder hB)

private theorem z180_card_five_exclusions_of_transform_five_six_zero
    {B : Finset (ZMod 180)} (hcard : B.card = 5)
    (h5 : z180ExactOrderTransform B 5 = 0)
    (h6 : z180ExactOrderTransform B 6 = 0) :
    z180ExactOrderTransform B 10 ≠ 0 ∧
    z180ExactOrderTransform B 15 ≠ 0 ∧
    z180ExactOrderTransform B 20 ≠ 0 ∧
    z180ExactOrderTransform B 30 ≠ 0 ∧
    z180ExactOrderTransform B 45 ≠ 0 ∧
    z180ExactOrderTransform B 60 ≠ 0 ∧
    z180ExactOrderTransform B 90 ≠ 0 ∧
    z180ExactOrderTransform B 180 ≠ 0 := by
  have hsum := z180_sum_exactOrderDistributionInt B
  have h1 := exactOrderDistributionInt_one B
  have hC2 := exactOrderDistributionInt_nonneg B 2
  have hC3 := exactOrderDistributionInt_nonneg B 3
  have hC4 := exactOrderDistributionInt_nonneg B 4
  have hC5 := exactOrderDistributionInt_nonneg B 5
  have hC6 := exactOrderDistributionInt_nonneg B 6
  have hC9 := exactOrderDistributionInt_nonneg B 9
  have hC10 := exactOrderDistributionInt_nonneg B 10
  have hC12 := exactOrderDistributionInt_nonneg B 12
  have hC15 := exactOrderDistributionInt_nonneg B 15
  have hC18 := exactOrderDistributionInt_nonneg B 18
  have hC20 := exactOrderDistributionInt_nonneg B 20
  have hC30 := exactOrderDistributionInt_nonneg B 30
  have hC36 := exactOrderDistributionInt_nonneg B 36
  have hC45 := exactOrderDistributionInt_nonneg B 45
  have hC60 := exactOrderDistributionInt_nonneg B 60
  have hC90 := exactOrderDistributionInt_nonneg B 90
  have hC180 := exactOrderDistributionInt_nonneg B 180
  have hcardCast : (B.card : Int) = 5 := by exact_mod_cast hcard
  have hcardSqCast : ((B.card ^ 2 : Nat) : Int) = 25 := by
    rw [hcard]
    norm_num
  rw [hcardCast] at h1
  rw [hcardSqCast] at hsum
  clear hcard hcardCast hcardSqCast
  simp only [z180ExactOrderTransform] at h5 h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro hx <;> simp only [z180ExactOrderTransform] at hx <;> omega

theorem z180_tiling_card36_transform_six_zero
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 36) :
    z180ExactOrderTransform A 6 = 0 := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  have hBcard : B.card = 5 := by
    rw [hcard] at hprod
    omega
  obtain ⟨h2, h3, h4, h9, h5B⟩ :=
    z180_tile_card_thirty_six_primePower_zeros hTiles hcard
  have hA2 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 2) (d := (90 : ZMod 180)) (by norm_num) (by decide) h2
  have hA3 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 3) (d := (60 : ZMod 180)) (by norm_num) (by decide) h3
  have hA4 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 4) (d := (45 : ZMod 180)) (by norm_num) (by decide) h4
  have hA9 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 9) (d := (20 : ZMod 180)) (by norm_num) (by decide) h9
  have hB5 := z180_transform_zero_of_cyclotomicZero
    (X := B) (e := 5) (d := (36 : ZMod 180)) (by norm_num) (by decide) h5B
  have hcover6 := z180_transform_zero_cover_of_tiles hTiles
    (e := 6) (d := (30 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover10 := z180_transform_zero_cover_of_tiles hTiles
    (e := 10) (d := (18 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover15 := z180_transform_zero_cover_of_tiles hTiles
    (e := 15) (d := (12 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover20 := z180_transform_zero_cover_of_tiles hTiles
    (e := 20) (d := (9 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover30 := z180_transform_zero_cover_of_tiles hTiles
    (e := 30) (d := (6 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover45 := z180_transform_zero_cover_of_tiles hTiles
    (e := 45) (d := (4 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover60 := z180_transform_zero_cover_of_tiles hTiles
    (e := 60) (d := (3 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover90 := z180_transform_zero_cover_of_tiles hTiles
    (e := 90) (d := (2 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover180 := z180_transform_zero_cover_of_tiles hTiles
    (e := 180) (d := (1 : ZMod 180)) (by norm_num) (by decide) (by decide)
  rcases hcover6 with hA6 | hB6
  · exact hA6
  · obtain ⟨hB10ne, hB15ne, hB20ne, hB30ne, hB45ne, hB60ne,
        hB90ne, hB180ne⟩ :=
      z180_card_five_exclusions_of_transform_five_six_zero hBcard hB5 hB6
    have hA10 := hcover10.resolve_right hB10ne
    have hA15 := hcover15.resolve_right hB15ne
    have hA20 := hcover20.resolve_right hB20ne
    have hA30 := hcover30.resolve_right hB30ne
    have hA45 := hcover45.resolve_right hB45ne
    have hA60 := hcover60.resolve_right hB60ne
    have hA90 := hcover90.resolve_right hB90ne
    have hA180 := hcover180.resolve_right hB180ne
    have hAsum := z180_sum_exactOrderDistributionInt A
    have hA1 := exactOrderDistributionInt_one A
    have hC10 := exactOrderDistributionInt_nonneg A 10
    have hC20 := exactOrderDistributionInt_nonneg A 20
    have hC45 := exactOrderDistributionInt_nonneg A 45
    have hAe6 := z180ExactOrderTransform_nonneg
      (z180RamanujanIdentity A) (e := 6) (by norm_num)
    have hAe12 := z180ExactOrderTransform_nonneg
      (z180RamanujanIdentity A) (e := 12) (by norm_num)
    have hcardCast : (A.card : Int) = 36 := by exact_mod_cast hcard
    have hcardSqCast : ((A.card ^ 2 : Nat) : Int) = 1296 := by
      rw [hcard]
      norm_num
    rw [hcardCast] at hA1
    rw [hcardSqCast] at hAsum
    clear hcard hcardCast hcardSqCast
    simp only [z180ExactOrderTransform] at hA2 hA3 hA4 hA9 hA10 hA15
    simp only [z180ExactOrderTransform] at hA20 hA30 hA45 hA60 hA90 hA180
    simp only [z180ExactOrderTransform] at hAe6 hAe12 ⊢
    linarith

#print axioms z180_tiling_card36_transform_six_zero

end Fuglede
