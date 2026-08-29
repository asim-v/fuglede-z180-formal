import Fuglede.Z180TilingCard36B5T36Exclusions

namespace Fuglede

set_option maxHeartbeats 0

/-- The order-thirty-six transform of the 36-point factor of a `36 × 5` tiling vanishes. -/
theorem z180_tiling_card36_transform_thirty_six_zero
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 36)
    (hA6 : z180ExactOrderTransform A 6 = 0)
    (hA12 : z180ExactOrderTransform A 12 = 0)
    (hA18 : z180ExactOrderTransform A 18 = 0) :
    z180ExactOrderTransform A 36 = 0 := by
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
  have hcover20 := z180_transform_zero_cover_of_tiles hTiles
    (e := 20) (d := (9 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover36 := z180_transform_zero_cover_of_tiles hTiles
    (e := 36) (d := (5 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover45 := z180_transform_zero_cover_of_tiles hTiles
    (e := 45) (d := (4 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover60 := z180_transform_zero_cover_of_tiles hTiles
    (e := 60) (d := (3 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover90 := z180_transform_zero_cover_of_tiles hTiles
    (e := 90) (d := (2 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover180 := z180_transform_zero_cover_of_tiles hTiles
    (e := 180) (d := (1 : ZMod 180)) (by norm_num) (by decide) (by decide)
  rcases hcover36 with hA36 | hB36
  · exact hA36
  · obtain ⟨hB60ne, hB90ne, hB180ne⟩ :=
      z180_card_five_exclusions_of_transform_five_thirty_six_zero hBcard hB5 hB36
    have hA60 := hcover60.resolve_right hB60ne
    have hA90 := hcover90.resolve_right hB90ne
    have hA180 := hcover180.resolve_right hB180ne
    have hAsum := z180_sum_exactOrderDistributionInt A
    have hA1 := exactOrderDistributionInt_one A
    have hC10 := exactOrderDistributionInt_nonneg A 10
    have hC15 := exactOrderDistributionInt_nonneg A 15
    have hE4 := z180ExactOrderTransform_nonneg
      (z180RamanujanIdentity A) (e := 4) (by norm_num)
    have hE9 := z180ExactOrderTransform_nonneg
      (z180RamanujanIdentity A) (e := 9) (by norm_num)
    have hE12 := z180ExactOrderTransform_nonneg
      (z180RamanujanIdentity A) (e := 12) (by norm_num)
    have hE18 := z180ExactOrderTransform_nonneg
      (z180RamanujanIdentity A) (e := 18) (by norm_num)
    have hE36 := z180ExactOrderTransform_nonneg
      (z180RamanujanIdentity A) (e := 36) (by norm_num)
    have hcardCast : (A.card : Int) = 36 := by exact_mod_cast hcard
    have hcardSqCast : ((A.card ^ 2 : Nat) : Int) = 1296 := by
      rw [hcard]
      norm_num
    rw [hcardCast] at hA1
    rw [hcardSqCast] at hAsum
    clear hcard hcardCast hcardSqCast
    simp only [z180ExactOrderTransform] at hA2 hA3 hA4 hA6 hA9 hA12 hA18
    simp only [z180ExactOrderTransform] at hA60 hA90 hA180
    simp only [z180ExactOrderTransform] at hE4 hE9 hE12 hE18 hE36 ⊢
    rcases hcover20 with hA20 | hB20
    · simp only [z180ExactOrderTransform] at hA20
      linarith
    · have hB45ne :=
        z180_card_five_excludes_forty_five_of_five_thirty_six_twenty
          hBcard hB5 hB36 hB20
      have hA45 := hcover45.resolve_right hB45ne
      simp only [z180ExactOrderTransform] at hA45
      linarith

#print axioms z180_tiling_card36_transform_thirty_six_zero

end Fuglede
