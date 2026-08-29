import Fuglede.Z180TilingCard36B5T12Secondary

namespace Fuglede

set_option maxHeartbeats 0

/-- The order-twelve transform of the 36-point factor of a `36 × 5` tiling vanishes. -/
theorem z180_tiling_card36_transform_twelve_zero
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 36)
    (hA6 : z180ExactOrderTransform A 6 = 0) :
    z180ExactOrderTransform A 12 = 0 := by
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
  have hcover10 := z180_transform_zero_cover_of_tiles hTiles
    (e := 10) (d := (18 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover12 := z180_transform_zero_cover_of_tiles hTiles
    (e := 12) (d := (15 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover15 := z180_transform_zero_cover_of_tiles hTiles
    (e := 15) (d := (12 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover18 := z180_transform_zero_cover_of_tiles hTiles
    (e := 18) (d := (10 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover20 := z180_transform_zero_cover_of_tiles hTiles
    (e := 20) (d := (9 : ZMod 180)) (by norm_num) (by decide) (by decide)
  have hcover30 := z180_transform_zero_cover_of_tiles hTiles
    (e := 30) (d := (6 : ZMod 180)) (by norm_num) (by decide) (by decide)
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
  rcases hcover12 with hA12 | hB12
  · exact hA12
  · obtain ⟨hB20ne, hB30ne, hB60ne, hB90ne, hB180ne⟩ :=
      z180_card_five_exclusions_of_transform_five_twelve_zero hBcard hB5 hB12
    have hA20 := hcover20.resolve_right hB20ne
    have hA30 := hcover30.resolve_right hB30ne
    have hA60 := hcover60.resolve_right hB60ne
    have hA90 := hcover90.resolve_right hB90ne
    have hA180 := hcover180.resolve_right hB180ne
    have hAsum := z180_sum_exactOrderDistributionInt A
    have hA1 := exactOrderDistributionInt_one A
    have hC10 := exactOrderDistributionInt_nonneg A 10
    have hC20 := exactOrderDistributionInt_nonneg A 20
    have hC30 := exactOrderDistributionInt_nonneg A 30
    have hE4 := z180ExactOrderTransform_nonneg (z180RamanujanIdentity A)
      (e := 4) (by norm_num)
    have hE9 := z180ExactOrderTransform_nonneg (z180RamanujanIdentity A)
      (e := 9) (by norm_num)
    have hE12 := z180ExactOrderTransform_nonneg (z180RamanujanIdentity A)
      (e := 12) (by norm_num)
    have hE18 := z180ExactOrderTransform_nonneg (z180RamanujanIdentity A)
      (e := 18) (by norm_num)
    have hE36 := z180ExactOrderTransform_nonneg (z180RamanujanIdentity A)
      (e := 36) (by norm_num)
    have hcardCast : (A.card : Int) = 36 := by exact_mod_cast hcard
    have hcardSqCast : ((A.card ^ 2 : Nat) : Int) = 1296 := by
      rw [hcard]
      norm_num
    rw [hcardCast] at hA1
    rw [hcardSqCast] at hAsum
    clear hcard hcardCast hcardSqCast
    simp only [z180ExactOrderTransform] at hA2 hA3 hA4 hA6 hA9 hA20 hA30
    simp only [z180ExactOrderTransform] at hA60 hA90 hA180
    simp only [z180ExactOrderTransform] at hE4 hE9 hE12 hE18 hE36 ⊢
    rcases hcover10 with hA10 | hB10
    · simp only [z180ExactOrderTransform] at hA10
      linarith
    · obtain ⟨hB15ne, hBsecondary⟩ :=
        z180_card_five_secondary_exclusions_five_twelve_ten
          hBcard hB5 hB12 hB10
      have hA15 := hcover15.resolve_right hB15ne
      simp only [z180ExactOrderTransform] at hA15
      rcases hcover18 with hA18 | hB18
      · simp only [z180ExactOrderTransform] at hA18
        linarith
      · obtain ⟨hB36ne, hB45ne⟩ := hBsecondary hB18
        have hA36 := hcover36.resolve_right hB36ne
        have hA45 := hcover45.resolve_right hB45ne
        simp only [z180ExactOrderTransform] at hA36 hA45
        linarith

#print axioms z180_tiling_card36_transform_twelve_zero

end Fuglede
