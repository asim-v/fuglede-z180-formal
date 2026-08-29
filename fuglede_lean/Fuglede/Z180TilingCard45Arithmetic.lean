import Fuglede.Z180TilingCard45ComplementArithmetic
import Fuglede.Z180TilingCard45FactorArithmetic

/-! # Mixed exact-order zeros for a `45 × 4` tiling -/

namespace Fuglede

set_option maxHeartbeats 0

theorem z180_tiling_card45_mixed_transform_zeros
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 45) :
    z180ExactOrderTransform A 15 = 0 ∧
      z180ExactOrderTransform A 45 = 0 := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 4 := by omega
  have hA3c : CyclotomicZero 180 A (60 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
      (A := B) (B := A) (p := 3) (d := (60 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  have hA9c : CyclotomicZero 180 A (20 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_primePower_not_dvd_card
      (A := B) (B := A) (p := 3) (k := 1) (d := (20 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  have hA5c : CyclotomicZero 180 A (36 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
      (A := B) (B := A) (p := 5) (d := (36 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  have hB2c : CyclotomicZero 180 B (90 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
      (A := A) (B := B) (p := 2) (d := (90 : ZMod 180))
      (by norm_num) (by decide) (by decide) hTiles (by omega)
  have hB4c : CyclotomicZero 180 B (45 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_primePower_not_dvd_card
      (A := A) (B := B) (p := 2) (k := 1) (d := (45 : ZMod 180))
      (by norm_num) (by decide) (by decide) hTiles (by omega)
  have hA3 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 3) (d := (60 : ZMod 180)) (by norm_num) (by decide) hA3c
  have hA5 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 5) (d := (36 : ZMod 180)) (by norm_num) (by decide) hA5c
  have hA9 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 9) (d := (20 : ZMod 180)) (by norm_num) (by decide) hA9c
  have hB2 := z180_transform_zero_of_cyclotomicZero
    (X := B) (e := 2) (d := (90 : ZMod 180)) (by norm_num) (by decide) hB2c
  have hB4 := z180_transform_zero_of_cyclotomicZero
    (X := B) (e := 4) (d := (45 : ZMod 180)) (by norm_num) (by decide) hB4c
  have hcover6 := z180_transform_zero_cover_of_tiles hTiles
    (e := 6) (d := (30 : ZMod 180)) (by norm_num) (by decide) (by decide)
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
  have hA15 : z180ExactOrderTransform A 15 = 0 := by
    rcases hcover15 with hA15 | hB15
    · exact hA15
    · obtain ⟨⟨hB30ne, hB45ne, hB60ne, hB90ne, hB180ne⟩,
          hB36zero, hB10zero, hB10nonzero⟩ :=
        z180_card4_pattern_of_zeros_two_four_fifteen hBcard hB2 hB4 hB15
      have hA30 := hcover30.resolve_right hB30ne
      have hA45 := hcover45.resolve_right hB45ne
      have hA60 := hcover60.resolve_right hB60ne
      have hA90 := hcover90.resolve_right hB90ne
      have hA180 := hcover180.resolve_right hB180ne
      apply z180_card45_transform_fifteen_zero_of_three_cases hcard
        hA3 hA5 hA9 hA30 hA45 hA60 hA90 hA180
      by_cases hB36 : z180ExactOrderTransform B 36 = 0
      · obtain ⟨hB6ne, hB18ne, hB20ne⟩ := hB36zero hB36
        exact Or.inl ⟨hcover6.resolve_right hB6ne,
          hcover18.resolve_right hB18ne, hcover20.resolve_right hB20ne⟩
      · have hA36 := hcover36.resolve_right hB36
        by_cases hB10 : z180ExactOrderTransform B 10 = 0
        · obtain ⟨hB6ne, hB20ne⟩ := hB10zero hB36 hB10
          exact Or.inr (Or.inl ⟨hcover6.resolve_right hB6ne,
            hcover20.resolve_right hB20ne, hA36⟩)
        · have hB12ne := hB10nonzero hB36 hB10
          exact Or.inr (Or.inr ⟨hcover10.resolve_right hB10,
            hcover12.resolve_right hB12ne, hA36⟩)
  have hA45 : z180ExactOrderTransform A 45 = 0 := by
    rcases hcover45 with hA45 | hB45
    · exact hA45
    · obtain ⟨⟨hB15ne, hB90ne, hB180ne⟩, hB18zero, hB36zero⟩ :=
        z180_card4_pattern_of_zeros_two_four_forty_five hBcard hB2 hB4 hB45
      have hA15' := hcover15.resolve_right hB15ne
      have hA90 := hcover90.resolve_right hB90ne
      have hA180 := hcover180.resolve_right hB180ne
      apply z180_card45_transform_forty_five_zero_of_three_cases hcard
        hA3 hA5 hA9 hA15' hA90 hA180
      by_cases hB18 : z180ExactOrderTransform B 18 = 0
      · obtain ⟨hB10ne, hB30ne, hB36ne⟩ := hB18zero hB18
        exact Or.inr (Or.inl ⟨hcover10.resolve_right hB10ne,
          hcover30.resolve_right hB30ne, hcover36.resolve_right hB36ne⟩)
      · have hA18 := hcover18.resolve_right hB18
        by_cases hB36 : z180ExactOrderTransform B 36 = 0
        · obtain ⟨hB18ne, hB20ne, hB60ne⟩ := hB36zero hB36
          exact Or.inr (Or.inr ⟨hcover18.resolve_right hB18ne,
            hcover20.resolve_right hB20ne, hcover60.resolve_right hB60ne⟩)
        · exact Or.inl ⟨hA18, hcover36.resolve_right hB36⟩
  exact ⟨hA15, hA45⟩

#print axioms z180_tiling_card45_mixed_transform_zeros

end Fuglede
