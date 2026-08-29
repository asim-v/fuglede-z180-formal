import Fuglede.Z180TilingCard20TwentyAggregate

/-! # Tiling implies spectrality at cardinality 20 in `ZMod 180` -/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def z180Lift20 (x : ZMod 20) : ZMod 180 := (9 * x.val : Nat)

noncomputable def z180LiftedSpectrum20 : Finset (ZMod 180) :=
  Finset.univ.image z180Lift20

private theorem z180Lift20_injective : Function.Injective z180Lift20 := by
  decide

theorem z180LiftedSpectrum20_card : z180LiftedSpectrum20.card = 20 := by
  classical
  rw [z180LiftedSpectrum20, Finset.card_image_of_injective _ z180Lift20_injective]
  simp

private theorem z180Lift20_sub (x y : ZMod 20) :
    z180Lift20 x - z180Lift20 y = z180Lift20 (x - y) := by
  revert x y
  decide

private theorem frequencyOrder_z180Lift20 (x : ZMod 20) :
    frequencyOrder 180 (z180Lift20 x) = frequencyOrder 20 x := by
  revert x
  decide

private theorem zmod20_nonzero_frequencyOrder (x : ZMod 20) (hx : x ≠ 0) :
    frequencyOrder 20 x = 2 ∨ frequencyOrder 20 x = 4 ∨
      frequencyOrder 20 x = 5 ∨ frequencyOrder 20 x = 10 ∨
      frequencyOrder 20 x = 20 := by
  revert x
  decide

theorem z180_cyclotomicSpectrum_lifted20_of_order_zeros
    {A : Finset (ZMod 180)} (hA : A.Nonempty) (hcard : A.card = 20)
    (h2 : CyclotomicZero 180 A (90 : ZMod 180))
    (h4 : CyclotomicZero 180 A (45 : ZMod 180))
    (h5 : CyclotomicZero 180 A (36 : ZMod 180))
    (h10 : CyclotomicZero 180 A (18 : ZMod 180))
    (h20 : CyclotomicZero 180 A (9 : ZMod 180)) :
    CyclotomicSpectrum 180 A z180LiftedSpectrum20 := by
  classical
  refine ⟨hA, hcard.trans z180LiftedSpectrum20_card.symm, ?_⟩
  intro l₁ hl₁ l₂ hl₂ hlne
  rw [z180LiftedSpectrum20, Finset.mem_image] at hl₁ hl₂
  obtain ⟨x, -, rfl⟩ := hl₁
  obtain ⟨y, -, rfl⟩ := hl₂
  have hxy : x - y ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hlne (congrArg z180Lift20 h)
  rw [z180Lift20_sub]
  rcases zmod20_nonzero_frequencyOrder (x - y) hxy with
    horder | horder | horder | horder | horder
  · unfold CyclotomicZero at h2 ⊢
    rw [frequencyOrder_z180Lift20, horder]
    have hr : frequencyOrder 180 (90 : ZMod 180) = 2 := by decide
    rwa [hr] at h2
  · unfold CyclotomicZero at h4 ⊢
    rw [frequencyOrder_z180Lift20, horder]
    have hr : frequencyOrder 180 (45 : ZMod 180) = 4 := by decide
    rwa [hr] at h4
  · unfold CyclotomicZero at h5 ⊢
    rw [frequencyOrder_z180Lift20, horder]
    have hr : frequencyOrder 180 (36 : ZMod 180) = 5 := by decide
    rwa [hr] at h5
  · unfold CyclotomicZero at h10 ⊢
    rw [frequencyOrder_z180Lift20, horder]
    have hr : frequencyOrder 180 (18 : ZMod 180) = 10 := by decide
    rwa [hr] at h10
  · unfold CyclotomicZero at h20 ⊢
    rw [frequencyOrder_z180Lift20, horder]
    have hr : frequencyOrder 180 (9 : ZMod 180) = 20 := by decide
    rwa [hr] at h20

theorem z180_exists_spectrum_of_tile_card_twenty
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 20) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 9 := by omega
  have h2 : CyclotomicZero 180 A (90 : ZMod 180) :=
    z180_complement_cyclotomicZero_two_of_tiles_of_odd_card
      (tiles_comm hTiles) (by omega)
  have h4 : CyclotomicZero 180 A (45 : ZMod 180) :=
    z180_complement_cyclotomicZero_four_of_tiles_of_odd_card
      (tiles_comm hTiles) (by omega)
  have h5 : CyclotomicZero 180 A (36 : ZMod 180) :=
    z180_complement_cyclotomicZero_five_of_tiles_of_not_five_dvd_card
      (tiles_comm hTiles) (by omega)
  have h3B : CyclotomicZero 180 B (60 : ZMod 180) :=
    z180_complement_cyclotomicZero_three_of_tiles_of_not_three_dvd_card
      hTiles (by omega)
  have h9B : CyclotomicZero 180 B (20 : ZMod 180) :=
    z180_complement_cyclotomicZero_nine_of_tiles_of_not_three_dvd_card
      hTiles (by omega)
  have hA2 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 2) (d := (90 : ZMod 180)) (by norm_num) (by decide) h2
  have hA4 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 4) (d := (45 : ZMod 180)) (by norm_num) (by decide) h4
  have hA5 := z180_transform_zero_of_cyclotomicZero
    (X := A) (e := 5) (d := (36 : ZMod 180)) (by norm_num) (by decide) h5
  have hB3 := z180_transform_zero_of_cyclotomicZero
    (X := B) (e := 3) (d := (60 : ZMod 180)) (by norm_num) (by decide) h3B
  have hB9 := z180_transform_zero_of_cyclotomicZero
    (X := B) (e := 9) (d := (20 : ZMod 180)) (by norm_num) (by decide) h9B
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
  have hA10 := z180_card20_transform_ten_zero_of_sharded_arithmetic
    hcard hBcard hA2 hA4 hA5 hB3 hB9 hcover6 hcover10 hcover12
      hcover15 hcover18 hcover20 hcover30 hcover36 hcover45 hcover60
      hcover90 hcover180
  have hA20 := z180_card20_transform_twenty_zero_of_sharded_arithmetic
    hcard hBcard hA2 hA5 hA10 hB3 hB9 hcover12 hcover20 hcover36
      hcover60 hcover180
  have h10 := z180_cyclotomicZero_of_transform_zero
    (X := A) (e := 10) (d := (18 : ZMod 180)) (by norm_num) (by decide) hA10
  have h20 := z180_cyclotomicZero_of_transform_zero
    (X := A) (e := 20) (d := (9 : ZMod 180)) (by norm_num) (by decide) hA20
  refine ⟨z180LiftedSpectrum20,
    z180_cyclotomicSpectrum_lifted20_of_order_zeros ?_ hcard h2 h4 h5 h10 h20⟩
  exact Finset.card_pos.mp (by omega)

#print axioms z180_cyclotomicSpectrum_lifted20_of_order_zeros
#print axioms z180_exists_spectrum_of_tile_card_twenty

end Fuglede
