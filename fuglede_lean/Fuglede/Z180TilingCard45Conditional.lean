import Fuglede.Z180TilingCard45Arithmetic

/-! # The canonical 45-point spectrum in `ZMod 180` -/

namespace Fuglede

private def z180Lift45 (x : ZMod 45) : ZMod 180 := (4 * x.val : Nat)

noncomputable def z180LiftedSpectrum45 : Finset (ZMod 180) :=
  Finset.univ.image z180Lift45

private theorem z180Lift45_injective : Function.Injective z180Lift45 := by
  decide

theorem z180LiftedSpectrum45_card : z180LiftedSpectrum45.card = 45 := by
  classical
  rw [z180LiftedSpectrum45, Finset.card_image_of_injective _ z180Lift45_injective]
  simp

private theorem z180Lift45_sub (x y : ZMod 45) :
    z180Lift45 x - z180Lift45 y = z180Lift45 (x - y) := by
  revert x y
  decide

private theorem frequencyOrder_z180Lift45 (x : ZMod 45) :
    frequencyOrder 180 (z180Lift45 x) = frequencyOrder 45 x := by
  revert x
  decide

private theorem zmod45_nonzero_frequencyOrder (x : ZMod 45) (hx : x ≠ 0) :
    frequencyOrder 45 x = 3 ∨ frequencyOrder 45 x = 5 ∨
      frequencyOrder 45 x = 9 ∨ frequencyOrder 45 x = 15 ∨
      frequencyOrder 45 x = 45 := by
  revert x
  decide

theorem z180_cyclotomicSpectrum_lifted45_of_order_zeros
    {A : Finset (ZMod 180)} (hA : A.Nonempty) (hcard : A.card = 45)
    (h3 : CyclotomicZero 180 A (60 : ZMod 180))
    (h5 : CyclotomicZero 180 A (36 : ZMod 180))
    (h9 : CyclotomicZero 180 A (20 : ZMod 180))
    (h15 : CyclotomicZero 180 A (12 : ZMod 180))
    (h45 : CyclotomicZero 180 A (4 : ZMod 180)) :
    CyclotomicSpectrum 180 A z180LiftedSpectrum45 := by
  classical
  refine ⟨hA, hcard.trans z180LiftedSpectrum45_card.symm, ?_⟩
  intro l₁ hl₁ l₂ hl₂ hlne
  rw [z180LiftedSpectrum45, Finset.mem_image] at hl₁ hl₂
  obtain ⟨x, -, rfl⟩ := hl₁
  obtain ⟨y, -, rfl⟩ := hl₂
  have hxy : x - y ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hlne (congrArg z180Lift45 h)
  rw [z180Lift45_sub]
  rcases zmod45_nonzero_frequencyOrder (x - y) hxy with
    horder | horder | horder | horder | horder
  · unfold CyclotomicZero at h3 ⊢
    rw [frequencyOrder_z180Lift45, horder]
    have hr : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
    rwa [hr] at h3
  · unfold CyclotomicZero at h5 ⊢
    rw [frequencyOrder_z180Lift45, horder]
    have hr : frequencyOrder 180 (36 : ZMod 180) = 5 := by decide
    rwa [hr] at h5
  · unfold CyclotomicZero at h9 ⊢
    rw [frequencyOrder_z180Lift45, horder]
    have hr : frequencyOrder 180 (20 : ZMod 180) = 9 := by decide
    rwa [hr] at h9
  · unfold CyclotomicZero at h15 ⊢
    rw [frequencyOrder_z180Lift45, horder]
    have hr : frequencyOrder 180 (12 : ZMod 180) = 15 := by decide
    rwa [hr] at h15
  · unfold CyclotomicZero at h45 ⊢
    rw [frequencyOrder_z180Lift45, horder]
    have hr : frequencyOrder 180 (4 : ZMod 180) = 45 := by decide
    rwa [hr] at h45

theorem z180_exists_spectrum_of_tile_card_forty_five_of_mixed_order_zeros
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 45)
    (h15 : CyclotomicZero 180 A (12 : ZMod 180))
    (h45 : CyclotomicZero 180 A (4 : ZMod 180)) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 4 := by omega
  have h3 : CyclotomicZero 180 A (60 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
      (A := B) (B := A) (p := 3) (d := (60 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  have h9 : CyclotomicZero 180 A (20 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_primePower_not_dvd_card
      (A := B) (B := A) (p := 3) (k := 1) (d := (20 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  have h5 : CyclotomicZero 180 A (36 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
      (A := B) (B := A) (p := 5) (d := (36 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  refine ⟨z180LiftedSpectrum45,
    z180_cyclotomicSpectrum_lifted45_of_order_zeros ?_ hcard h3 h5 h9 h15 h45⟩
  exact Finset.card_pos.mp (by omega)

#print axioms z180_cyclotomicSpectrum_lifted45_of_order_zeros
#print axioms z180_exists_spectrum_of_tile_card_forty_five_of_mixed_order_zeros

end Fuglede
