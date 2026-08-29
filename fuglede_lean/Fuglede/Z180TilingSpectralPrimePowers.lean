import Fuglede.Z180TilingSpectralReductionV3
import Fuglede.Z180TilingPrimeAllocation

/-!
# Prime-power tile cardinalities in `ZMod 180`

For cardinalities 4, 5, and 9, prime-power allocation gives exactly the
nontrivial character orders of the corresponding canonical subgroup of the
dual group.  Those subgroups are therefore explicit spectra.
-/

namespace Fuglede

private def z180Lift4 (x : ZMod 4) : ZMod 180 := (45 * x.val : Nat)
private def z180Lift5 (x : ZMod 5) : ZMod 180 := (36 * x.val : Nat)
private def z180Lift9 (x : ZMod 9) : ZMod 180 := (20 * x.val : Nat)

private noncomputable def z180Spectrum4 : Finset (ZMod 180) :=
  Finset.univ.image z180Lift4
private noncomputable def z180Spectrum5 : Finset (ZMod 180) :=
  Finset.univ.image z180Lift5
private noncomputable def z180Spectrum9 : Finset (ZMod 180) :=
  Finset.univ.image z180Lift9

private theorem z180Lift4_injective : Function.Injective z180Lift4 := by decide
private theorem z180Lift5_injective : Function.Injective z180Lift5 := by decide
private theorem z180Lift9_injective : Function.Injective z180Lift9 := by decide

private theorem z180Spectrum4_card : z180Spectrum4.card = 4 := by
  classical
  rw [z180Spectrum4, Finset.card_image_of_injective _ z180Lift4_injective]
  simp

private theorem z180Spectrum5_card : z180Spectrum5.card = 5 := by
  classical
  rw [z180Spectrum5, Finset.card_image_of_injective _ z180Lift5_injective]
  simp

private theorem z180Spectrum9_card : z180Spectrum9.card = 9 := by
  classical
  rw [z180Spectrum9, Finset.card_image_of_injective _ z180Lift9_injective]
  simp

private theorem z180Lift4_sub (x y : ZMod 4) :
    z180Lift4 x - z180Lift4 y = z180Lift4 (x - y) := by
  revert x y
  decide

private theorem z180Lift5_sub (x y : ZMod 5) :
    z180Lift5 x - z180Lift5 y = z180Lift5 (x - y) := by
  revert x y
  decide

private theorem z180Lift9_sub (x y : ZMod 9) :
    z180Lift9 x - z180Lift9 y = z180Lift9 (x - y) := by
  revert x y
  decide

private theorem frequencyOrder_z180Lift4 (x : ZMod 4) :
    frequencyOrder 180 (z180Lift4 x) = frequencyOrder 4 x := by
  revert x
  decide

private theorem frequencyOrder_z180Lift5 (x : ZMod 5) :
    frequencyOrder 180 (z180Lift5 x) = frequencyOrder 5 x := by
  revert x
  decide

private theorem frequencyOrder_z180Lift9 (x : ZMod 9) :
    frequencyOrder 180 (z180Lift9 x) = frequencyOrder 9 x := by
  revert x
  decide

private theorem zmod4_nonzero_frequencyOrder (x : ZMod 4) (hx : x ≠ 0) :
    frequencyOrder 4 x = 2 ∨ frequencyOrder 4 x = 4 := by
  revert x
  decide

private theorem zmod5_nonzero_frequencyOrder (x : ZMod 5) (hx : x ≠ 0) :
    frequencyOrder 5 x = 5 := by
  revert x
  decide

private theorem zmod9_nonzero_frequencyOrder (x : ZMod 9) (hx : x ≠ 0) :
    frequencyOrder 9 x = 3 ∨ frequencyOrder 9 x = 9 := by
  revert x
  decide

private theorem z180_cyclotomicSpectrum4_of_zeros
    {A : Finset (ZMod 180)} (hA : A.Nonempty) (hcard : A.card = 4)
    (h2 : CyclotomicZero 180 A (90 : ZMod 180))
    (h4 : CyclotomicZero 180 A (45 : ZMod 180)) :
    CyclotomicSpectrum 180 A z180Spectrum4 := by
  classical
  refine ⟨hA, hcard.trans z180Spectrum4_card.symm, ?_⟩
  intro l₁ hl₁ l₂ hl₂ hlne
  rw [z180Spectrum4, Finset.mem_image] at hl₁ hl₂
  obtain ⟨x, -, rfl⟩ := hl₁
  obtain ⟨y, -, rfl⟩ := hl₂
  have hxy : x - y ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hlne (congrArg z180Lift4 h)
  rw [z180Lift4_sub]
  rcases zmod4_nonzero_frequencyOrder (x - y) hxy with horder | horder
  · unfold CyclotomicZero at h2 ⊢
    rw [frequencyOrder_z180Lift4, horder]
    have hr : frequencyOrder 180 (90 : ZMod 180) = 2 := by decide
    rwa [hr] at h2
  · unfold CyclotomicZero at h4 ⊢
    rw [frequencyOrder_z180Lift4, horder]
    have hr : frequencyOrder 180 (45 : ZMod 180) = 4 := by decide
    rwa [hr] at h4

private theorem z180_cyclotomicSpectrum5_of_zero
    {A : Finset (ZMod 180)} (hA : A.Nonempty) (hcard : A.card = 5)
    (h5 : CyclotomicZero 180 A (36 : ZMod 180)) :
    CyclotomicSpectrum 180 A z180Spectrum5 := by
  classical
  refine ⟨hA, hcard.trans z180Spectrum5_card.symm, ?_⟩
  intro l₁ hl₁ l₂ hl₂ hlne
  rw [z180Spectrum5, Finset.mem_image] at hl₁ hl₂
  obtain ⟨x, -, rfl⟩ := hl₁
  obtain ⟨y, -, rfl⟩ := hl₂
  have hxy : x - y ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hlne (congrArg z180Lift5 h)
  rw [z180Lift5_sub]
  have horder := zmod5_nonzero_frequencyOrder (x - y) hxy
  unfold CyclotomicZero at h5 ⊢
  rw [frequencyOrder_z180Lift5, horder]
  have hr : frequencyOrder 180 (36 : ZMod 180) = 5 := by decide
  rwa [hr] at h5

private theorem z180_cyclotomicSpectrum9_of_zeros
    {A : Finset (ZMod 180)} (hA : A.Nonempty) (hcard : A.card = 9)
    (h3 : CyclotomicZero 180 A (60 : ZMod 180))
    (h9 : CyclotomicZero 180 A (20 : ZMod 180)) :
    CyclotomicSpectrum 180 A z180Spectrum9 := by
  classical
  refine ⟨hA, hcard.trans z180Spectrum9_card.symm, ?_⟩
  intro l₁ hl₁ l₂ hl₂ hlne
  rw [z180Spectrum9, Finset.mem_image] at hl₁ hl₂
  obtain ⟨x, -, rfl⟩ := hl₁
  obtain ⟨y, -, rfl⟩ := hl₂
  have hxy : x - y ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hlne (congrArg z180Lift9 h)
  rw [z180Lift9_sub]
  rcases zmod9_nonzero_frequencyOrder (x - y) hxy with horder | horder
  · unfold CyclotomicZero at h3 ⊢
    rw [frequencyOrder_z180Lift9, horder]
    have hr : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
    rwa [hr] at h3
  · unfold CyclotomicZero at h9 ⊢
    rw [frequencyOrder_z180Lift9, horder]
    have hr : frequencyOrder 180 (20 : ZMod 180) = 9 := by decide
    rwa [hr] at h9

/-- Every four-point translational tile in `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_four
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 4) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 45 := by omega
  have h2 : CyclotomicZero 180 A (90 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
      (A := B) (B := A) (p := 2) (d := (90 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  have h4 : CyclotomicZero 180 A (45 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_primePower_not_dvd_card
      (A := B) (B := A) (p := 2) (k := 1) (d := (45 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  exact ⟨z180Spectrum4, z180_cyclotomicSpectrum4_of_zeros
    (Finset.card_pos.mp (by omega)) hcard h2 h4⟩

/-- Every five-point translational tile in `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_five
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 5) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 36 := by omega
  have h5 : CyclotomicZero 180 A (36 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
      (A := B) (B := A) (p := 5) (d := (36 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  exact ⟨z180Spectrum5, z180_cyclotomicSpectrum5_of_zero
    (Finset.card_pos.mp (by omega)) hcard h5⟩

/-- Every nine-point translational tile in `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_nine
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B) (hcard : A.card = 9) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 20 := by omega
  have h3 : CyclotomicZero 180 A (60 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_prime_not_dvd_card
      (A := B) (B := A) (p := 3) (d := (60 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  have h9 : CyclotomicZero 180 A (20 : ZMod 180) := by
    exact complement_cyclotomicZero_of_tiles_of_primePower_not_dvd_card
      (A := B) (B := A) (p := 3) (k := 1) (d := (20 : ZMod 180))
      (by norm_num) (by decide) (by decide) (tiles_comm hTiles) (by omega)
  exact ⟨z180Spectrum9, z180_cyclotomicSpectrum9_of_zeros
    (Finset.card_pos.mp (by omega)) hcard h3 h9⟩

#print axioms z180_exists_spectrum_of_tile_card_four
#print axioms z180_exists_spectrum_of_tile_card_five
#print axioms z180_exists_spectrum_of_tile_card_nine

end Fuglede
