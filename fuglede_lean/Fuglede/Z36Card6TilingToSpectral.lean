import Fuglede.Z36Card6ForcingClosure
import Fuglede.Z36Card18PrimePowerFiberCore
import Fuglede.Z180TilingCard12Descent

/-! # Six-point tiles of ZMod 36 are spectral

The tiling zero cover allocates exactly one of the two-primary factors
`Phi_2,Phi_4` and one of the three-primary factors `Phi_3,Phi_9` to each
side.  The already verified six-point cyclotomic forcing lemmas then force
one of five explicit difference patterns, each furnishing a spectrum.
-/

namespace Fuglede

private theorem z36_zero_order_cover_of_tiles
    {A B : Finset (ZMod 36)} (hTiles : Tiles A B)
    (m : Nat) (d : ZMod 36) (horder : frequencyOrder 36 d = m)
    (hd : d ≠ 0) :
    Z36ZeroAtOrder A m ∨ Z36ZeroAtOrder B m := by
  rcases cyclotomic_zero_cover_of_tiles hTiles d hd with hA | hB
  · left
    simpa [CyclotomicZero, Z36ZeroAtOrder, horder] using hA
  · right
    simpa [CyclotomicZero, Z36ZeroAtOrder, horder] using hB

private theorem z36_cyclotomicZero_of_zeroAtOrder
    {A : Finset (ZMod 36)} {m : Nat} (d : ZMod 36)
    (horder : frequencyOrder 36 d = m) (h : Z36ZeroAtOrder A m) :
    CyclotomicZero 36 A d := by
  simpa [CyclotomicZero, Z36ZeroAtOrder, horder] using h

private theorem z36_not_zero_two_and_four
    (A : Finset (ZMod 36)) (hcard : A.card = 6) :
    ¬ (Z36ZeroAtOrder A 2 ∧ Z36ZeroAtOrder A 4) := by
  rintro ⟨h2, h4⟩
  have hdiv := z36_four_dvd_card_of_cyclotomicZero_orders_two_and_four
    A (d₂ := (18 : ZMod 36)) (d₄ := (9 : ZMod 36))
    (by decide) (by decide)
    (z36_cyclotomicZero_of_zeroAtOrder 18 (by decide) h2)
    (z36_cyclotomicZero_of_zeroAtOrder 9 (by decide) h4)
  rw [hcard] at hdiv
  norm_num at hdiv

private theorem z36_prime_power_allocation_of_six_by_six
    {A B : Finset (ZMod 36)} (hTiles : Tiles A B)
    (hAcard : A.card = 6) (hBcard : B.card = 6) :
    ((Z36ZeroAtOrder A 2 ∧ Z36ZeroAtOrder B 4) ∨
      (Z36ZeroAtOrder A 4 ∧ Z36ZeroAtOrder B 2)) ∧
    ((Z36ZeroAtOrder A 3 ∧ Z36ZeroAtOrder B 9) ∨
      (Z36ZeroAtOrder A 9 ∧ Z36ZeroAtOrder B 3)) := by
  have h2 := z36_zero_order_cover_of_tiles hTiles 2 18 (by decide) (by decide)
  have h4 := z36_zero_order_cover_of_tiles hTiles 4 9 (by decide) (by decide)
  have h3 := z36_zero_order_cover_of_tiles hTiles 3 12 (by decide) (by decide)
  have h9 := z36_zero_order_cover_of_tiles hTiles 9 4 (by decide) (by decide)
  have hnA24 := z36_not_zero_two_and_four A hAcard
  have hnB24 := z36_not_zero_two_and_four B hBcard
  have hnA39 : ¬ (Z36ZeroAtOrder A 3 ∧ Z36ZeroAtOrder A 9) := by
    rintro ⟨ha3, ha9⟩
    exact z36_zero_3_and_9_impossible A hAcard ha3 ha9
  have hnB39 : ¬ (Z36ZeroAtOrder B 3 ∧ Z36ZeroAtOrder B 9) := by
    rintro ⟨hb3, hb9⟩
    exact z36_zero_3_and_9_impossible B hBcard hb3 hb9
  constructor
  · rcases h2 with ha2 | hb2 <;> rcases h4 with ha4 | hb4
    · exact (hnA24 ⟨ha2, ha4⟩).elim
    · exact Or.inl ⟨ha2, hb4⟩
    · exact Or.inr ⟨ha4, hb2⟩
    · exact (hnB24 ⟨hb2, hb4⟩).elim
  · rcases h3 with ha3 | hb3 <;> rcases h9 with ha9 | hb9
    · exact (hnA39 ⟨ha3, ha9⟩).elim
    · exact Or.inl ⟨ha3, hb9⟩
    · exact Or.inr ⟨ha9, hb3⟩
    · exact (hnB39 ⟨hb3, hb9⟩).elim

private theorem z36_spectrum236
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h2 : Z36ZeroAtOrder A 2) (h3 : Z36ZeroAtOrder A 3)
    (h6 : Z36ZeroAtOrder A 6) :
    CyclotomicSpectrum 36 A z36Card6Complement236 := by
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · rw [hcard]
    decide
  · intro x hx y hy hne
    have hord : frequencyOrder 36 (x - y) = 2 ∨
        frequencyOrder 36 (x - y) = 3 ∨
        frequencyOrder 36 (x - y) = 6 := by
      revert x y
      decide
    rcases hord with hm | hm | hm
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h2
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h3
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h6

private theorem z36_spectrum2918
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h2 : Z36ZeroAtOrder A 2) (h9 : Z36ZeroAtOrder A 9)
    (h18 : Z36ZeroAtOrder A 18) :
    CyclotomicSpectrum 36 A z36Card6Complement2918 := by
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · rw [hcard]
    decide
  · intro x hx y hy hne
    have hord : frequencyOrder 36 (x - y) = 2 ∨
        frequencyOrder 36 (x - y) = 9 ∨
        frequencyOrder 36 (x - y) = 18 := by
      revert x y
      decide
    rcases hord with hm | hm | hm
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h2
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h9
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h18

private theorem z36_spectrum3412
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h3 : Z36ZeroAtOrder A 3) (h4 : Z36ZeroAtOrder A 4)
    (h12 : Z36ZeroAtOrder A 12) :
    CyclotomicSpectrum 36 A z36Card6Complement3412 := by
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · rw [hcard]
    decide
  · intro x hx y hy hne
    have hord : frequencyOrder 36 (x - y) = 3 ∨
        frequencyOrder 36 (x - y) = 4 ∨
        frequencyOrder 36 (x - y) = 12 := by
      revert x y
      decide
    rcases hord with hm | hm | hm
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h3
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h4
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h12

private theorem z36_spectrum491236
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h4 : Z36ZeroAtOrder A 4) (h9 : Z36ZeroAtOrder A 9)
    (h12 : Z36ZeroAtOrder A 12) (h36 : Z36ZeroAtOrder A 36) :
    CyclotomicSpectrum 36 A z36Card6Complement491836 := by
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · rw [hcard]
    decide
  · intro x hx y hy hne
    have hord : frequencyOrder 36 (x - y) = 4 ∨
        frequencyOrder 36 (x - y) = 9 ∨
        frequencyOrder 36 (x - y) = 12 ∨
        frequencyOrder 36 (x - y) = 36 := by
      revert x y
      decide
    rcases hord with hm | hm | hm | hm
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h4
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h9
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h12
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h36

private theorem z36_spectrum491836
    {A : Finset (ZMod 36)} (hcard : A.card = 6)
    (h4 : Z36ZeroAtOrder A 4) (h9 : Z36ZeroAtOrder A 9)
    (h18 : Z36ZeroAtOrder A 18) (h36 : Z36ZeroAtOrder A 36) :
    CyclotomicSpectrum 36 A z36Card6Complement491236 := by
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · rw [hcard]
    decide
  · intro x hx y hy hne
    have hord : frequencyOrder 36 (x - y) = 4 ∨
        frequencyOrder 36 (x - y) = 9 ∨
        frequencyOrder 36 (x - y) = 18 ∨
        frequencyOrder 36 (x - y) = 36 := by
      revert x y
      decide
    rcases hord with hm | hm | hm | hm
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h4
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h9
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h18
    · exact z36_cyclotomicZero_of_zeroAtOrder (x - y) hm h36

/-- Every six-point tile of `ZMod 36` is spectral. -/
theorem z36_exists_spectrum_of_tile_card_six
    {A B : Finset (ZMod 36)} (hTiles : Tiles A B)
    (hcard : A.card = 6) :
    ∃ L : Finset (ZMod 36), CyclotomicSpectrum 36 A L := by
  have hprod : A.card * B.card = 36 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  rw [hcard] at hprod
  have hBcard : B.card = 6 := by omega
  obtain ⟨h24, h39⟩ :=
    z36_prime_power_allocation_of_six_by_six hTiles hcard hBcard
  have h6 := z36_zero_order_cover_of_tiles hTiles 6 6 (by decide) (by decide)
  have h12 := z36_zero_order_cover_of_tiles hTiles 12 3 (by decide) (by decide)
  have h18 := z36_zero_order_cover_of_tiles hTiles 18 2 (by decide) (by decide)
  have h36 := z36_zero_order_cover_of_tiles hTiles 36 1 (by decide) (by decide)
  rcases h24 with hA24 | hA42 <;> rcases h39 with hA39 | hA93
  · obtain ⟨hA2, hB4⟩ := hA24
    obtain ⟨hA3, hB9⟩ := hA39
    have hA6 : Z36ZeroAtOrder A 6 := by
      by_contra hnA6
      have hB6 : Z36ZeroAtOrder B 6 := h6.resolve_left hnA6
      have hnA18 : ¬ Z36ZeroAtOrder A 18 := by
        intro hA18
        exact hnA6 (z36_zero_3_18_forces_2_6 A hcard hA3 hA18).2
      have hB18 : Z36ZeroAtOrder B 18 := h18.resolve_left hnA18
      have hB2 := z36_zero_6_9_18_forces_2 B hBcard hB6 hB9 hB18
      exact (z36_not_zero_two_and_four B hBcard) ⟨hB2, hB4⟩
    exact ⟨z36Card6Complement236, z36_spectrum236 hcard hA2 hA3 hA6⟩
  · obtain ⟨hA2, hB4⟩ := hA24
    obtain ⟨hA9, hB3⟩ := hA93
    have hA18 : Z36ZeroAtOrder A 18 := by
      by_contra hnA18
      have hB18 : Z36ZeroAtOrder B 18 := h18.resolve_left hnA18
      have hB2 := (z36_zero_3_18_forces_2_6 B hBcard hB3 hB18).1
      exact (z36_not_zero_two_and_four B hBcard) ⟨hB2, hB4⟩
    exact ⟨z36Card6Complement2918, z36_spectrum2918 hcard hA2 hA9 hA18⟩
  · obtain ⟨hA4, hB2⟩ := hA42
    obtain ⟨hA3, hB9⟩ := hA39
    have hA12 : Z36ZeroAtOrder A 12 := by
      by_contra hnA12
      have hB12 : Z36ZeroAtOrder B 12 := h12.resolve_left hnA12
      have hnA36 : ¬ Z36ZeroAtOrder A 36 := by
        intro hA36
        exact hnA12 (z36_zero_3_36_forces_4_12 A hcard hA3 hA36).2
      have hB36 : Z36ZeroAtOrder B 36 := h36.resolve_left hnA36
      have hB4 := z36_zero_9_12_36_forces_4 B hBcard hB9 hB12 hB36
      exact (z36_not_zero_two_and_four B hBcard) ⟨hB2, hB4⟩
    exact ⟨z36Card6Complement3412, z36_spectrum3412 hcard hA3 hA4 hA12⟩
  · obtain ⟨hA4, hB2⟩ := hA42
    obtain ⟨hA9, hB3⟩ := hA93
    have hA36 : Z36ZeroAtOrder A 36 := by
      by_contra hnA36
      have hB36 : Z36ZeroAtOrder B 36 := h36.resolve_left hnA36
      have hB4 := (z36_zero_3_36_forces_4_12 B hBcard hB3 hB36).1
      exact (z36_not_zero_two_and_four B hBcard) ⟨hB2, hB4⟩
    rcases z36_zero_36_forces_12_or_18 A hcard hA36 with hA12 | hA18
    · exact ⟨z36Card6Complement491836,
        z36_spectrum491236 hcard hA4 hA9 hA12 hA36⟩
    · exact ⟨z36Card6Complement491236,
        z36_spectrum491836 hcard hA4 hA9 hA18 hA36⟩

/-- Every six-point tile of `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_six
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 6) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  obtain ⟨C, hTiles36, hprojectionCard⟩ :=
    z180_tile_descends_to_z36_of_five_not_dvd_card hTiles (by omega)
  have hprojectionCard6 : (A.image z180TileProjection36).card = 6 :=
    hprojectionCard.trans hcard
  obtain ⟨L, hSpectrum36⟩ :=
    z36_exists_spectrum_of_tile_card_six hTiles36 hprojectionCard6
  have hFourier36 : FourierSpectrum (A.image z180TileProjection36) L :=
    (cyclotomicSpectrum_iff_fourierSpectrum _ _).mp hSpectrum36
  have hprojectionInj : Set.InjOn z180TileProjection36 A := by
    apply Finset.card_image_iff.mp
    exact hprojectionCard
  let L180 : Finset (ZMod 180) := L.image z36ScaleFive
  refine ⟨L180, (cyclotomicSpectrum_iff_fourierSpectrum _ _).mpr ?_⟩
  refine ⟨Finset.card_pos.mp (by omega), ?_, ?_⟩
  · calc
      A.card = (A.image z180TileProjection36).card := hprojectionCard.symm
      _ = L.card := hFourier36.2.1
      _ = L180.card := by
        symm
        exact Finset.card_image_of_injective L z36ScaleFive_injective
  · intro l₁ hl₁ l₂ hl₂ hlne
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.mp (by simpa [L180] using hl₁)
    obtain ⟨d₂, hd₂, rfl⟩ := Finset.mem_image.mp (by simpa [L180] using hl₂)
    have hdne : d₁ ≠ d₂ := by
      intro h
      subst d₂
      exact hlne rfl
    rw [← map_sub]
    rw [← fourierSum_image_projection36 A (d₁ - d₂) hprojectionInj]
    exact hFourier36.2.2 d₁ hd₁ d₂ hd₂ hdne

#print axioms z36_exists_spectrum_of_tile_card_six
#print axioms z180_exists_spectrum_of_tile_card_six

end Fuglede
