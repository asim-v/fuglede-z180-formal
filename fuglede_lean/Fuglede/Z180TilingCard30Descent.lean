import Fuglede.Z36Card6NonzeroSpectrum
import Fuglede.Z180TilingModFiveDescent
import Fuglede.Z180SmallCardinality
import Fuglede.Z180TilingSpectralLargePrimeComplements

/-!
# Thirty-point tiles of `ZMod 180` are spectral

Dilate the six-point tiling complement by five and project it to `ZMod 36`.
The explicit six-frequency theorem in `ZMod 36` is then lifted through all
five fibres of the quotient map, producing a thirty-point spectrum.
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem z180_projection36_surjective :
    Function.Surjective z180TileProjection36 := by
  simpa [z180TileProjection36] using
    ZMod.castHom_surjective (by norm_num : 36 ∣ 180)

private theorem z180_projection36_fiber_card
    (y : ZMod 36) :
    ((Finset.univ : Finset (ZMod 180)).filter
      (fun x => z180TileProjection36 x = y)).card = 5 := by
  let fiber : ZMod 36 → Finset (ZMod 180) := fun z =>
    Finset.univ.filter fun x => z180TileProjection36 x = z
  have hsame (z : ZMod 36) : (fiber z).card = (fiber y).card := by
    simpa [fiber] using
      (AddMonoidHom.card_fiber_eq_of_mem_range z180TileProjection36
        (z180_projection36_surjective z) (z180_projection36_surjective y))
  have hpartition :
      (Finset.univ : Finset (ZMod 180)).card =
        ∑ z : ZMod 36, (fiber z).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ZMod 180)))
      (t := (Finset.univ : Finset (ZMod 36)))
      (f := z180TileProjection36) (by simp)
    simpa [fiber] using h
  have htotal : 180 = 36 * (fiber y).card := by
    calc
      180 = ∑ z : ZMod 36, (fiber z).card := by
        simpa [ZMod.card] using hpartition
      _ = ∑ _z : ZMod 36, (fiber y).card := by
        apply Finset.sum_congr rfl
        intro z _hz
        exact hsame z
      _ = 36 * (fiber y).card := by simp [ZMod.card]
  change (fiber y).card = 5
  omega

private theorem z180_card_preimage_projection36
    (Q : Finset (ZMod 36)) :
    (preimageFinset z180TileProjection36 Q).card = 5 * Q.card := by
  let L := preimageFinset z180TileProjection36 Q
  let fiber : ZMod 36 → Finset (ZMod 180) := fun z =>
    L.filter fun x => z180TileProjection36 x = z
  have hpartition : L.card = ∑ z ∈ Q, (fiber z).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := L) (t := Q) (f := z180TileProjection36) (by
        intro x hx
        exact (mem_preimageFinset z180TileProjection36 Q x).mp (by
          simpa [L] using hx))
    simpa [fiber] using h
  have hfiber (z : ZMod 36) (hz : z ∈ Q) : (fiber z).card = 5 := by
    have heq : fiber z =
        (Finset.univ : Finset (ZMod 180)).filter
          (fun x => z180TileProjection36 x = z) := by
      ext x
      simp only [fiber, L, Finset.mem_filter, Finset.mem_univ,
        mem_preimageFinset, true_and]
      constructor
      · exact fun hx => hx.2
      · intro hx
        exact ⟨hx ▸ hz, hx⟩
    rw [heq]
    exact z180_projection36_fiber_card z
  rw [hpartition]
  calc
    (∑ z ∈ Q, (fiber z).card) = ∑ _z ∈ Q, 5 := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hfiber z hz
    _ = 5 * Q.card := by simp [Nat.mul_comm]

private theorem fourierSum_image_five_nsmul
    (B : Finset (ZMod 180))
    (hinj : Set.InjOn (fun b : ZMod 180 => 5 • b) B)
    (l : ZMod 180) :
    fourierSum (B.image fun b => 5 • b) l = fourierSum B (5 • l) := by
  rw [fourierSum_eq_finset_sum, fourierSum_eq_finset_sum]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- Every thirty-point tile of `ZMod 180` is spectral. -/
theorem z180_exists_spectrum_of_tile_card_thirty
    {A B : Finset (ZMod 180)} (hTiles : Tiles A B)
    (hcard : A.card = 30) :
    ∃ L : Finset (ZMod 180), CyclotomicSpectrum 180 A L := by
  have hprod : A.card * B.card = 180 := by
    simpa using card_mul_eq_card_of_tiles hTiles
  have hBcard : B.card = 6 := by
    rw [hcard] at hprod
    omega
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let B5 : Finset (ZMod 180) := B.image fun b => 5 • b
  have hTilesB5A : Tiles B5 A := by
    simpa [B5] using tiles_image_prime_nsmul_left_of_not_dvd_card
      5 (tiles_comm hTiles) (by simp [hBcard])
  have hTilesAB5 : Tiles A B5 := tiles_comm hTilesB5A
  obtain ⟨_D, _hTiles36, hprojectionCard⟩ :=
    z180_tile_descends_to_z36_of_five_not_dvd_card
      (tiles_comm hTiles) (by simp [hBcard])
  let C : Finset (ZMod 36) := B.image z180TileProjection36
  have hCcard : C.card = 6 := by
    simpa [C, hBcard] using hprojectionCard
  have hprojectionInj : Set.InjOn z180TileProjection36 B := by
    apply Finset.card_image_iff.mp
    exact hprojectionCard
  have hfiveInj : Set.InjOn (fun b : ZMod 180 => 5 • b) B := by
    intro x hx y hy hxy
    apply hprojectionInj hx hy
    apply z36ScaleFive_injective
    simpa only [z36ScaleFive_projection36] using hxy
  obtain ⟨Q, hQcard, hQnonzero⟩ :=
    z36_exists_six_frequencies_complement_nonzero C hCcard
  let L : Finset (ZMod 180) := preimageFinset z180TileProjection36 Q
  have hLcard : L.card = 30 := by
    rw [show L.card = 5 * Q.card by
      simpa [L] using z180_card_preimage_projection36 Q, hQcard]
  have hB5Fourier (l : ZMod 180) :
      fourierSum B5 l = fourierSum C (z180TileProjection36 l) := by
    calc
      fourierSum B5 l = fourierSum B (5 • l) := by
        simpa [B5] using fourierSum_image_five_nsmul B hfiveInj l
      _ = fourierSum B (z36ScaleFive (z180TileProjection36 l)) := by
        rw [z36ScaleFive_projection36]
      _ = fourierSum C (z180TileProjection36 l) := by
        symm
        simpa [C] using fourierSum_image_projection36 B
          (z180TileProjection36 l) hprojectionInj
  have hnonzero : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
      fourierSum B5 (l₁ - l₂) ≠ 0 := by
    intro l₁ hl₁ l₂ hl₂ hlne
    rw [hB5Fourier]
    have hq₁ : z180TileProjection36 l₁ ∈ Q :=
      (mem_preimageFinset z180TileProjection36 Q l₁).mp (by simpa [L] using hl₁)
    have hq₂ : z180TileProjection36 l₂ ∈ Q :=
      (mem_preimageFinset z180TileProjection36 Q l₂).mp (by simpa [L] using hl₂)
    rw [map_sub]
    by_cases heq : z180TileProjection36 l₁ = z180TileProjection36 l₂
    · rw [heq, sub_self, fourierSum_zero, hCcard]
      norm_num
    · exact fun hz => hQnonzero _ hq₁ _ hq₂ heq
        ((cyclotomicZero_iff_fourierSum_zero C _).2 hz)
  refine ⟨L, cyclotomicSpectrum_of_tiles_of_complement_nonzero
    hTilesAB5 (Finset.card_pos.mp (by omega)) ?_ hnonzero⟩
  exact hcard.trans hLcard.symm

#print axioms z180_exists_spectrum_of_tile_card_thirty

end Fuglede
