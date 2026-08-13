import Fuglede.Z36Card18PrimePowerFibers
import Fuglede.Z180Projection
import Fuglede.Z180SmallCardinality

/-!
# The injective `180 → 36` descent at cardinality eighteen

Since five does not divide eighteen, reduction modulo `36` is injective on
both members of a cardinality-eighteen spectral pair.  Under the explicitly
named zero-descent condition their images form a spectral pair in `ZMod 36`,
whose tiling lifts through the surjective quotient map.
-/

namespace Fuglede

/-- The additive quotient used in the cardinality-eighteen descent. -/
def z180K18Projection36 : ZMod 180 →+ ZMod 36 :=
  (ZMod.castHom (by norm_num : 36 ∣ 180) (ZMod 36)).toAddMonoidHom

@[simp]
theorem z180K18Projection36_apply (x : ZMod 180) :
    z180K18Projection36 x = ZMod.cast x := by
  rfl

theorem z180_k18_projection36_injOn
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    Set.InjOn z180K18Projection36 (A : Set (ZMod 180)) := by
  intro x hx y hy hxy
  apply z180_projection36_injOn_of_spectral_not_five_dvd hSpec
    (by norm_num [hcard]) hx hy
  simpa only [z180K18Projection36_apply] using hxy

theorem z180_k18_projection36_spectrum_injOn
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    Set.InjOn z180K18Projection36 (L : Set (ZMod 180)) := by
  intro x hx y hy hxy
  apply z180_projection36_spectrum_injOn_of_spectral_not_five_dvd hSpec
    (by norm_num [hcard]) hx hy
  simpa only [z180K18Projection36_apply] using hxy

/-- Exact orthogonality condition remaining after projecting a
cardinality-eighteen spectral pair to `ZMod 36`. -/
def Z180K18Projection36ZeroDescends
    (A L : Finset (ZMod 180)) : Prop :=
  ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
    CyclotomicZero 36 (A.image z180K18Projection36)
      (z180K18Projection36 l₁ - z180K18Projection36 l₂)

/-- Zero descent supplies the only non-cardinality field of the projected
spectral pair. -/
theorem z180_k18_projection36_cyclotomicSpectrum_of_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18)
    (hdesc : Z180K18Projection36ZeroDescends A L) :
    CyclotomicSpectrum 36
      (A.image z180K18Projection36) (L.image z180K18Projection36) := by
  have hinjA := z180_k18_projection36_injOn hSpec hcard
  have hinjL := z180_k18_projection36_spectrum_injOn hSpec hcard
  refine ⟨hSpec.1.image z180K18Projection36, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinjA,
      Finset.card_image_of_injOn hinjL]
    exact hSpec.2.1
  · intro l₁ hl₁ l₂ hl₂ hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl₁
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hl₂
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hne rfl
    exact hdesc x hx y hy hxy

/-- After injectivity, zero descent is equivalent to spectrality of the two
projected images. -/
theorem z180_k18_projection36_cyclotomicSpectrum_iff_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    CyclotomicSpectrum 36
        (A.image z180K18Projection36) (L.image z180K18Projection36) ↔
      Z180K18Projection36ZeroDescends A L := by
  constructor
  · intro himage l₁ hl₁ l₂ hl₂ hne
    have hinjL := z180_k18_projection36_spectrum_injOn hSpec hcard
    have hneImage : z180K18Projection36 l₁ ≠
        z180K18Projection36 l₂ := by
      intro heq
      exact hne (hinjL hl₁ hl₂ heq)
    exact himage.2.2 _ (Finset.mem_image_of_mem _ hl₁)
      _ (Finset.mem_image_of_mem _ hl₂) hneImage
  · exact z180_k18_projection36_cyclotomicSpectrum_of_zero_descent
      hSpec hcard

/-- A tiling of the injective projected image lifts to `ZMod 180`. -/
theorem z180_k18_exists_tiling_of_projection36_image_tile
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18)
    (himage : ∃ C : Finset (ZMod 36),
      Tiles (A.image z180K18Projection36) C) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  have hsurj : Function.Surjective z180K18Projection36 := by
    simpa [z180K18Projection36] using
      ZMod.castHom_surjective (by norm_num : 36 ∣ 180)
  have hinj := z180_k18_projection36_injOn hSpec hcard
  obtain ⟨C, hC⟩ := himage
  exact ⟨preimageFinset z180K18Projection36 C,
    lift_tiles_of_surjective z180K18Projection36 hsurj A C hinj hC⟩

/-- Conditional subgroup-induction endpoint at cardinality eighteen. -/
theorem z180_k18_exists_tiling_of_projection36_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18)
    (hdesc : Z180K18Projection36ZeroDescends A L)
    (hInduction : Z36SpectralCard18ImpliesTile) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  have hinjA := z180_k18_projection36_injOn hSpec hcard
  have himageCard : (A.image z180K18Projection36).card = 18 := by
    rw [Finset.card_image_of_injOn hinjA, hcard]
  have himageSpec :=
    z180_k18_projection36_cyclotomicSpectrum_of_zero_descent
      hSpec hcard hdesc
  obtain ⟨C, hC⟩ := hInduction _ _ himageCard himageSpec
  exact z180_k18_exists_tiling_of_projection36_image_tile
    hSpec hcard ⟨C, hC⟩

/-- A non-tiler must therefore fail projected zero descent. -/
theorem z180_k18_not_zero_descent_of_non_tiler
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18)
    (hInduction : Z36SpectralCard18ImpliesTile)
    (hnot : ¬ ∃ B : Finset (ZMod 180), Tiles A B) :
    ¬ Z180K18Projection36ZeroDescends A L := by
  intro hdesc
  exact hnot (z180_k18_exists_tiling_of_projection36_zero_descent
    hSpec hcard hdesc hInduction)

#print axioms z180_k18_projection36_cyclotomicSpectrum_iff_zero_descent
#print axioms z180_k18_exists_tiling_of_projection36_image_tile
#print axioms z180_k18_exists_tiling_of_projection36_zero_descent
#print axioms z180_k18_not_zero_descent_of_non_tiler

end Fuglede
