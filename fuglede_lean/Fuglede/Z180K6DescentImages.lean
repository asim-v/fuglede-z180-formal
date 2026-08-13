import Fuglede.Z180K6Bridge
import Fuglede.Z180SmallCardinality

/-!
# The injective `180 -> 36` descent at cardinality six

This module isolates the subgroup-induction interface.  Both members of a
cardinality-six spectral pair embed in `ZMod 36`.  Thus the only missing
orthogonality datum for their images is the explicitly named zero-descent
condition below.  A tiling of the projected set then lifts through the
surjective quotient map.
-/

namespace Fuglede

/-- The additive quotient used throughout the cardinality-six descent. -/
def z180K6Projection36 : ZMod 180 →+ ZMod 36 :=
  (ZMod.castHom (by norm_num : 36 ∣ 180) (ZMod 36)).toAddMonoidHom

@[simp]
theorem z180K6Projection36_apply (x : ZMod 180) :
    z180K6Projection36 x = ZMod.cast x := by
  rfl

theorem z180_k6_projection36_injOn
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6) :
    Set.InjOn z180K6Projection36 (A : Set (ZMod 180)) := by
  intro x hx y hy hxy
  apply z180_k6_projection36_injOn_of_spectral hSpec hcard hx hy
  simpa only [z180K6Projection36_apply] using hxy

theorem z180_k6_projection36_spectrum_injOn
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6) :
    Set.InjOn z180K6Projection36 (L : Set (ZMod 180)) := by
  intro x hx y hy hxy
  apply z180_k6_projection36_spectrum_injOn_of_spectral hSpec hcard hx hy
  simpa only [z180K6Projection36_apply] using hxy

/-- Exact orthogonality condition remaining after projecting a spectral
pair from `ZMod 180` to `ZMod 36`. -/
def Z180K6Projection36ZeroDescends
    (A L : Finset (ZMod 180)) : Prop :=
  ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ →
    CyclotomicZero 36 (A.image z180K6Projection36)
      (z180K6Projection36 l₁ - z180K6Projection36 l₂)

/-- Under zero descent, the two injective images form a genuine spectral
pair in `ZMod 36`. -/
theorem z180_k6_projection36_cyclotomicSpectrum_of_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hdesc : Z180K6Projection36ZeroDescends A L) :
    CyclotomicSpectrum 36
      (A.image z180K6Projection36) (L.image z180K6Projection36) := by
  have hinjA := z180_k6_projection36_injOn hSpec hcard
  have hinjL := z180_k6_projection36_spectrum_injOn hSpec hcard
  refine ⟨hSpec.1.image z180K6Projection36, ?_, ?_⟩
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

/-- After the injectivity gateway, zero descent is exactly the remaining
orthogonality field of the projected spectrum. -/
theorem z180_k6_projection36_cyclotomicSpectrum_iff_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6) :
    CyclotomicSpectrum 36
        (A.image z180K6Projection36) (L.image z180K6Projection36) ↔
      Z180K6Projection36ZeroDescends A L := by
  constructor
  · intro himage l₁ hl₁ l₂ hl₂ hne
    have hinjL := z180_k6_projection36_spectrum_injOn hSpec hcard
    have hneImage : z180K6Projection36 l₁ ≠
        z180K6Projection36 l₂ := by
      intro heq
      exact hne (hinjL hl₁ hl₂ heq)
    exact himage.2.2 _ (Finset.mem_image_of_mem _ hl₁)
      _ (Finset.mem_image_of_mem _ hl₂) hneImage
  · exact z180_k6_projection36_cyclotomicSpectrum_of_zero_descent
      hSpec hcard

/-- The exact smaller-modulus theorem needed by subgroup induction. -/
def Z36SpectralCard6ImpliesTile : Prop :=
  ∀ A L : Finset (ZMod 36), A.card = 6 →
    CyclotomicSpectrum 36 A L → ∃ B : Finset (ZMod 36), Tiles A B

/-- Any tiling of the injective projected image lifts to `ZMod 180`. -/
theorem z180_k6_exists_tiling_of_projection36_image_tile
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (himage : ∃ C : Finset (ZMod 36),
      Tiles (A.image z180K6Projection36) C) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  have hsurj : Function.Surjective z180K6Projection36 := by
    simpa [z180K6Projection36] using
      ZMod.castHom_surjective (by norm_num : 36 ∣ 180)
  have hinj := z180_k6_projection36_injOn hSpec hcard
  obtain ⟨C, hC⟩ := himage
  exact ⟨preimageFinset z180K6Projection36 C,
    lift_tiles_of_surjective z180K6Projection36 hsurj A C hinj hC⟩

/-- Conditional subgroup-induction endpoint. -/
theorem z180_k6_exists_tiling_of_projection36_zero_descent
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hdesc : Z180K6Projection36ZeroDescends A L)
    (hInduction : Z36SpectralCard6ImpliesTile) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  have hinjA := z180_k6_projection36_injOn hSpec hcard
  have himageCard : (A.image z180K6Projection36).card = 6 := by
    rw [Finset.card_image_of_injOn hinjA, hcard]
  have himageSpec :=
    z180_k6_projection36_cyclotomicSpectrum_of_zero_descent
      hSpec hcard hdesc
  obtain ⟨C, hC⟩ := hInduction _ _ himageCard himageSpec
  exact z180_k6_exists_tiling_of_projection36_image_tile
    hSpec hcard ⟨C, hC⟩

/-- Consequently a non-tiler must contain a projected zero failure, provided
the exact `ZMod 36`, cardinality-six theorem. -/
theorem z180_k6_not_zero_descent_of_non_tiler
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hInduction : Z36SpectralCard6ImpliesTile)
    (hnot : ¬ ∃ B : Finset (ZMod 180), Tiles A B) :
    ¬ Z180K6Projection36ZeroDescends A L := by
  intro hdesc
  exact hnot (z180_k6_exists_tiling_of_projection36_zero_descent
    hSpec hcard hdesc hInduction)

#print axioms z180_k6_projection36_cyclotomicSpectrum_iff_zero_descent
#print axioms z180_k6_exists_tiling_of_projection36_image_tile
#print axioms z180_k6_exists_tiling_of_projection36_zero_descent
#print axioms z180_k6_not_zero_descent_of_non_tiler

end Fuglede
