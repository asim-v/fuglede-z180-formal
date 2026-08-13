import Fuglede.Z180K30ExceptionalHBalanceV3

namespace Fuglede

theorem z180_k30_sixthFibre_spectrum_exceptionalResidues30_of_saturated
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (hsat : Z180K30Projection30Saturated L) :
    ∀ c : ZMod 6,
      CyclotomicSpectrum 30 (z180K30SixthFibre A c)
        (z180K30ExceptionalResidues30 L) := by
  classical
  have hcardL : L.card = 30 := hSpec.2.1.symm.trans hcard
  have hcardD :=
    z180_k30_sixthFibre_card_five_of_saturated_spectrum hSpec hcard hsat
  have hcardR : (z180K30ExceptionalResidues30 L).card = 5 := by
    exact z180_k30_projection30_image_card_five_of_saturated hsat hcardL
  intro c
  refine ⟨Finset.card_pos.mp (by rw [hcardD c]; norm_num),
    (hcardD c).trans hcardR.symm, ?_⟩
  intro r₁ hr₁ r₂ hr₂ hrne
  obtain ⟨l₁, hl₁, hl₁r⟩ := Finset.mem_image.mp hr₁
  obtain ⟨l₂, hl₂, hl₂r⟩ := Finset.mem_image.mp hr₂
  let u : ZMod 180 := l₁ - l₂
  have hprojU : z180K30Projection30 u = r₁ - r₂ := by
    simp only [u, map_sub, hl₁r, hl₂r]
  have hzeroAll : ∀ b : ZMod 6,
      fourierSum A (u + z180K30Kernel30Lift (-b)) = 0 := by
    intro b
    let l₁b : ZMod 180 := l₁ + z180K30Kernel30Lift (-b)
    have hl₁b : l₁b ∈ L := hsat l₁ hl₁ (-b)
    have hne : l₁b ≠ l₂ := by
      intro heq
      apply hrne
      rw [← hl₁r, ← hl₂r]
      have hp := congrArg z180K30Projection30 heq
      simpa only [l₁b, map_add,
        z180K30Projection30_kernel30Lift, add_zero] using hp
    have hcyclo := hSpec.2.2 l₁b hl₁b l₂ hl₂ hne
    have hfourier :=
      (cyclotomicZero_iff_fourierSum_zero A _).1 hcyclo
    convert hfourier using 1 <;> simp only [l₁b, u] <;> ring_nf
  have hlevelzero : z180K30SixLevelFourierSum A u c = 0 :=
    z180K30SixLevelFourierSum_eq_zero_of_all_lifts A u hzeroAll c
  have hphase :=
    z180K30SixLevelFourierSum_eq_phase_mul_fourierSum A u c
  rw [hphase] at hlevelzero
  have hphase_ne : ZMod.stdAddChar ((c.val : ZMod 180) * u) ≠ 0 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.coe_ne_zero _
  have hfourierD :
      fourierSum (z180K30SixthFibre A c)
        (z180K30Projection30 u) = 0 :=
    (mul_eq_zero.mp hlevelzero).resolve_left hphase_ne
  apply (cyclotomicZero_iff_fourierSum_zero
    (z180K30SixthFibre A c) (r₁ - r₂)).2
  rwa [← hprojU]

theorem z180_k30_projection30_injOn_of_saturated_spectrum
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (hsat : Z180K30Projection30Saturated L) :
    Set.InjOn z180K30Projection30 (A : Set (ZMod 180)) := by
  classical
  intro x hx y hy hproj
  have hc : z180K30Projection6 x = z180K30Projection6 y :=
    z180K30_projection6_eq_of_projection30_eq x y hproj
  let c : ZMod 6 := z180K30Projection6 x
  have hSpecD :=
    z180_k30_sixthFibre_spectrum_exceptionalResidues30_of_saturated
      hSpec hcard hsat c
  have hcardD : (z180K30SixthFibre A c).card = 5 :=
    z180_k30_sixthFibre_card_five_of_saturated_spectrum hSpec hcard hsat c
  have hinj5 := z30_k5_projection5_injOn_of_spectral hSpecD hcardD
  have hdx : z180K30SixthDigit x ∈ z180K30SixthFibre A c := by
    exact Finset.mem_image.mpr ⟨x,
      Finset.mem_filter.mpr ⟨hx, rfl⟩, rfl⟩
  have hdy : z180K30SixthDigit y ∈ z180K30SixthFibre A c := by
    exact Finset.mem_image.mpr ⟨y,
      Finset.mem_filter.mpr ⟨hy, hc.symm⟩, rfl⟩
  have hdcast :
      (ZMod.cast (z180K30SixthDigit x) : ZMod 5) =
        ZMod.cast (z180K30SixthDigit y) := by
    exact (z180K30_projection30_eq_iff_sixthDigit_cast5_eq x y hc).mp hproj
  have hdigit : z180K30SixthDigit x = z180K30SixthDigit y :=
    hinj5 hdx hdy hdcast
  apply z180K30SixthDigit_injective_on_sixth_slice c
  · exact rfl
  · exact hc.symm
  · exact hdigit

theorem z180_k30_projection30_injOn_of_all_HCosetColumns
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (hH : Z180K30AllHCosetColumnsConcrete L) :
    Set.InjOn z180K30Projection30 (A : Set (ZMod 180)) := by
  exact z180_k30_projection30_injOn_of_saturated_spectrum hSpec hcard
    (z180_k30_projection30_saturated_of_all_HCosetColumns hH)

def z180K30ExceptionalHCaseBridgeOfConcrete
    {A L : Finset (ZMod 180)}
    {boundary : Z180K30ExceptionalExternalBoundary A L}
    (certificate : Z180K30ExactExceptionalCertificate boundary)
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (hhonest : ∀ s, certificate.HCosetColumn s →
      Z180K30HCosetColumnConcrete L s) :
    Z180K30ExceptionalHCaseBridge certificate where
  projection30_injOn hall :=
    z180_k30_projection30_injOn_of_all_HCosetColumns hSpec hcard
      (fun s ↦ hhonest s (hall s))

#print axioms z180_k30_sixthFibre_spectrum_exceptionalResidues30_of_saturated
#print axioms z180_k30_projection30_injOn_of_saturated_spectrum
#print axioms z180_k30_projection30_injOn_of_all_HCosetColumns

end Fuglede
