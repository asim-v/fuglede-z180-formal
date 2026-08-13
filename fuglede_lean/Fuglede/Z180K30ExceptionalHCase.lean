import Fuglede.Z180K30ExceptionalHConcrete
import Fuglede.Z30K5InflationBridge
import Mathlib.Tactic

/-!
# Closing the concrete H-coset branch at cardinality thirty

If `L` is a union of complete fibres modulo thirty, its six frequency lifts
separate the six residue classes of `A`.  For each residue `c mod 6`, the
mixed-radix quotient fibre `D_c ⊆ ZMod 30` has five points and has
`L.image z180K30Projection30` as a five-point spectrum.  The sealed
`ZMod 30`, cardinality-five bridge then makes `D_c` injective modulo five.
This is exactly injectivity of `A` modulo thirty.
-/

namespace Fuglede

open scoped BigOperators ZMod

/-- The five residues modulo thirty represented by a saturated `L`. -/
noncomputable def z180K30ExceptionalResidues30
    (L : Finset (ZMod 180)) : Finset (ZMod 30) :=
  L.image z180K30Projection30

theorem z180K30_projection6_eq_of_projection30_eq :
    ∀ x y : ZMod 180,
      z180K30Projection30 x = z180K30Projection30 y →
        z180K30Projection6 x = z180K30Projection6 y := by
  decide

/-- At base frequency zero, a six-level sum is the cardinality of the slice. -/
@[simp]
theorem z180K30SixLevelFourierSum_zero
    (X : Finset (ZMod 180)) (c : ZMod 6) :
    z180K30SixLevelFourierSum X 0 c =
      ((z180K30SixthSlice X c).card : ℂ) := by
  simp [z180K30SixLevelFourierSum]

/-- Saturation of the spectrum balances `A` over its six residue classes. -/
theorem z180_k30_sixthFibre_card_five_of_saturated_spectrum
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (hsat : Z180K30Projection30Saturated L) :
    ∀ c : ZMod 6, (z180K30SixthFibre A c).card = 5 := by
  classical
  have hcardL : L.card = 30 := hSpec.2.1.symm.trans hcard
  have hLnonempty : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨l, hl⟩ := hLnonempty
  have hzero : ∀ b : ZMod 6, b ≠ 0 →
      fourierSum A (0 + z180K30Kernel30Lift (-b)) = 0 := by
    intro b hb
    have hlb : l + z180K30Kernel30Lift (-b) ∈ L := hsat l hl (-b)
    have hne : l + z180K30Kernel30Lift (-b) ≠ l := by
      intro heq
      have hzeroLift : z180K30Kernel30Lift (-b) = 0 := by
        exact add_left_cancel (heq.trans (add_zero l).symm)
      have hbzero : -b = 0 := z180K30Kernel30Lift_injective
        (hzeroLift.trans z180K30Kernel30Lift_zero.symm)
      exact hb (neg_eq_zero.mp hbzero)
    have hcyclo := hSpec.2.2
      (l + z180K30Kernel30Lift (-b)) hlb l hl hne
    have hfourier :=
      (cyclotomicZero_iff_fourierSum_zero A _).1 hcyclo
    convert hfourier using 1 <;> ring
  have heqLevel : ∀ c c' : ZMod 6,
      z180K30SixLevelFourierSum A 0 c =
        z180K30SixLevelFourierSum A 0 c' := by
    apply eq_of_dft_eq_zero_off_zero
    intro b hb
    rw [← fourierSum_add_kernel30Lift_eq_dft]
    exact hzero b hb
  have hsum :
      (∑ c : ZMod 6, z180K30SixLevelFourierSum A 0 c) = (30 : ℂ) := by
    rw [sum_z180K30SixLevelFourierSum_eq, fourierSum_zero, hcard]
  intro c
  have hlevel : z180K30SixLevelFourierSum A 0 c = 5 := by
    have hsix : (6 : ℂ) * z180K30SixLevelFourierSum A 0 c = 30 := by
      rw [← hsum]
      simp_rw [heqLevel _ c]
      norm_num
    linear_combination hsix / 6
  have hslice : (z180K30SixthSlice A c).card = 5 := by
    have := hlevel
    rw [z180K30SixLevelFourierSum_zero] at this
    exact_mod_cast this
  rw [z180K30SixthFibre, z180K30SixthSlice,
    Finset.card_image_iff.mpr]
  · exact hslice
  · intro x hx y hy hxy
    apply z180K30SixthDigit_injective_on_sixth_slice c
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hy).2
    · exact hxy

/-- Every mixed-radix quotient fibre of `A` has the five projected residues
of `L` as a spectrum in `ZMod 30`. -/
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
      have := congrArg z180K30Projection30 heq
      simpa only [l₁b, map_add,
        z180K30Projection30_kernel30Lift, add_zero] using this
    have hcyclo := hSpec.2.2 l₁b hl₁b l₂ hl₂ hne
    have hfourier :=
      (cyclotomicZero_iff_fourierSum_zero A _).1 hcyclo
    convert hfourier using 1 <;> simp only [l₁b, u] <;> ring
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

/-- Saturation of `L` forces injectivity of `A` modulo thirty. -/
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

/-- Concrete H-cosets imply the projection-thirty endpoint. -/
theorem z180_k30_projection30_injOn_of_all_HCosetColumns
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (hH : Z180K30AllHCosetColumnsConcrete L) :
    Set.InjOn z180K30Projection30 (A : Set (ZMod 180)) := by
  exact z180_k30_projection30_injOn_of_saturated_spectrum hSpec hcard
    (z180_k30_projection30_saturated_of_all_HCosetColumns hH)

/-- Tiny compatibility adapter for the abstract boundary module.  The only
extra field says that its abstract `HCosetColumn` really implies the concrete
coset statement above. -/
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
