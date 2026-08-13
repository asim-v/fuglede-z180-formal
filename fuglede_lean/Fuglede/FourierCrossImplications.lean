import Fuglede.FourierEnergy
import Fuglede.SupportOrder

/-!
# Exact-support Fourier-energy cross implications

This file closes the bridge from a positive exact-support inner-distribution
mass on one member of a spectral pair to vanishing of the corresponding
exact-support energy on the other member.  The argument is exact:

* a positive mass supplies an actual ordered pair with the requested support;
* spectrality supplies one cyclotomic zero at the difference of that pair;
* `SupportOrder` shows that every frequency with the same CRT support has the
  same cyclotomic index;
* the Fourier-energy identity turns simultaneous coefficient vanishing into
  `supportEnergy = 0`.
-/

namespace Fuglede

/-- A positive exact-support inner-distribution mass is witnessed by an
actual ordered pair in the set. -/
theorem exists_pair_of_innerDistribution_pos
    {X : Finset (ZMod 2310)} {D : Finset (Fin 5)}
    (hpos : 0 < innerDistribution X D) :
    ∃ x ∈ X, ∃ y ∈ X, differenceSupport x y = D := by
  rw [innerDistribution] at hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_product] at hp
  exact ⟨p.1, hp.1.1, p.2, hp.1.2, hp.2⟩

/-- Reconstructing a CRT vector preserves its literal coordinate support. -/
theorem crt2310Support_fromCRT2310 (d : CRT2310) :
    crt2310Support (fromCRT2310 d) = crtVectorSupport d := by
  classical
  ext i
  simp only [mem_crt2310Support, mem_crtVectorSupport,
    toCRT2310_fromCRT2310]

/-- The order of a reconstructed frequency is the product of the primes in
the support of its CRT vector. -/
theorem frequencyOrder_fromCRT2310_eq_supportModulus (d : CRT2310) :
    frequencyOrder 2310 (fromCRT2310 d) =
      supportModulus (crtVectorSupport d) := by
  rw [frequencyOrder_eq_supportModulus, crt2310Support_fromCRT2310]

/-- Literal standard-character version of exact-support energy vanishing. -/
theorem supportEnergy_eq_zero_iff_fourierSum_fromCRT2310
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    supportEnergy X D = 0 ↔
      ∀ d ∈ exactCRTFrequencies D,
        fourierSum X (fromCRT2310 d) = 0 := by
  constructor
  · intro hzero
    have hsum :
        (∑ d ∈ exactCRTFrequencies D,
            Complex.normSq (fourierSum X (fromCRT2310 d))) = 0 := by
      rw [← supportEnergy_cast_real_eq_sum_normSq_fourierSum, hzero]
      norm_num
    have hall :
        ∀ d ∈ exactCRTFrequencies D,
          Complex.normSq (fourierSum X (fromCRT2310 d)) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun d hd ↦ Complex.normSq_nonneg
          (fourierSum X (fromCRT2310 d)))).mp
      exact hsum
    intro d hd
    exact Complex.normSq_eq_zero.mp (hall d hd)
  · intro hall
    have hsum :
        (∑ d ∈ exactCRTFrequencies D,
            Complex.normSq (fourierSum X (fromCRT2310 d))) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      simp [hall d hd]
    have hcast : (supportEnergy X D : ℝ) = 0 := by
      rw [supportEnergy_cast_real_eq_sum_normSq_fourierSum, hsum]
    exact_mod_cast hcast

/-- Binder form of the preceding equivalence, exposing literal CRT support
rather than membership in `exactCRTFrequencies`. -/
theorem supportEnergy_eq_zero_iff_fourierSum_of_crtVectorSupport
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    supportEnergy X D = 0 ↔
      ∀ d : CRT2310, crtVectorSupport d = D →
        fourierSum X (fromCRT2310 d) = 0 := by
  simpa only [mem_exactCRTFrequencies] using
    supportEnergy_eq_zero_iff_fourierSum_fromCRT2310 X D

/-- Cyclotomic spelling of exact-support energy vanishing. -/
theorem supportEnergy_eq_zero_iff_cyclotomicZero_fromCRT2310
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    supportEnergy X D = 0 ↔
      ∀ d ∈ exactCRTFrequencies D,
        CyclotomicZero 2310 X (fromCRT2310 d) := by
  rw [supportEnergy_eq_zero_iff_fourierSum_fromCRT2310]
  simp only [cyclotomicZero_iff_fourierSum_zero]

/-- A single cyclotomic zero annihilates the whole exact-support energy,
provided that its frequency has the requested CRT support.  Cyclotomic
divisibility depends only on `frequencyOrder`, and `SupportOrder` identifies
that order with `supportModulus D`. -/
theorem supportEnergy_eq_zero_of_cyclotomicZero_of_support
    {X : Finset (ZMod 2310)} {u : ZMod 2310} {D : Finset (Fin 5)}
    (hzero : CyclotomicZero 2310 X u)
    (hsupport : crt2310Support u = D) :
    supportEnergy X D = 0 := by
  rw [supportEnergy_eq_zero_iff_cyclotomicZero_fromCRT2310]
  intro d hd
  have hdSupport : crtVectorSupport d = D :=
    mem_exactCRTFrequencies.mp hd
  have hordD :
      frequencyOrder 2310 (fromCRT2310 d) = supportModulus D := by
    rw [frequencyOrder_fromCRT2310_eq_supportModulus, hdSupport]
  have hordU : frequencyOrder 2310 u = supportModulus D := by
    rw [frequencyOrder_eq_supportModulus, hsupport]
  unfold CyclotomicZero at hzero ⊢
  rw [hordD, ← hordU]
  exact hzero

/-- If `A` has a positive nonempty-support mass, the dual member `L` of a
cyclotomic spectral pair has zero energy on that support. -/
theorem supportEnergy_L_eq_zero_of_innerDistribution_A_pos
    {A L : Finset (ZMod 2310)}
    (hSpec : CyclotomicSpectrum 2310 A L)
    {D : Finset (Fin 5)} (hD : D ≠ ∅)
    (hpos : 0 < innerDistribution A D) :
    supportEnergy L D = 0 := by
  obtain ⟨x, hx, y, hy, hsupport⟩ :=
    exists_pair_of_innerDistribution_pos hpos
  have hxy : x ≠ y := by
    intro hxy
    apply hD
    rw [← hsupport]
    exact (differenceSupport_eq_empty_iff x y).2 hxy
  have hdual : CyclotomicSpectrum 2310 L A :=
    cyclotomicSpectrum_dual hSpec
  have hzero : CyclotomicZero 2310 L (x - y) :=
    hdual.2.2 x hx y hy hxy
  exact supportEnergy_eq_zero_of_cyclotomicZero_of_support hzero hsupport

/-- Symmetric cross implication: a positive nonempty-support mass on `L`
annihilates the corresponding energy of `A`. -/
theorem supportEnergy_A_eq_zero_of_innerDistribution_L_pos
    {A L : Finset (ZMod 2310)}
    (hSpec : CyclotomicSpectrum 2310 A L)
    {D : Finset (Fin 5)} (hD : D ≠ ∅)
    (hpos : 0 < innerDistribution L D) :
    supportEnergy A D = 0 := by
  obtain ⟨x, hx, y, hy, hsupport⟩ :=
    exists_pair_of_innerDistribution_pos hpos
  have hxy : x ≠ y := by
    intro hxy
    apply hD
    rw [← hsupport]
    exact (differenceSupport_eq_empty_iff x y).2 hxy
  have hzero : CyclotomicZero 2310 A (x - y) :=
    hSpec.2.2 x hx y hy hxy
  exact supportEnergy_eq_zero_of_cyclotomicZero_of_support hzero hsupport

/-- Fourier-spectrum entry point for the `A → L` cross implication. -/
theorem supportEnergy_L_eq_zero_of_innerDistribution_A_pos_fourier
    {A L : Finset (ZMod 2310)}
    (hSpec : FourierSpectrum A L)
    {D : Finset (Fin 5)} (hD : D ≠ ∅)
    (hpos : 0 < innerDistribution A D) :
    supportEnergy L D = 0 := by
  exact supportEnergy_L_eq_zero_of_innerDistribution_A_pos
    ((cyclotomicSpectrum_iff_fourierSpectrum A L).2 hSpec) hD hpos

/-- Fourier-spectrum entry point for the symmetric `L → A` implication. -/
theorem supportEnergy_A_eq_zero_of_innerDistribution_L_pos_fourier
    {A L : Finset (ZMod 2310)}
    (hSpec : FourierSpectrum A L)
    {D : Finset (Fin 5)} (hD : D ≠ ∅)
    (hpos : 0 < innerDistribution L D) :
    supportEnergy A D = 0 := by
  exact supportEnergy_A_eq_zero_of_innerDistribution_L_pos
    ((cyclotomicSpectrum_iff_fourierSpectrum A L).2 hSpec) hD hpos

end Fuglede
