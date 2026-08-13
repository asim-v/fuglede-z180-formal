import Fuglede.CyclicCertificate
import Fuglede.FrequencyOrder
import Fuglede.SpectralDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Cyclotomic certificates and exact Fourier sums

This file connects the integer-polynomial definition `CyclotomicZero` to the
usual vanishing of a finite Fourier coefficient.  The bridge uses the
standard injective additive character of `ZMod N` into `ℂ`; no numerical
approximation or choice of floating-point roots is involved.
-/

namespace Fuglede

open Polynomial
open scoped ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- The unnormalised Fourier coefficient of the indicator of `A`, with the
positive-sign convention. -/
noncomputable def fourierSum (A : Finset (ZMod N)) (d : ZMod N) : ℂ :=
  ∑ a : ↥A, ZMod.stdAddChar (a.1 * d)

/-- Injectivity of the standard additive character preserves the exact
order of every element. -/
theorem isPrimitiveRoot_stdAddChar (d : ZMod N) :
    IsPrimitiveRoot (ZMod.stdAddChar d) (frequencyOrder N d) := by
  rw [frequencyOrder_eq_addOrderOf (NeZero.ne N)]
  constructor
  · rw [← AddChar.map_nsmul_eq_pow, addOrderOf_nsmul_eq_zero]
    exact AddChar.map_zero_eq_one _
  · intro k hk
    have himage : ZMod.stdAddChar (k • d) =
        ZMod.stdAddChar (0 : ZMod N) := by
      rw [AddChar.map_nsmul_eq_pow, hk, AddChar.map_zero_eq_one]
    have hz : k • d = 0 := ZMod.injective_stdAddChar himage
    exact (addOrderOf_dvd_iff_nsmul_eq_zero).2 hz

/-- A cyclotomic polynomial divides an integer polynomial exactly when that
polynomial vanishes at a primitive root of the corresponding order. -/
theorem cyclotomic_dvd_iff_aeval_primitive {n : ℕ} (hn : 0 < n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (P : Polynomial ℤ) :
    cyclotomic n ℤ ∣ P ↔ Polynomial.aeval ζ P = 0 := by
  rw [cyclotomic_eq_minpoly hζ hn]
  exact (minpoly.isIntegrallyClosed_dvd_iff (hζ.isIntegral hn) P).symm

/-- Evaluating the mask at the character value of `d` is exactly the finite
Fourier sum at `d`. -/
theorem aeval_maskPolynomial_stdAddChar (A : Finset (ZMod N)) (d : ZMod N) :
    Polynomial.aeval (ZMod.stdAddChar d) (maskPolynomial N A) =
      fourierSum A d := by
  have hpow (a : ZMod N) :
      ZMod.stdAddChar d ^ a.val = ZMod.stdAddChar (a * d) := by
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    simpa only [nsmul_eq_mul] using
      congrArg (fun x : ZMod N ↦ x * d) (ZMod.natCast_zmod_val a)
  calc
    Polynomial.aeval (ZMod.stdAddChar d) (maskPolynomial N A) =
        ∑ a ∈ A, ZMod.stdAddChar (a * d) := by
      simp [maskPolynomial, hpow]
    _ = ∑ a : ↥A, ZMod.stdAddChar (a.1 * d) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach A (fun a ↦ ZMod.stdAddChar (a * d))).symm
    _ = fourierSum A d := rfl

/-- The exact bridge used by the certificate: integer cyclotomic
divisibility is equivalent to vanishing of the corresponding complex
Fourier coefficient. -/
theorem cyclotomicZero_iff_fourierSum_zero (A : Finset (ZMod N)) (d : ZMod N) :
    CyclotomicZero N A d ↔ fourierSum A d = 0 := by
  have hord : 0 < frequencyOrder N d := by
    rw [frequencyOrder_eq_addOrderOf (NeZero.ne N)]
    exact addOrderOf_pos d
  unfold CyclotomicZero
  rw [cyclotomic_dvd_iff_aeval_primitive hord (isPrimitiveRoot_stdAddChar d)]
  rw [aeval_maskPolynomial_stdAddChar]

/-- Analytic spelling of the spectrum condition.  It is kept separate so
the linear-algebraic duality argument can be read independently of
polynomial divisibility. -/
def FourierSpectrum (A L : Finset (ZMod N)) : Prop :=
  A.Nonempty ∧ A.card = L.card ∧
    ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → fourierSum A (l₁ - l₂) = 0

theorem cyclotomicSpectrum_iff_fourierSpectrum (A L : Finset (ZMod N)) :
    CyclotomicSpectrum N A L ↔ FourierSpectrum A L := by
  simp only [CyclotomicSpectrum, FourierSpectrum]
  constructor
  · rintro ⟨hA, hcard, hzero⟩
    refine ⟨hA, hcard, ?_⟩
    intro l₁ hl₁ l₂ hl₂ hne
    exact (cyclotomicZero_iff_fourierSum_zero A (l₁ - l₂)).1
      (hzero l₁ hl₁ l₂ hl₂ hne)
  · rintro ⟨hA, hcard, hzero⟩
    refine ⟨hA, hcard, ?_⟩
    intro l₁ hl₁ l₂ hl₂ hne
    exact (cyclotomicZero_iff_fourierSum_zero A (l₁ - l₂)).2
      (hzero l₁ hl₁ l₂ hl₂ hne)

@[simp]
theorem star_stdAddChar (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, Complex.star_def,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

/-- The Fourier evaluation matrix with rows indexed by `A` and columns
indexed by `L`. -/
noncomputable def fourierMatrix (A L : Finset (ZMod N)) :
    Matrix (↥A) (↥L) ℂ :=
  fun a l ↦ ZMod.stdAddChar (a.1 * l.1)

theorem columnGram_fourierMatrix (A L : Finset (ZMod N)) (l₁ l₂ : ↥L) :
    columnGram (fourierMatrix A L) l₁ l₂ =
      fourierSum A (l₂.1 - l₁.1) := by
  have hterm (a : ZMod N) :
      star (ZMod.stdAddChar (a * l₁.1)) * ZMod.stdAddChar (a * l₂.1) =
        ZMod.stdAddChar (a * (l₂.1 - l₁.1)) := by
    rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [columnGram, fourierMatrix, fourierSum]
  exact Finset.sum_congr rfl fun a _ ↦ hterm a

theorem rowGram_fourierMatrix (A L : Finset (ZMod N)) (a₁ a₂ : ↥A) :
    rowGram (fourierMatrix A L) a₁ a₂ =
      fourierSum L (a₁.1 - a₂.1) := by
  have hterm (l : ZMod N) :
      ZMod.stdAddChar (a₁.1 * l) * star (ZMod.stdAddChar (a₂.1 * l)) =
        ZMod.stdAddChar (l * (a₁.1 - a₂.1)) := by
    rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [rowGram, fourierMatrix, fourierSum]
  exact Finset.sum_congr rfl fun l _ ↦ hterm l

@[simp]
theorem fourierSum_zero (A : Finset (ZMod N)) :
    fourierSum A 0 = (A.card : ℂ) := by
  simp [fourierSum]

/-- Spectrality is symmetric: a square Fourier evaluation matrix with
orthogonal columns has orthogonal rows. -/
theorem fourierSpectrum_dual {A L : Finset (ZMod N)}
    (h : FourierSpectrum A L) : FourierSpectrum L A := by
  rcases h with ⟨hA, hcard, horth⟩
  have hL : L.Nonempty := by
    apply Finset.card_pos.mp
    rw [← hcard]
    exact hA.card_pos
  have hmatrixCard : Fintype.card ↥A = Fintype.card ↥L := by
    simpa using hcard
  have hc : (A.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hA)
  have hcols : ∀ l₁ l₂ : ↥L,
      columnGram (fourierMatrix A L) l₁ l₂ =
        if l₁ = l₂ then (A.card : ℂ) else 0 := by
    intro l₁ l₂
    rw [columnGram_fourierMatrix]
    by_cases heq : l₁ = l₂
    · subst l₂
      simp
    · rw [if_neg heq]
      apply horth l₂.1 l₂.2 l₁.1 l₁.2
      intro hcoe
      apply heq
      exact Subtype.ext hcoe.symm
  have hrows := rowGram_eq_ite_of_columnGram_eq_ite
    (fourierMatrix A L) hmatrixCard (A.card : ℂ) hc hcols
  refine ⟨hL, hcard.symm, ?_⟩
  intro a₁ ha₁ a₂ ha₂ hne
  let i : ↥A := ⟨a₁, ha₁⟩
  let k : ↥A := ⟨a₂, ha₂⟩
  have hik : i ≠ k := by
    intro e
    exact hne (congrArg Subtype.val e)
  have hrow := hrows i k
  rw [rowGram_fourierMatrix, if_neg hik] at hrow
  exact hrow

/-- Exact polynomial form of spectral duality.  This closes the bridge from
the cyclotomic certificate language to the usual square Fourier-matrix
argument and back. -/
theorem cyclotomicSpectrum_dual {A L : Finset (ZMod N)}
    (h : CyclotomicSpectrum N A L) : CyclotomicSpectrum N L A := by
  apply (cyclotomicSpectrum_iff_fourierSpectrum L A).2
  apply fourierSpectrum_dual
  exact (cyclotomicSpectrum_iff_fourierSpectrum A L).1 h

end Fuglede
