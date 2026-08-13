import Fuglede.Z180K5Closure
import Fuglede.SpectralFourier
import Mathlib.Tactic

/-!
# Cardinality-five spectra in `ZMod 30` via asymmetric inflation to `ZMod 180`

There is no new finite classification in this module.  Representatives
`0, ..., 29` inflate the set, while multiplication by six inflates its
spectrum.  The mask polynomial is unchanged on the first side and frequency
orders are unchanged on the second side.  Hence every spectral pair in
`ZMod 30` inflates to one in `ZMod 180`, where the sealed cardinality-five
theorem applies.

The final conclusion is stronger than the exceptional-branch application:
neither member of a cardinality-five spectral pair in `ZMod 30` needs to be
assumed transversal modulo five; spectrality forces both transversals.
-/

namespace Fuglede

/-- The representative section `ZMod 30 -> ZMod 180`.  It is deliberately
not presented as an additive map. -/
def z30K5Representative180 (x : ZMod 30) : ZMod 180 :=
  (x.val : ZMod 180)

/-- The additive subgroup embedding used on the spectrum side. -/
def z30K5ScaleSix180 (x : ZMod 30) : ZMod 180 :=
  (6 * x.val : Nat)

theorem z30K5Representative180_injective :
    Function.Injective z30K5Representative180 := by
  decide

theorem z30K5ScaleSix180_injective :
    Function.Injective z30K5ScaleSix180 := by
  decide

@[simp]
theorem z30K5Representative180_val :
    ∀ x : ZMod 30, (z30K5Representative180 x).val = x.val := by
  decide

@[simp]
theorem z30K5ScaleSix180_sub :
    ∀ x y : ZMod 30,
      z30K5ScaleSix180 (x - y) =
        z30K5ScaleSix180 x - z30K5ScaleSix180 y := by
  decide

@[simp]
theorem z30K5_frequencyOrder_scaleSix180 :
    ∀ d : ZMod 30,
      frequencyOrder 180 (z30K5ScaleSix180 d) = frequencyOrder 30 d := by
  decide

@[simp]
theorem z30K5Representative180_cast5 :
    ∀ x : ZMod 30,
      (ZMod.cast (z30K5Representative180 x) : ZMod 5) = ZMod.cast x := by
  decide

@[simp]
theorem z30K5ScaleSix180_cast5 :
    ∀ x : ZMod 30,
      (ZMod.cast (z30K5ScaleSix180 x) : ZMod 5) = ZMod.cast x := by
  decide

/-- Taking the least nonnegative representatives does not change the mask
polynomial. -/
theorem maskPolynomial_z30K5Representative180
    (R : Finset (ZMod 30)) :
    maskPolynomial 180 (R.image z30K5Representative180) =
      maskPolynomial 30 R := by
  classical
  rw [maskPolynomial, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [z30K5Representative180_val]
  · intro x hx y hy hxy
    exact z30K5Representative180_injective hxy

/-- Exact cyclotomic zeros survive the asymmetric inflation. -/
theorem cyclotomicZero_z30K5_inflate
    (R : Finset (ZMod 30)) (d : ZMod 30) :
    CyclotomicZero 30 R d ↔
      CyclotomicZero 180 (R.image z30K5Representative180)
        (z30K5ScaleSix180 d) := by
  unfold CyclotomicZero
  rw [z30K5_frequencyOrder_scaleSix180,
    maskPolynomial_z30K5Representative180]

/-- Inflate a spectral pair from `ZMod 30` to `ZMod 180`: use ordinary
representatives on the set side and the order-preserving scale-six embedding
on the spectrum side. -/
theorem cyclotomicSpectrum_z30K5_inflate
    {R D : Finset (ZMod 30)}
    (hSpec : CyclotomicSpectrum 30 R D) :
    CyclotomicSpectrum 180
      (R.image z30K5Representative180)
      (D.image z30K5ScaleSix180) := by
  classical
  refine ⟨hSpec.1.image z30K5Representative180, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _
        z30K5Representative180_injective,
      Finset.card_image_of_injective _ z30K5ScaleSix180_injective]
    exact hSpec.2.1
  · intro l₁ hl₁ l₂ hl₂ hne
    obtain ⟨d₁, hd₁, rfl⟩ := Finset.mem_image.mp hl₁
    obtain ⟨d₂, hd₂, rfl⟩ := Finset.mem_image.mp hl₂
    have hdne : d₁ ≠ d₂ := by
      intro h
      subst d₂
      exact hne rfl
    rw [← z30K5ScaleSix180_sub]
    apply (cyclotomicZero_z30K5_inflate R (d₁ - d₂)).1
    exact hSpec.2.2 d₁ hd₁ d₂ hd₂ hdne

/-- Every five-point spectral set in `ZMod 30` is a complete transversal
modulo five. -/
theorem z30_k5_projection5_injOn_of_spectral
    {R D : Finset (ZMod 30)}
    (hSpec : CyclotomicSpectrum 30 R D) (hcard : R.card = 5) :
    Set.InjOn (fun x : ZMod 30 => (ZMod.cast x : ZMod 5))
      (R : Set (ZMod 30)) := by
  classical
  have hInflated := cyclotomicSpectrum_z30K5_inflate hSpec
  have hcardInflated :
      (R.image z30K5Representative180).card = 5 := by
    rw [Finset.card_image_of_injective _
      z30K5Representative180_injective, hcard]
  have hinjInflated :=
    z180_k5_projection5_injOn_of_spectral hInflated hcardInflated
  intro x hx y hy hcast
  apply z30K5Representative180_injective
  apply hinjInflated
  · exact Finset.mem_image_of_mem z30K5Representative180 hx
  · exact Finset.mem_image_of_mem z30K5Representative180 hy
  · simpa only [z30K5Representative180_cast5] using hcast

/-- The spectrum member is also a complete transversal modulo five.  This
is just the preceding theorem applied after exact spectral duality. -/
theorem z30_k5_spectrum_projection5_injOn_of_spectral
    {R D : Finset (ZMod 30)}
    (hSpec : CyclotomicSpectrum 30 R D) (hcard : R.card = 5) :
    Set.InjOn (fun x : ZMod 30 => (ZMod.cast x : ZMod 5))
      (D : Set (ZMod 30)) := by
  have hcardD : D.card = 5 := hSpec.2.1.symm.trans hcard
  exact z30_k5_projection5_injOn_of_spectral
    (cyclotomicSpectrum_dual hSpec) hcardD

#print axioms cyclotomicSpectrum_z30K5_inflate
#print axioms z30_k5_projection5_injOn_of_spectral
#print axioms z30_k5_spectrum_projection5_injOn_of_spectral

end Fuglede
