import Fuglede.FiniteTiling
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Exact cyclotomic certificates for cyclic Fuglede

For `A ⊆ Z/NZ`, its mask polynomial is

`m_A(X) = Σ_{a∈A} X^(a.val)`.

For a nonzero frequency difference `d`, vanishing of the Fourier sum at `d`
is certified algebraically by divisibility by the cyclotomic polynomial whose
index is the additive order `N / gcd N d.val`.  Keeping the witness as an
ordinary polynomial over `ℤ` means that Lean can check certificates without
floating-point complex arithmetic.
-/

namespace Fuglede

open Polynomial

/-- The integer mask polynomial of a subset of the cyclic group `ZMod N`. -/
noncomputable def maskPolynomial (N : ℕ) (A : Finset (ZMod N)) : Polynomial ℤ :=
  ∑ a ∈ A, X ^ a.val

/-- The additive order of a frequency in `ZMod N`, written arithmetically. -/
def frequencyOrder (N : ℕ) (d : ZMod N) : ℕ :=
  N / Nat.gcd N d.val

/-- An exact Fourier-zero certificate: a cyclotomic polynomial divides the
mask polynomial.  A proof supplies (and the kernel checks) the quotient. -/
def CyclotomicZero (N : ℕ) (A : Finset (ZMod N)) (d : ZMod N) : Prop :=
  cyclotomic (frequencyOrder N d) ℤ ∣ maskPolynomial N A

/-- `L` is a spectrum certificate for `A` when it has the right size and every
nonzero pairwise frequency difference has a cyclotomic zero certificate. -/
def CyclotomicSpectrum (N : ℕ) (A L : Finset (ZMod N)) : Prop :=
  A.Nonempty ∧ A.card = L.card ∧
    ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → CyclotomicZero N A (l₁ - l₂)

/-- The spectral-to-tiling direction at a specified cyclic modulus, expressed
entirely as a finite exact statement. -/
def SpectralImpliesTileAt (N : ℕ) : Prop :=
  ∀ A L : Finset (ZMod N), CyclotomicSpectrum N A L → ∃ B, Tiles A B

/-- The converse finite Fuglede direction: every translational tile admits
an exact cyclotomic spectrum. -/
def TileImpliesSpectralAt (N : ℕ) : Prop :=
  ∀ A B : Finset (ZMod N), Tiles A B → ∃ L, CyclotomicSpectrum N A L

/-- Both directions of finite Fuglede at a fixed cyclic modulus. -/
def FugledeAt (N : ℕ) : Prop :=
  SpectralImpliesTileAt N ∧ TileImpliesSpectralAt N

end Fuglede
