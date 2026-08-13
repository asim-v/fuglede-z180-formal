import Fuglede.CyclicCertificate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The finite-dimensional core of spectral duality

For a square Fourier evaluation matrix, orthogonality of its columns implies
orthogonality of its rows.  This file isolates that purely linear-algebraic
step.  The scalar `c` is kept explicit because an unnormalised Fourier matrix
has Gram matrix `c I`, with `c` equal to the cardinality of the spectral set.

The current definition `CyclotomicSpectrum N A L` is phrased using
divisibility of the integer mask polynomial by cyclotomic polynomials.  To
derive `CyclotomicSpectrum N L A` from the results below, the project still
needs the following analytic/algebraic interface:

* a chosen primitive `N`-th root of unity and the evaluation matrix indexed
  by `A` and `L`;
* a theorem identifying `CyclotomicZero N A d` with vanishing of the
  corresponding character sum;
* entrywise identifications of the two Gram matrices with those character
  sums.

No such interface is assumed here, so the results below introduce no axioms
and make no claim stronger than the matrix argument they formalise.
-/

namespace Fuglede

open Matrix

variable {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]
variable {𝕂 : Type*} [Field 𝕂] [StarRing 𝕂]

/-- The inner product of columns `j` and `k` of a matrix, written explicitly
so later Fourier code can use this result without unfolding matrix products. -/
def columnGram (M : Matrix ρ κ 𝕂) (j k : κ) : 𝕂 :=
  ∑ i, star (M i j) * M i k

/-- The inner product of rows `i` and `k` of a matrix. -/
def rowGram (M : Matrix ρ κ 𝕂) (i k : ρ) : 𝕂 :=
  ∑ j, M i j * star (M k j)

/-- A matrix between equally sized finite index types whose column Gram
matrix is the identity also has row Gram matrix equal to the identity.  This
is the finite-dimensional fact that a left inverse is also a right inverse.

Keeping the two index types distinct is useful for Fourier matrices: their
rows are indexed by `↥A`, their columns by `↥L`, and a spectrum gives only
the cardinal equality between those two types. -/
theorem self_mul_conjTranspose_eq_one_of_card_eq
    (M : Matrix ρ κ 𝕂) (hcard : Fintype.card ρ = Fintype.card κ)
    (h : Mᴴ * M = 1) :
    M * Mᴴ = 1 := by
  exact (Matrix.mul_eq_one_comm_of_card_eq κ ρ 𝕂 hcard.symm).mp h

/-- Unnormalised form of spectral duality: if the column Gram matrix of a
square matrix is `c I`, for nonzero `c`, then its row Gram matrix is `c I`. -/
theorem self_mul_conjTranspose_eq_smul_one_of_card_eq
    (M : Matrix ρ κ 𝕂) (hcard : Fintype.card ρ = Fintype.card κ)
    (c : 𝕂) (hc : c ≠ 0)
    (h : Mᴴ * M = c • (1 : Matrix κ κ 𝕂)) :
    M * Mᴴ = c • (1 : Matrix ρ ρ 𝕂) := by
  have hleft : (c⁻¹ • Mᴴ) * M = 1 := by
    rw [Matrix.smul_mul, h]
    simp [smul_smul, hc]
  have hright : M * (c⁻¹ • Mᴴ) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq κ ρ 𝕂 hcard.symm).mp hleft
  have hscaled : c⁻¹ • (M * Mᴴ) = (1 : Matrix ρ ρ 𝕂) := by
    simpa only [Matrix.mul_smul] using hright
  have hrescaled := congrArg (fun X : Matrix ρ ρ 𝕂 ↦ c • X) hscaled
  simpa [smul_smul, hc] using hrescaled

/-- Entrywise form used by Fourier matrices: pairwise orthogonal columns of
equal nonzero squared norm `c` force pairwise orthogonal rows with the same
norm. -/
theorem rowGram_eq_ite_of_columnGram_eq_ite
    (M : Matrix ρ κ 𝕂) (hcard : Fintype.card ρ = Fintype.card κ)
    (c : 𝕂) (hc : c ≠ 0)
    (hcols : ∀ j k, columnGram M j k = if j = k then c else 0) :
    ∀ i k, rowGram M i k = if i = k then c else 0 := by
  have hcolumnMatrix : Mᴴ * M = c • (1 : Matrix κ κ 𝕂) := by
    ext j k
    rw [Matrix.mul_apply]
    change columnGram M j k = _
    rw [hcols]
    by_cases hjk : j = k <;> simp [hjk]
  have hrowMatrix : M * Mᴴ = c • (1 : Matrix ρ ρ 𝕂) :=
    self_mul_conjTranspose_eq_smul_one_of_card_eq M hcard c hc hcolumnMatrix
  intro i k
  have hik := congrFun (congrFun hrowMatrix i) k
  rw [Matrix.mul_apply] at hik
  change rowGram M i k = _
  change rowGram M i k = _ at hik
  by_cases heq : i = k <;> simpa [heq] using hik

end Fuglede
