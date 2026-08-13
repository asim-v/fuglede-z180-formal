import Fuglede.Z180K30OriginalFourierBlockSumV35
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-! Transfer of the concrete matrix Gram sum to Euclidean operators. -/

namespace Fuglede

open Module.End
open scoped BigOperators

noncomputable section

theorem z180K30GramOfMatrixV19_eq_toEuclideanLin_v37
    (M : Z180K30BlockMatrixV19) :
    z180K30GramOfMatrixV19 M =
      Matrix.toEuclideanLin (Matrix.conjTranspose M * M) := by
  rw [z180K30GramOfMatrixV19,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change
    (Matrix.toEuclideanLin (Matrix.conjTranspose M)).comp
        (Matrix.toEuclideanLin M) =
      Matrix.toEuclideanLin (Matrix.conjTranspose M * M)
  simpa [Matrix.toEuclideanLin] using
    (Matrix.toLpLin_mul_same (2 : ENNReal)
      (Matrix.conjTranspose M) M).symm

theorem z180K30OriginalFourierBlockV32_sum_gram_matrix_v37
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L) (s : Fin 5) :
    (∑ r : Fin 5,
      Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data r s) *
        z180K30OriginalFourierBlockV32 data r s) =
      (30 : Complex) • (1 : Z180K30BlockMatrixV19) := by
  ext j k
  change
    (∑ r : Fin 5,
      (Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data r s) *
        z180K30OriginalFourierBlockV32 data r s) j k) =
      (((30 : Complex) • (1 : Z180K30BlockMatrixV19)) j k)
  rw [z180K30OriginalFourierBlockV32_sum_gram_apply
    hSpec hcard data s j k]
  by_cases hjk : j = k
  · subst k
    simp
  · simp [hjk]

theorem z180K30OriginalFourierBlockV32_sum_gram_operator_apply_v37
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L) (s : Fin 5)
    (x : Z180K30JointSpaceV5) :
    (∑ r : Fin 5,
      z180K30GramOfMatrixV19
        (z180K30OriginalFourierBlockV32 data r s) x) =
      (30 : Complex) • x := by
  simp_rw [z180K30GramOfMatrixV19_eq_toEuclideanLin_v37]
  calc
    (∑ r : Fin 5,
      Matrix.toEuclideanLin
        (Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data r s) *
          z180K30OriginalFourierBlockV32 data r s) x) =
        Matrix.toEuclideanLin
          (∑ r : Fin 5,
            Matrix.conjTranspose (z180K30OriginalFourierBlockV32 data r s) *
              z180K30OriginalFourierBlockV32 data r s) x := by
      simp only [map_sum, Finset.sum_apply]
    _ = Matrix.toEuclideanLin
        ((30 : Complex) • (1 : Z180K30BlockMatrixV19)) x := by
      rw [z180K30OriginalFourierBlockV32_sum_gram_matrix_v37
        hSpec hcard data s]
    _ = (30 : Complex) • x := by simp

#print axioms z180K30GramOfMatrixV19_eq_toEuclideanLin_v37
#print axioms z180K30OriginalFourierBlockV32_sum_gram_operator_apply_v37

end
end Fuglede
