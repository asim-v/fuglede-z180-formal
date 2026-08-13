import Fuglede.Z180K30DephasedFourierBlockV51
import Fuglede.Z180K30OriginalFourierBlockTraceV46

namespace Fuglede

open scoped BigOperators ComplexConjugate

noncomputable section

@[simp]
theorem z180K30DephasedFourierBlockV51_gram_operator_v52
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) :
    z180K30GramOfMatrixV19
        (z180K30DephasedFourierBlockV51 data r s) =
      z180K30GramOfMatrixV19
        (z180K30OriginalFourierBlockV32 data r s) := by
  simp only [z180K30GramOfMatrixV19_eq_toEuclideanLin_v39]
  rw [z180K30DephasedFourierBlockV51_gram_matrix]

theorem z180K30DephasedFourierBlockV51_trace_gram_v52
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) :
    LinearMap.trace Complex Z180K30JointSpaceV5
      (z180K30GramOfMatrixV19
        (z180K30DephasedFourierBlockV51 data r s)) = 36 := by
  rw [z180K30DephasedFourierBlockV51_gram_operator_v52]
  exact z180K30OriginalFourierBlockV32_trace_gram_v46 data r s

theorem z180K30DephasedFourierBlockV51_sum_gram_matrix_v52
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L) (s : Fin 5) :
    (∑ r : Fin 5,
      Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data r s) *
        z180K30DephasedFourierBlockV51 data r s) =
      (30 : Complex) • (1 : Z180K30BlockMatrixV19) := by
  simp_rw [z180K30DephasedFourierBlockV51_gram_matrix]
  exact z180K30OriginalFourierBlockV32_sum_gram_matrix_v39
    hSpec hcard data s

theorem z180K30DephasedFourierBlockV51_sum_gram_operator_apply_v52
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L) (s : Fin 5)
    (x : Z180K30JointSpaceV5) :
    (∑ r : Fin 5,
      z180K30GramOfMatrixV19
        (z180K30DephasedFourierBlockV51 data r s) x) =
      (30 : Complex) • x := by
  simp_rw [z180K30DephasedFourierBlockV51_gram_operator_v52]
  exact z180K30OriginalFourierBlockV32_sum_gram_operator_apply_v39
    hSpec hcard data s x

#print axioms z180K30DephasedFourierBlockV51_gram_operator_v52
#print axioms z180K30DephasedFourierBlockV51_trace_gram_v52
#print axioms z180K30DephasedFourierBlockV51_sum_gram_operator_apply_v52

end
end Fuglede
