import Fuglede.Z180K30OriginalFourierBlockOperatorSumV39

namespace Fuglede

open scoped BigOperators ComplexConjugate

noncomputable section

theorem z180K30GramOfMatrixV19_trace_of_star_mul_self_eq_one_v46
    (M : Z180K30BlockMatrixV19)
    (hM : ∀ i j, star (M i j) * M i j = 1) :
    LinearMap.trace Complex Z180K30JointSpaceV5
      (z180K30GramOfMatrixV19 M) = 36 := by
  rw [z180K30GramOfMatrixV19_eq_toEuclideanLin_v39]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.trace_toLin_eq]
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
  calc
    (∑ i : Fin 6, ∑ j : Fin 6, star (M j i) * M j i) =
        ∑ i : Fin 6, ∑ _j : Fin 6, (1 : Complex) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      exact hM j i
    _ = 36 := by norm_num

theorem z180K30OriginalFourierBlockV32_trace_gram_v46
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (r s : Fin 5) :
    LinearMap.trace Complex Z180K30JointSpaceV5
      (z180K30GramOfMatrixV19
        (z180K30OriginalFourierBlockV32 data r s)) = 36 := by
  apply z180K30GramOfMatrixV19_trace_of_star_mul_self_eq_one_v46
  intro i j
  rw [z180K30OriginalFourierBlockV32_apply, star_stdAddChar,
    ← AddChar.map_add_eq_mul]
  simp

#print axioms z180K30GramOfMatrixV19_trace_of_star_mul_self_eq_one_v46
#print axioms z180K30OriginalFourierBlockV32_trace_gram_v46

end
end Fuglede
