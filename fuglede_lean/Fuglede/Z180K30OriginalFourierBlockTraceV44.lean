import Fuglede.Z180K30OriginalFourierBlockOperatorSumV39

namespace Fuglede

open scoped ComplexConjugate

noncomputable section

theorem z180K30GramOfMatrixV19_trace_of_star_mul_self_eq_one_v44
    (M : Z180K30BlockMatrixV19)
    (hM : ∀ i j, star (M i j) * M i j = 1) :
    LinearMap.trace Complex Z180K30JointSpaceV5
      (z180K30GramOfMatrixV19 M) = 36 := by
  rw [z180K30GramOfMatrixV19_eq_toEuclideanLin_v39]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.trace_toLin_eq]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, hM]

theorem z180K30OriginalFourierBlockV32_trace_gram_v44
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (r s : Fin 5) :
    LinearMap.trace Complex Z180K30JointSpaceV5
      (z180K30GramOfMatrixV19
        (z180K30OriginalFourierBlockV32 data r s)) = 36 := by
  apply z180K30GramOfMatrixV19_trace_of_star_mul_self_eq_one_v44
  intro i j
  rw [z180K30OriginalFourierBlockV32_apply, star_stdAddChar,
    ← AddChar.map_add_eq_mul]
  simp

#print axioms z180K30GramOfMatrixV19_trace_of_star_mul_self_eq_one_v44
#print axioms z180K30OriginalFourierBlockV32_trace_gram_v44

end
end Fuglede
