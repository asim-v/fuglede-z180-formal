import Fuglede.Z180K30JointEigenvalueIdentitiesV18
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.Matrix

/-! A matrix Gram operator on the six-dimensional Euclidean space. -/

namespace Fuglede

open Module.End

noncomputable section

abbrev Z180K30BlockMatrixV19 := Matrix (Fin 6) (Fin 6) Complex

noncomputable def z180K30GramOfMatrixV19
    (M : Z180K30BlockMatrixV19) :
    Module.End Complex Z180K30JointSpaceV5 :=
  LinearMap.adjoint (Matrix.toEuclideanLin M) * Matrix.toEuclideanLin M

theorem z180K30GramOfMatrixV19_symmetric
    (M : Z180K30BlockMatrixV19) :
    LinearMap.IsSymmetric (z180K30GramOfMatrixV19 M) := by
  exact LinearMap.isSymmetric_adjoint_mul_self (Matrix.toEuclideanLin M)

theorem z180K30GramOfMatrixV19_nonnegative
    (M : Z180K30BlockMatrixV19) (x : Z180K30JointSpaceV5) :
    0 ≤ Complex.re (inner Complex x (z180K30GramOfMatrixV19 M x)) := by
  exact LinearMap.re_inner_adjoint_mul_self_nonneg
    (Matrix.toEuclideanLin M) x

#print axioms z180K30GramOfMatrixV19_symmetric
#print axioms z180K30GramOfMatrixV19_nonnegative

end
end Fuglede
