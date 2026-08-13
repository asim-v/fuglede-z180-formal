import Fuglede.Z180K30MatrixGramPilotV19

/-! Five concrete six-by-six blocks and their Gram identities. -/

namespace Fuglede

open Module.End
open scoped BigOperators

noncomputable section

structure Z180K30FiveBlockGramDataV20 where
  block : Fin 5 -> Z180K30BlockMatrixV19
  sum_apply :
    ∀ x, (Finset.univ.sum fun r : Fin 5 =>
      z180K30GramOfMatrixV19 (block r) x) = (30 : Complex) • x
  commonProduct :
    ∃ Q : Module.End Complex Z180K30JointSpaceV5,
      ∀ r s, r ≠ s ->
        (z180K30GramOfMatrixV19 (block r)).comp
          (z180K30GramOfMatrixV19 (block s)) = Q
  trace_eq :
    ∀ r, LinearMap.trace Complex Z180K30JointSpaceV5
      (z180K30GramOfMatrixV19 (block r)) = 36

theorem Z180K30FiveBlockGramDataV20.pairwiseCommute
    (data : Z180K30FiveBlockGramDataV20) :
    Pairwise (fun r s => Commute
      (z180K30GramOfMatrixV19 (data.block r))
      (z180K30GramOfMatrixV19 (data.block s))) := by
  rcases data.commonProduct with ⟨Q, hQ⟩
  intro r s hrs
  change
    (z180K30GramOfMatrixV19 (data.block r)).comp
        (z180K30GramOfMatrixV19 (data.block s)) =
      (z180K30GramOfMatrixV19 (data.block s)).comp
        (z180K30GramOfMatrixV19 (data.block r))
  rw [hQ r s hrs, hQ s r hrs.symm]

noncomputable def Z180K30FiveBlockGramDataV20.toPositiveFamily
    (data : Z180K30FiveBlockGramDataV20) :
    Z180K30PositiveCommutingGramFamilyV7 where
  family :=
    { gram := fun r => z180K30GramOfMatrixV19 (data.block r)
      symmetric := fun r => z180K30GramOfMatrixV19_symmetric (data.block r)
      pairwiseCommute := data.pairwiseCommute }
  nonnegative := fun r x =>
    z180K30GramOfMatrixV19_nonnegative (data.block r) x

noncomputable def Z180K30FiveBlockGramDataV20.toOperatorData
    (data : Z180K30FiveBlockGramDataV20) :
    Z180K30GramOperatorDataV18 where
  core := data.toPositiveFamily
  sum_apply := data.sum_apply
  commonProduct := data.commonProduct
  trace_eq := data.trace_eq

theorem Z180K30FiveBlockGramDataV20.dichotomy
    (data : Z180K30FiveBlockGramDataV20) :
    (∀ k, Z180K30GramNormalScalar
      (data.toPositiveFamily.eigenvalue k)) ∨
      Z180K30ExceptionalGramEigenvalueData
        data.toPositiveFamily.eigenvalue :=
  data.toOperatorData.dichotomy

#print axioms Z180K30FiveBlockGramDataV20.dichotomy

end
end Fuglede
