import Fuglede.Z180K30DephasedGramDichotomyV54

namespace Fuglede

noncomputable section

theorem z180K30DephasedGramOperator_eq_six_smul_id_v56
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L) (s r : Fin 5)
    (hnormal : ∀ k, Z180K30GramNormalScalar
      ((z180K30DephasedFiveBlockGramDataV54
        hSpec hcard data s).toPositiveFamily.eigenvalue k)) :
    z180K30GramOfMatrixV19
        (z180K30DephasedFourierBlockV51 data r s) =
      (6 : Complex) • LinearMap.id := by
  let D := z180K30DephasedFiveBlockGramDataV54 hSpec hcard data s
  change D.toPositiveFamily.family.gram r =
    (6 : Complex) • LinearMap.id
  apply D.toPositiveFamily.family.jointBasis.toBasis.ext
  intro k
  change D.toPositiveFamily.family.gram r
      (D.toPositiveFamily.family.jointBasis k) =
    ((6 : Complex) • LinearMap.id)
      (D.toPositiveFamily.family.jointBasis k)
  rw [D.toPositiveFamily.gram_apply_jointBasis]
  rw [hnormal k r]
  simp

theorem z180K30OriginalGramOperator_eq_six_smul_id_v56
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L) (s r : Fin 5)
    (hnormal : ∀ k, Z180K30GramNormalScalar
      ((z180K30DephasedFiveBlockGramDataV54
        hSpec hcard data s).toPositiveFamily.eigenvalue k)) :
    z180K30GramOfMatrixV19
        (z180K30OriginalFourierBlockV32 data r s) =
      (6 : Complex) • LinearMap.id := by
  rw [← z180K30DephasedFourierBlockV51_gram_operator_v52 data r s]
  exact z180K30DephasedGramOperator_eq_six_smul_id_v56
    hSpec hcard data s r hnormal

#print axioms z180K30DephasedGramOperator_eq_six_smul_id_v56
#print axioms z180K30OriginalGramOperator_eq_six_smul_id_v56

end
end Fuglede
