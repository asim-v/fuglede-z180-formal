import Fuglede.Z180K30DephasedCommonProductV53
import Fuglede.Z180K30FiveBlockGramDataV20

namespace Fuglede

open scoped BigOperators

noncomputable section

noncomputable def z180K30DephasedFiveBlockGramDataV54
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L)
    (s : Fin 5) : Z180K30FiveBlockGramDataV20 where
  block := fun r => z180K30DephasedFourierBlockV51 data r s
  sum_apply := fun x =>
    z180K30DephasedFourierBlockV51_sum_gram_operator_apply_v52
      hSpec hcard data s x
  commonProduct :=
    ⟨z180K30DephasedCommonOperatorV53 data s,
      fun r u hru =>
        z180K30DephasedGramOperatorV53_comp_common
          hSpec data s r u hru⟩
  trace_eq := fun r =>
    z180K30DephasedFourierBlockV51_trace_gram_v52 data r s

theorem z180_k30_dephased_gram_dichotomy_v54
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L)
    (s : Fin 5) :
    (∀ k, Z180K30GramNormalScalar
      ((z180K30DephasedFiveBlockGramDataV54
        hSpec hcard data s).toPositiveFamily.eigenvalue k)) ∨
      Z180K30ExceptionalGramEigenvalueData
        (z180K30DephasedFiveBlockGramDataV54
          hSpec hcard data s).toPositiveFamily.eigenvalue :=
  (z180K30DephasedFiveBlockGramDataV54
    hSpec hcard data s).dichotomy

#print axioms z180_k30_dephased_gram_dichotomy_v54

end
end Fuglede
