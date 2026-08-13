import Fuglede.Z180K30DephasedFourierBlockGramV52
import Mathlib.Tactic

namespace Fuglede

open scoped BigOperators ComplexConjugate

noncomputable section

def z180K30OtherIndexV53 (s : Fin 5) : Fin 5 :=
  s + (1 : Fin 5)

theorem z180K30OtherIndexV53_ne (s : Fin 5) :
    z180K30OtherIndexV53 s ≠ s := by
  fin_cases s <;> decide

noncomputable def z180K30DephasedGramMatrixV53
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (r s : Fin 5) : Z180K30BlockMatrixV19 :=
  Matrix.conjTranspose (z180K30DephasedFourierBlockV51 data r s) *
    z180K30DephasedFourierBlockV51 data r s

noncomputable def z180K30DephasedCommonMatrixV53
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (s : Fin 5) : Z180K30BlockMatrixV19 :=
  (Matrix.conjTranspose
      (z180K30DephasedFourierBlockV51 data (0 : Fin 5) s) *
    z180K30DephasedFourierBlockV51 data (0 : Fin 5)
      (z180K30OtherIndexV53 s)) *
  (Matrix.conjTranspose
      (z180K30DephasedFourierBlockV51 data (0 : Fin 5)
        (z180K30OtherIndexV53 s)) *
    z180K30DephasedFourierBlockV51 data (0 : Fin 5) s)

noncomputable def z180K30DephasedCommonOperatorV53
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L)
    (s : Fin 5) : Module.End Complex Z180K30JointSpaceV5 :=
  Matrix.toEuclideanLin (z180K30DephasedCommonMatrixV53 data s)

theorem z180K30DephasedGramMatrixV53_mul_common
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (data : Z180K30BalancedFibreDataV22 A L)
    (s r u : Fin 5) (hru : r ≠ u) :
    z180K30DephasedGramMatrixV53 data r s *
        z180K30DephasedGramMatrixV53 data u s =
      z180K30DephasedCommonMatrixV53 data s := by
  have hst : s ≠ z180K30OtherIndexV53 s :=
    (z180K30OtherIndexV53_ne s).symm
  have hrow := z180K30DephasedFourierBlockV51_row_cross
    hSpec data r u s (z180K30OtherIndexV53 s) hru
  have hcolr := z180K30DephasedFourierBlockV51_column_cross
    hSpec data r (0 : Fin 5) s (z180K30OtherIndexV53 s) hst
  have hcolu := z180K30DephasedFourierBlockV51_column_cross
    hSpec data u (0 : Fin 5) (z180K30OtherIndexV53 s) s
      (z180K30OtherIndexV53_ne s)
  unfold z180K30DephasedGramMatrixV53
  unfold z180K30DephasedCommonMatrixV53
  calc
    (Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data r s) *
        z180K30DephasedFourierBlockV51 data r s) *
        (Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data u s) *
        z180K30DephasedFourierBlockV51 data u s) =
      Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data r s) *
        (z180K30DephasedFourierBlockV51 data r s *
          Matrix.conjTranspose
            (z180K30DephasedFourierBlockV51 data u s)) *
        z180K30DephasedFourierBlockV51 data u s := by
      simp only [mul_assoc]
    _ = Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data r s) *
        (z180K30DephasedFourierBlockV51 data r
            (z180K30OtherIndexV53 s) *
          Matrix.conjTranspose
            (z180K30DephasedFourierBlockV51 data u
              (z180K30OtherIndexV53 s))) *
        z180K30DephasedFourierBlockV51 data u s := by
      rw [hrow]
    _ = (Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data r s) *
        z180K30DephasedFourierBlockV51 data r
          (z180K30OtherIndexV53 s)) *
        (Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data u
            (z180K30OtherIndexV53 s)) *
        z180K30DephasedFourierBlockV51 data u s) := by
      simp only [mul_assoc]
    _ = (Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data (0 : Fin 5) s) *
        z180K30DephasedFourierBlockV51 data (0 : Fin 5)
          (z180K30OtherIndexV53 s)) *
        (Matrix.conjTranspose
          (z180K30DephasedFourierBlockV51 data (0 : Fin 5)
            (z180K30OtherIndexV53 s)) *
        z180K30DephasedFourierBlockV51 data (0 : Fin 5) s) := by
      rw [hcolr, hcolu]

theorem z180K30DephasedGramOperatorV53_comp_common
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (data : Z180K30BalancedFibreDataV22 A L)
    (s r u : Fin 5) (hru : r ≠ u) :
    (z180K30GramOfMatrixV19
        (z180K30DephasedFourierBlockV51 data r s)).comp
      (z180K30GramOfMatrixV19
        (z180K30DephasedFourierBlockV51 data u s)) =
      z180K30DephasedCommonOperatorV53 data s := by
  simp only [z180K30GramOfMatrixV19_eq_toEuclideanLin_v39]
  change
    (Matrix.toEuclideanLin
      (z180K30DephasedGramMatrixV53 data r s)).comp
        (Matrix.toEuclideanLin
          (z180K30DephasedGramMatrixV53 data u s)) =
      z180K30DephasedCommonOperatorV53 data s
  calc
    (Matrix.toEuclideanLin
      (z180K30DephasedGramMatrixV53 data r s)).comp
        (Matrix.toEuclideanLin
          (z180K30DephasedGramMatrixV53 data u s)) =
      Matrix.toEuclideanLin
        (z180K30DephasedGramMatrixV53 data r s *
          z180K30DephasedGramMatrixV53 data u s) := by
      simpa [Matrix.toEuclideanLin] using
        (Matrix.toLpLin_mul_same (2 : ENNReal)
          (z180K30DephasedGramMatrixV53 data r s)
          (z180K30DephasedGramMatrixV53 data u s)).symm
    _ = Matrix.toEuclideanLin
        (z180K30DephasedCommonMatrixV53 data s) := by
      rw [z180K30DephasedGramMatrixV53_mul_common hSpec data s r u hru]
    _ = z180K30DephasedCommonOperatorV53 data s := rfl

#print axioms z180K30DephasedGramMatrixV53_mul_common
#print axioms z180K30DephasedGramOperatorV53_comp_common

end
end Fuglede
