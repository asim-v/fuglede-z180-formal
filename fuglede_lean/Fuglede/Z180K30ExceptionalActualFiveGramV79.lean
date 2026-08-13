import Fuglede.Z180K30ExceptionalRawGramSemanticsV78AggregateFix
import Fuglede.Z180K30ExceptionalRawBlockV69Fix2
import Fuglede.Z180K30ExceptionalBlockRankV77Fix2
import Fuglede.Z180K30ExceptionalTraceSquareV67Fix
import Fuglede.Z180K30ProjectiveResidueArithmeticV75Fix2
import Mathlib.Tactic

/-! The five actual dephased blocks satisfy the exact raw exceptional certificate. -/

namespace Fuglede

open scoped BigOperators ComplexConjugate
open Z180K30ExceptionalRawV2
noncomputable section

private theorem rawRow_eq_z36RawSet_v79
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (r : Fin 5) :
    z180K30ExceptionalRawRowV69Fix2 data r =
      z36RawSetV75Fix2
        (fun i => ((z180K30ExceptionalRawRowPointV69Fix2
          data r i).val : ZMod 36)) := by
  rw [z36RawSetV75Fix2_natCast_rawPoints]
  rfl

private theorem rawColumn_eq_z36RawSet_v79
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (s : Fin 5) :
    z180K30ExceptionalRawColumnV69Fix2 data s =
      z36RawSetV75Fix2
        (fun i => ((z180K30ExceptionalRawColumnPointV69Fix2
          data s i).val : ZMod 36)) := by
  rw [z36RawSetV75Fix2_natCast_rawPoints]
  rfl

private theorem rawFourier_eq_dephased_v79
    {A L : Finset (ZMod 180)}
    (data : Z180K30BalancedFibreDataV22 A L) (r s : Fin 5) :
    rawFourierV78GramFix
        (fun i => z180K30ExceptionalRawRowPointV69Fix2 data r i)
        (fun j => z180K30ExceptionalRawColumnPointV69Fix2 data s j) =
      z180K30DephasedFourierBlockV51 data r s := by
  ext i j
  exact (z180K30DephasedFourierBlockV51_apply_raw_v69Fix2
    data r s i j).symm

private theorem matrix_trace_mul_self_eq_linear_trace_comp_v79
    (M : Z180K30BlockMatrixV19) :
    Matrix.trace
        ((Matrix.conjTranspose M * M) *
          (Matrix.conjTranspose M * M)) =
      LinearMap.trace Complex Z180K30JointSpaceV5
        ((z180K30GramOfMatrixV19 M).comp
          (z180K30GramOfMatrixV19 M)) := by
  rw [z180K30GramOfMatrixV19_eq_toEuclideanLin_v39]
  have hmul :
      (Matrix.toEuclideanLin (Matrix.conjTranspose M * M)).comp
          (Matrix.toEuclideanLin (Matrix.conjTranspose M * M)) =
        Matrix.toEuclideanLin
          ((Matrix.conjTranspose M * M) *
            (Matrix.conjTranspose M * M)) := by
    simpa [Matrix.toEuclideanLin] using
      (Matrix.toLpLin_mul_same (2 : ENNReal)
        (Matrix.conjTranspose M * M)
        (Matrix.conjTranspose M * M)).symm
  rw [hmul]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.trace_toLin_eq]

theorem z180_k30_actual_exceptional_fiveGramStar_v79
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L) (s : Fin 5)
    (hex : Z180K30ExceptionalGramEigenvalueData
      (z180K30DephasedFiveBlockGramDataV54
        hSpec hcard data s).toPositiveFamily.eigenvalue) :
    fiveGramStarB
      (fun r => z180K30ExceptionalRawRowV69Fix2 data r)
      (z180K30ExceptionalRawColumnV69Fix2 data s) = true := by
  let U : Fin 5 → Fin 6 → RawPoint := fun r i =>
    z180K30ExceptionalRawRowPointV69Fix2 data r i
  let V : Fin 6 → RawPoint := fun j =>
    z180K30ExceptionalRawColumnPointV69Fix2 data s j
  have hU : ∀ r,
      List.ofFn (U r) = z180K30ExceptionalRawRowV69Fix2 data r := by
    intro r
    rfl
  have hV : List.ofFn V = z180K30ExceptionalRawColumnV69Fix2 data s := by
    rfl
  apply fiveGramStarB_of_complex_certificate_v76Fix3
    (fun r => List.ofFn (U r)) (List.ofFn V)
    (rawFiveGramComplexBridgeV76Fix3_ofFn_exists_v78AggregateFix U V)
  · intro r
    rw [hU]
    exact z180K30ExceptionalRawRowV69Fix2_validSixSetB data r
  · rw [hV]
    exact z180K30ExceptionalRawColumnV69Fix2_validSixSetB data s
  · intro r
    obtain ⟨p, q, alpha, beta, hspan⟩ :=
      z180K30DephasedFourierBlockV51_rows_span_two_of_exceptional_v77Fix2
        hSpec hcard data s hex r
    rw [hU, hV, rawRow_eq_z36RawSet_v79,
      rawColumn_eq_z36RawSet_v79]
    apply z36FourierBlockV74Fix_rankTwoProjectiveCoverB_of_span_two_v75Fix2
      _ _ p q alpha beta
    intro i j
    simpa only [z36FourierBlockV74Fix_apply,
      z180K30DephasedFourierBlockV51_apply_raw_v69Fix2] using hspan i j
  · intro r
    rw [evalGramV76Fix3_gram_ofFn_v78GramFix]
    rw [rawFourier_eq_dephased_v79]
    rw [matrix_trace_mul_self_eq_linear_trace_comp_v79]
    exact z180_k30_exceptional_trace_square_eq_936_v67Fix
      (z180K30DephasedFiveBlockGramDataV54
        hSpec hcard data s).toPositiveFamily hex r
  · change (∑ r : Fin 5,
      evalGramV76Fix3 (gram (List.ofFn (U r)) (List.ofFn V))) = _
    simp_rw [evalGramV76Fix3_gram_ofFn_v78GramFix]
    calc
      (∑ r : Fin 5,
        Matrix.conjTranspose (rawFourierV78GramFix (U r) V) *
          rawFourierV78GramFix (U r) V) =
          ∑ r : Fin 5,
            Matrix.conjTranspose
                (z180K30DephasedFourierBlockV51 data r s) *
              z180K30DephasedFourierBlockV51 data r s := by
        apply Finset.sum_congr rfl
        intro r _hr
        rw [show rawFourierV78GramFix (U r) V =
            z180K30DephasedFourierBlockV51 data r s by
          exact rawFourier_eq_dephased_v79 data r s]
      _ = _ := z180K30DephasedFourierBlockV51_sum_gram_matrix_v52
        hSpec hcard data s

#print axioms z180_k30_actual_exceptional_fiveGramStar_v79

end
end Fuglede
