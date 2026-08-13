import Fuglede.Z180K30ProjectedFibreFourierV57
import Fuglede.Z180K30ExceptionalBoundary

namespace Fuglede

noncomputable section

theorem z180_k30_commonSpectrumAt_of_normal_v58
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L)
    (s : Fin 5)
    (hnormal : ∀ k, Z180K30GramNormalScalar
      ((z180K30DephasedFiveBlockGramDataV54
        hSpec hcard data s).toPositiveFamily.eigenvalue k)) :
    Z180K30CommonSpectrumAt A L s := by
  classical
  unfold Z180K30CommonSpectrumAt
  unfold Z180K30FiveFibresHaveCommonZ36Spectrum
  intro r
  have hAcard := data.cardA r
  have hLcard := data.cardL s
  refine ⟨Finset.card_pos.mp (by omega),
    hAcard.trans hLcard.symm, ?_⟩
  intro l₁ hl₁ l₂ hl₂ hne
  obtain ⟨k, hk⟩ :=
    z180K30ProjectedFibreEnumV57_surjective
      L s (data.cardL s) l₁ hl₁
  obtain ⟨j, hj⟩ :=
    z180K30ProjectedFibreEnumV57_surjective
      L s (data.cardL s) l₂ hl₂
  have hjk : j ≠ k := by
    intro h
    apply hne
    calc
      l₁ = z180K30ProjectedFibreEnumV57
          L s (data.cardL s) k := hk.symm
      _ = z180K30ProjectedFibreEnumV57
          L s (data.cardL s) j := by rw [h]
      _ = l₂ := hj
  let M := z180K30OriginalFourierBlockV32 data r s
  have hop :
      z180K30GramOfMatrixV19 M =
        (6 : Complex) • LinearMap.id := by
    exact z180K30OriginalGramOperator_eq_six_smul_id_v56
      hSpec hcard data s r hnormal
  have hmatrix :
      Matrix.conjTranspose M * M =
        (6 : Complex) • (1 : Z180K30BlockMatrixV19) := by
    apply (Matrix.toEuclideanLin :
      Z180K30BlockMatrixV19 ≃ₗ[Complex]
        Z180K30JointSpaceV5 →ₗ[Complex] Z180K30JointSpaceV5).injective
    calc
      Matrix.toEuclideanLin (Matrix.conjTranspose M * M) =
          z180K30GramOfMatrixV19 M :=
        (z180K30GramOfMatrixV19_eq_toEuclideanLin_v39 M).symm
      _ = (6 : Complex) • LinearMap.id := hop
      _ = Matrix.toEuclideanLin
          ((6 : Complex) • (1 : Z180K30BlockMatrixV19)) := by simp
  let d : ZMod 180 :=
    z180K30OriginalFibreEnumV32 L s (data.cardL s) k -
      z180K30OriginalFibreEnumV32 L s (data.cardL s) j
  have hslice : z180K30FifthSliceFourierSumV34 A r d = 0 := by
    have hentry := congrFun (congrFun hmatrix j) k
    rw [z180K30OriginalFourierBlockV32_conjTranspose_mul_apply_v34]
      at hentry
    simpa [M, d, hjk] using hentry
  have hfive : (ZMod.cast d : ZMod 5) = 0 := by
    dsimp [d]
    rw [ZMod.cast_sub (by norm_num : 5 ∣ 180),
      z180K30OriginalFibreEnumV32_fifth,
      z180K30OriginalFibreEnumV32_fifth]
    simp
  have hproj :
      z180K30Projection36 d = l₁ - l₂ := by
    dsimp [d]
    change
      ZMod.cast
        (z180K30OriginalFibreEnumV32 L s (data.cardL s) k -
          z180K30OriginalFibreEnumV32 L s (data.cardL s) j) = l₁ - l₂
    rw [ZMod.cast_sub (by norm_num : 36 ∣ 180)]
    change
      z180K30ProjectedFibreEnumV57 L s (data.cardL s) k -
          z180K30ProjectedFibreEnumV57 L s (data.cardL s) j =
        l₁ - l₂
    rw [hk, hj]
  have htwisted :
      fourierSum (z180K30FifthFibres36 A r)
        ((29 : ZMod 36) * (l₁ - l₂)) = 0 := by
    calc
      _ = fourierSum (z180K30FifthFibres36 A r)
          ((29 : ZMod 36) * z180K30Projection36 d) := by rw [hproj]
      _ = z180K30FifthSliceFourierSumV34 A r d :=
        (z180K30FifthSliceFourierSum_eq_twisted_projection_v57
          A r d hfive).symm
      _ = 0 := hslice
  apply cyclotomicZero_of_unit29_v57
  exact (cyclotomicZero_iff_fourierSum_zero _ _).2 htwisted

/-- The spectral block dichotomy, with its normal branch translated to the
common-spectrum statement used by the tiling closure. -/
theorem z180_k30_column_dichotomy_v58
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L)
    (s : Fin 5) :
    Z180K30CommonSpectrumAt A L s ∨
      Z180K30ExceptionalGramEigenvalueData
        (z180K30DephasedFiveBlockGramDataV54
          hSpec hcard data s).toPositiveFamily.eigenvalue := by
  exact (z180_k30_dephased_gram_dichotomy_v54
    hSpec hcard data s).imp
      (z180_k30_commonSpectrumAt_of_normal_v58
        hSpec hcard data s) id

#print axioms z180_k30_commonSpectrumAt_of_normal_v58
#print axioms z180_k30_column_dichotomy_v58

end
end Fuglede
