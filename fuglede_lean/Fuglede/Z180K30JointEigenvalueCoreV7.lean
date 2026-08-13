import Fuglede.Z180K30JointEigenbasisPilotV5

/-! Real and nonnegative joint eigenvalues for the K30 Gram family. -/

namespace Fuglede

open Module.End

noncomputable section

structure Z180K30PositiveCommutingGramFamilyV7 where
  family : Z180K30CommutingSymmetricFamilyV5
  nonnegative :
    forall r x, 0 ≤ Complex.re (inner Complex x (family.gram r x))

noncomputable def Z180K30PositiveCommutingGramFamilyV7.eigenvalue
    (data : Z180K30PositiveCommutingGramFamilyV7)
    (k : Fin 6) (r : Fin 5) : Real :=
  Complex.re (data.family.jointIndex k r).val

theorem Z180K30PositiveCommutingGramFamilyV7.jointIndex_real
    (data : Z180K30PositiveCommutingGramFamilyV7)
    (k : Fin 6) (r : Fin 5) :
    (data.eigenvalue k r : Complex) =
      (data.family.jointIndex k r).val := by
  have hmem := data.family.jointBasis_mem_eigenspace k r
  have hne : Not (data.family.jointBasis k = 0) :=
    data.family.jointBasis.toBasis.ne_zero k
  have hHas : HasEigenvalue (data.family.gram r)
      (data.family.jointIndex k r).val :=
    hasEigenvalue_of_hasEigenvector
      { 1 := hmem, 2 := hne }
  exact RCLike.conj_eq_iff_re.mp
    ((data.family.symmetric r).conj_eigenvalue_eq_self hHas)

theorem Z180K30PositiveCommutingGramFamilyV7.gram_apply_jointBasis
    (data : Z180K30PositiveCommutingGramFamilyV7)
    (k : Fin 6) (r : Fin 5) :
    data.family.gram r (data.family.jointBasis k) =
      (data.eigenvalue k r : Complex) • data.family.jointBasis k := by
  have happly := mem_eigenspace_iff.mp
    (data.family.jointBasis_mem_eigenspace k r)
  rw [← data.jointIndex_real k r] at happly
  exact happly

theorem Z180K30PositiveCommutingGramFamilyV7.eigenvalue_nonnegative
    (data : Z180K30PositiveCommutingGramFamilyV7)
    (k : Fin 6) (r : Fin 5) :
    0 ≤ data.eigenvalue k r := by
  have hne : Not (data.family.jointBasis k = 0) :=
    data.family.jointBasis.toBasis.ne_zero k
  have hvec : HasEigenvector (data.family.gram r)
      (data.eigenvalue k r : Complex) (data.family.jointBasis k) := by
    refine { 1 := ?_, 2 := hne }
    apply mem_eigenspace_iff.mpr
    exact data.gram_apply_jointBasis k r
  exact eigenvalue_nonneg_of_nonneg
    (hasEigenvalue_of_hasEigenvector hvec) (data.nonnegative r)

#print axioms Z180K30PositiveCommutingGramFamilyV7.eigenvalue_nonnegative

end

end Fuglede
