import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Tactic

/-! A finite-index resource pilot for the K30 simultaneous eigenbasis. -/

namespace Fuglede

open Module.End

noncomputable section

abbrev Z180K30JointSpaceV5 := EuclideanSpace Complex (Fin 6)

structure Z180K30CommutingSymmetricFamilyV5 where
  gram : Fin 5 -> Module.End Complex Z180K30JointSpaceV5
  symmetric : forall r, LinearMap.IsSymmetric (gram r)
  pairwiseCommute :
    Pairwise (fun r s => Commute (gram r) (gram s))

abbrev Z180K30JointEigenvalueIndexV5
    (data : Z180K30CommutingSymmetricFamilyV5) :=
  (r : Fin 5) -> Eigenvalues (data.gram r)

def Z180K30CommutingSymmetricFamilyV5.jointIndexCoe
    (data : Z180K30CommutingSymmetricFamilyV5)
    (alpha : Z180K30JointEigenvalueIndexV5 data) :
    Fin 5 -> Complex :=
  fun r => (alpha r).val

theorem Z180K30CommutingSymmetricFamilyV5.jointIndexCoe_injective
    (data : Z180K30CommutingSymmetricFamilyV5) :
    Function.Injective data.jointIndexCoe := by
  intro alpha beta hab
  funext r
  exact Subtype.ext (congrFun hab r)

def Z180K30CommutingSymmetricFamilyV5.jointSubspace
    (data : Z180K30CommutingSymmetricFamilyV5)
    (alpha : Z180K30JointEigenvalueIndexV5 data) :
    Submodule Complex Z180K30JointSpaceV5 :=
  iInf fun r => eigenspace (data.gram r) (data.jointIndexCoe alpha r)

theorem Z180K30CommutingSymmetricFamilyV5.joint_iSup_eq_top
    (data : Z180K30CommutingSymmetricFamilyV5) :
    iSup data.jointSubspace = (⊤ : Submodule Complex Z180K30JointSpaceV5) := by
  have hfull :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
      data.symmetric data.pairwiseCommute
  apply le_antisymm
  · exact le_top
  · calc
      (⊤ : Submodule Complex Z180K30JointSpaceV5) =
          iSup (fun chi : Fin 5 -> Complex =>
            iInf fun r => eigenspace (data.gram r) (chi r)) := hfull.symm
      _ ≤ iSup data.jointSubspace := by
        apply iSup_le
        intro chi
        by_cases hjoint :
            (iInf fun r => eigenspace (data.gram r) (chi r)) = ⊥
        · rw [hjoint]
          exact bot_le
        · let alpha : Z180K30JointEigenvalueIndexV5 data := fun r =>
            {
              val := chi r
              property := by
                intro hr
                apply hjoint
                apply le_antisymm
                · exact (iInf_le
                    (fun j => eigenspace (data.gram j) (chi j)) r).trans
                    (le_of_eq hr)
                · exact bot_le
            }
          have heq : data.jointSubspace alpha =
              iInf fun r => eigenspace (data.gram r) (chi r) := by
            rfl
          rw [← heq]
          exact le_iSup data.jointSubspace alpha

def Z180K30CommutingSymmetricFamilyV5.jointOrthogonalFamily
    (data : Z180K30CommutingSymmetricFamilyV5) :=
  (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces data.symmetric).comp
    data.jointIndexCoe_injective

def Z180K30CommutingSymmetricFamilyV5.jointInternal
    (data : Z180K30CommutingSymmetricFamilyV5) :
    DirectSum.IsInternal data.jointSubspace := by
  apply data.jointOrthogonalFamily.isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff]
  exact data.joint_iSup_eq_top

noncomputable def Z180K30CommutingSymmetricFamilyV5.jointBasis
    (data : Z180K30CommutingSymmetricFamilyV5) :
    OrthonormalBasis (Fin 6) Complex Z180K30JointSpaceV5 :=
  data.jointInternal.subordinateOrthonormalBasis (by simp)
    data.jointOrthogonalFamily

noncomputable def Z180K30CommutingSymmetricFamilyV5.jointIndex
    (data : Z180K30CommutingSymmetricFamilyV5) (k : Fin 6) :
    Z180K30JointEigenvalueIndexV5 data :=
  data.jointInternal.subordinateOrthonormalBasisIndex
    (by simp) k data.jointOrthogonalFamily

theorem Z180K30CommutingSymmetricFamilyV5.jointBasis_mem_eigenspace
    (data : Z180K30CommutingSymmetricFamilyV5) (k : Fin 6) (r : Fin 5) :
    data.jointBasis k ∈
      eigenspace (data.gram r) (data.jointIndex k r).val := by
  have h := data.jointInternal.subordinateOrthonormalBasis_subordinate
    (by simp) k data.jointOrthogonalFamily
  have hmem : data.jointBasis k ∈
      data.jointSubspace (data.jointIndex k) := by
    simpa [Z180K30CommutingSymmetricFamilyV5.jointBasis,
      Z180K30CommutingSymmetricFamilyV5.jointIndex] using h
  exact (Submodule.mem_iInf
    (p := fun j => eigenspace (data.gram j)
      (data.jointIndex k j).val)).mp hmem r

#print axioms Z180K30CommutingSymmetricFamilyV5.jointBasis_mem_eigenspace

end

end Fuglede
