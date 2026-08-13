import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Tactic

/-! A finite-index resource pilot for the K30 simultaneous eigenbasis. -/

namespace Fuglede

open Module.End

noncomputable section

abbrev Z180K30JointSpaceV2 := EuclideanSpace Complex (Fin 6)

structure Z180K30CommutingSymmetricFamilyV2 where
  gram : Fin 5 -> Module.End Complex Z180K30JointSpaceV2
  symmetric : forall r, LinearMap.IsSymmetric (gram r)
  pairwiseCommute :
    Pairwise (fun r s => Commute (gram r) (gram s))

abbrev Z180K30JointEigenvalueIndexV2
    (data : Z180K30CommutingSymmetricFamilyV2) :=
  (r : Fin 5) -> Eigenvalues (data.gram r)

def Z180K30CommutingSymmetricFamilyV2.jointSubspace
    (data : Z180K30CommutingSymmetricFamilyV2)
    (alpha : Z180K30JointEigenvalueIndexV2 data) :
    Submodule Complex Z180K30JointSpaceV2 :=
  iInf fun r => eigenspace (data.gram r) (alpha r : Complex)

theorem Z180K30CommutingSymmetricFamilyV2.joint_iSup_eq_top
    (data : Z180K30CommutingSymmetricFamilyV2) :
    iSup data.jointSubspace = (⊤ : Submodule Complex Z180K30JointSpaceV2) := by
  have hfull :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
      data.symmetric data.pairwiseCommute
  rw [show (⊤ : Submodule Complex Z180K30JointSpaceV2) =
      iSup (fun chi : Fin 5 -> Complex =>
        iInf fun r => eigenspace (data.gram r) (chi r)) by
        exact hfull.symm]
  apply iSup_le
  intro chi
  by_cases hjoint :
      (iInf fun r => eigenspace (data.gram r) (chi r)) = ⊥
  + rw [hjoint]
    exact bot_le
  + let alpha : Z180K30JointEigenvalueIndexV2 data := fun r =>
      {
        val := chi r
        property := by
          intro hr
          apply hjoint
          apply le_antisymm
          + exact (iInf_le
              (fun j => eigenspace (data.gram j) (chi j)) r).trans
              (le_of_eq hr)
          + exact bot_le
      }
    simpa only [Z180K30CommutingSymmetricFamilyV2.jointSubspace, alpha] using
      (le_iSup (fun a => data.jointSubspace a) alpha)

def Z180K30CommutingSymmetricFamilyV2.jointOrthogonalFamily
    (data : Z180K30CommutingSymmetricFamilyV2) :=
  (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces data.symmetric).comp
    (by
      intro alpha beta hab
      funext r
      exact Subtype.ext (congrFun hab r))

def Z180K30CommutingSymmetricFamilyV2.jointInternal
    (data : Z180K30CommutingSymmetricFamilyV2) :
    DirectSum.IsInternal data.jointSubspace := by
  apply data.jointOrthogonalFamily.isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff, data.joint_iSup_eq_top]

noncomputable def Z180K30CommutingSymmetricFamilyV2.jointBasis
    (data : Z180K30CommutingSymmetricFamilyV2) :
    OrthonormalBasis (Fin 6) Complex Z180K30JointSpaceV2 :=
  data.jointInternal.subordinateOrthonormalBasis (by simp)
    data.jointOrthogonalFamily

noncomputable def Z180K30CommutingSymmetricFamilyV2.jointIndex
    (data : Z180K30CommutingSymmetricFamilyV2) (k : Fin 6) :
    Z180K30JointEigenvalueIndexV2 data :=
  (data.jointInternal.subordinateOrthonormalBasisIndex
    (by simp) k data.jointOrthogonalFamily).val

theorem Z180K30CommutingSymmetricFamilyV2.jointBasis_mem_eigenspace
    (data : Z180K30CommutingSymmetricFamilyV2) (k : Fin 6) (r : Fin 5) :
    data.jointBasis k ∈
      eigenspace (data.gram r) (data.jointIndex k r : Complex) := by
  have h := data.jointInternal.subordinateOrthonormalBasis_subordinate
    (by simp) k data.jointOrthogonalFamily
  exact (Submodule.mem_iInf
    (p := fun j => eigenspace (data.gram j)
      (data.jointIndex k j : Complex))).mp h r

#print axioms Z180K30CommutingSymmetricFamilyV2.jointBasis_mem_eigenspace

end

end Fuglede
