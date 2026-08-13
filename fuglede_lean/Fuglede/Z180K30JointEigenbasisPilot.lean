import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Tactic

/-! A resource pilot for the simultaneous eigenbasis used by the K30 Gram bridge. -/

namespace Fuglede

noncomputable section

abbrev Z180K30JointSpace := EuclideanSpace Complex (Fin 6)

structure Z180K30CommutingSymmetricFamily where
  gram : Fin 5 -> Module.End Complex Z180K30JointSpace
  symmetric : forall r, LinearMap.IsSymmetric (gram r)
  pairwiseCommute :
    Pairwise (fun r s => Commute (gram r) (gram s))

def Z180K30CommutingSymmetricFamily.jointOrthogonalFamily
    (data : Z180K30CommutingSymmetricFamily) :=
  LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces data.symmetric

def Z180K30CommutingSymmetricFamily.jointInternal
    (data : Z180K30CommutingSymmetricFamily) :=
  LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute
    data.symmetric data.pairwiseCommute

noncomputable def Z180K30CommutingSymmetricFamily.jointBasis
    (data : Z180K30CommutingSymmetricFamily) :
    OrthonormalBasis (Fin 6) Complex Z180K30JointSpace :=
  data.jointInternal.subordinateOrthonormalBasis (by simp)
    data.jointOrthogonalFamily

noncomputable def Z180K30CommutingSymmetricFamily.jointIndex
    (data : Z180K30CommutingSymmetricFamily) (k : Fin 6) :
    Fin 5 -> Complex :=
  (data.jointInternal.subordinateOrthonormalBasisIndex
    (by simp) k data.jointOrthogonalFamily).val

theorem Z180K30CommutingSymmetricFamily.jointBasis_mem_eigenspace
    (data : Z180K30CommutingSymmetricFamily) (k : Fin 6) (r : Fin 5) :
    data.jointBasis k ∈
      LinearMap.eigenspace (data.gram r) (data.jointIndex k r) := by
  have h := data.jointInternal.subordinateOrthonormalBasis_subordinate
    (by simp) k data.jointOrthogonalFamily
  exact (Submodule.mem_iInf.mp h) r

#print axioms Z180K30CommutingSymmetricFamily.jointBasis_mem_eigenspace

end

end Fuglede
