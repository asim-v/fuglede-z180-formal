import Fuglede.Z180K30JointEigenvalueCoreV7

namespace Fuglede

open Module.End

noncomputable section

theorem z180_k30_joint_coordinate_pilot_v15
    (core : Z180K30PositiveCommutingGramFamilyV7)
    (r : Fin 5) (k : Fin 6) :
    (LinearMap.toMatrix core.family.jointBasis.toBasis
      core.family.jointBasis.toBasis
      (core.family.gram r)) k k =
      (core.eigenvalue k r : Complex) := by
  rw [LinearMap.toMatrix_apply]
  change
    (core.family.jointBasis.toBasis.repr
      ((core.family.gram r) (core.family.jointBasis k))) k =
        (core.eigenvalue k r : Complex)
  rw [core.gram_apply_jointBasis]
  rw [core.family.jointBasis.coe_toBasis_repr_apply]
  rw [core.family.jointBasis.repr_apply_apply]
  rw [inner_smul_right, core.family.jointBasis.inner_eq_one, mul_one]

#print axioms z180_k30_joint_coordinate_pilot_v15

end

end Fuglede
