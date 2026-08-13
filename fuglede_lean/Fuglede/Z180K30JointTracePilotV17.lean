import Fuglede.Z180K30JointCoordinatePilotV15

namespace Fuglede

open Module.End
open scoped BigOperators

noncomputable section

theorem z180_k30_joint_trace_pilot_v17
    (core : Z180K30PositiveCommutingGramFamilyV7)
    (r : Fin 5)
    (htrace : LinearMap.trace Complex Z180K30JointSpaceV5
      (core.family.gram r) = 36) :
    (Finset.univ.sum fun k : Fin 6 => core.eigenvalue k r) = 36 := by
  have ht := htrace
  rw [LinearMap.trace_eq_matrix_trace Complex
    core.family.jointBasis.toBasis] at ht
  have hcomplex :
      (∑ k : Fin 6, (core.eigenvalue k r : Complex)) = 36 := by
    calc
      (∑ k : Fin 6, (core.eigenvalue k r : Complex)) =
          (LinearMap.toMatrix core.family.jointBasis.toBasis
            core.family.jointBasis.toBasis
            (core.family.gram r)).trace := by
        rw [Matrix.trace]
        apply Finset.sum_congr rfl
        intro k _hk
        exact (z180_k30_joint_coordinate_pilot_v15 core r k).symm
      _ = 36 := ht
  exact_mod_cast hcomplex

#print axioms z180_k30_joint_trace_pilot_v17

end
end Fuglede
