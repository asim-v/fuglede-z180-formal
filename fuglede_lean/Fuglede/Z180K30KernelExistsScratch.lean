import Fuglede.Z180K30SixLevelFourierV4

namespace Fuglede

theorem z180K30_kernel30Lift_of_projection30_eq_zero_scratch :
    ∀ d : ZMod 180, z180K30Projection30 d = 0 →
      ∃ b : ZMod 6, d = z180K30Kernel30Lift b := by
  intro d
  fin_cases d <;>
    letI := Fintype.decidableExistsFintype
    decide

end Fuglede
