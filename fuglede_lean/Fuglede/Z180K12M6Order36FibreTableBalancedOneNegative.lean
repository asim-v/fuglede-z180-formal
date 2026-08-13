-- Generator SHA-256: 950682432c432f362d3d6da2b2a55eae5e2e46d66690481fba2a0b696adc323b
import Fuglede.Z180K12M6Order36FibreBase

namespace Fuglede

theorem z180_k12_order36_fibre_table_balancedOne_negative :
    ∀ f2 f3 f4 f5 : Z180K12Order36Fibre,
      Z180K12Order36TableProperty .balancedOne .negative f2 f3 f4 f5 := by
  letI : Decidable (∀ f2 f3 f4 f5 : Z180K12Order36Fibre,
      Z180K12Order36TableProperty .balancedOne .negative f2 f3 f4 f5) :=
    z180K12Order36DecidableForall fun f2 =>
      z180K12Order36DecidableForall fun f3 =>
        z180K12Order36DecidableForall fun f4 =>
          z180K12Order36DecidableForall fun f5 => by
            unfold Z180K12Order36TableProperty
            infer_instance
  decide

#print axioms z180_k12_order36_fibre_table_balancedOne_negative

end Fuglede
