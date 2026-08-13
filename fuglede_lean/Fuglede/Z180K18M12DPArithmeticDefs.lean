import Mathlib.Tactic

/-! Shared predicates for the sharded residual `m = 12` arithmetic DAG. -/

namespace Fuglede

/-- Common nonvanishing spelling for the four `Phi_12` coordinates. -/
def Z180K18M12FourRemaindersNonzero
    (r0 r1 r2 r3 : Int) : Prop :=
  ¬ (r0 = 0 ∧ r1 = 0 ∧ r2 = 0 ∧ r3 = 0)

/-- Aggregate constraints for one three-fibre block. -/
def Z180K18M12ThreeFiberBalance
    (X W parityWitness : Int) : Prop :=
  X + W ≤ 3 ∧ X - W ≤ 3 ∧
    -X + W ≤ 3 ∧ -X - W ≤ 3 ∧
    X + W = 1 + 2 * parityWitness

/-- One-fibre form underlying the aggregate constraint. -/
def Z180K18M12OneFiberBalance
    (x z parityWitness : Int) : Prop :=
  x + z ≤ 1 ∧ x - z ≤ 1 ∧
    -x + z ≤ 1 ∧ -x - z ≤ 1 ∧
    x + z = 1 + 2 * parityWitness

end Fuglede
