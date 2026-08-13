import Fuglede.Z180K12M6Order20Omega
import Fuglede.Z180K12Projection36Phi6
import Fuglede.Z180K12Projection36Remainders3_12
import Mathlib.Tactic

/-!
# Grouping the projected order-six remainders

The two explicit `Phi_6` forms commute with grouping the 36 projected
coordinates into twelve residue classes.
-/

namespace Fuglede

set_option maxHeartbeats 0

theorem projection36_phi6_count12_remainders_order20
    (b : Fin 36 → Int) :
    z180K12Order20Phi6R0 (projection36Count12 b) =
        projection36Phi6R0 b ∧
    z180K12Order20Phi6R1 (projection36Count12 b) =
        projection36Phi6R1 b := by
  dsimp only [z180K12Order20Phi6R0, z180K12Order20Phi6R1,
    projection36Count12, projection36Phi6R0, projection36Phi6R1]
  norm_num
  change
    (b 0 + b 12 + b 24) - (b 2 + b 14 + b 26) -
        (b 3 + b 15 + b 27) + (b 5 + b 17 + b 29) +
        (b 6 + b 18 + b 30) - (b 8 + b 20 + b 32) -
        (b 9 + b 21 + b 33) + (b 11 + b 23 + b 35) =
      b 0 - b 2 - b 3 + b 5 + b 6 - b 8 - b 9 + b 11 +
        b 12 - b 14 - b 15 + b 17 + b 18 - b 20 - b 21 + b 23 +
        b 24 - b 26 - b 27 + b 29 + b 30 - b 32 - b 33 + b 35 ∧
    (b 1 + b 13 + b 25) + (b 2 + b 14 + b 26) -
        (b 4 + b 16 + b 28) - (b 5 + b 17 + b 29) +
        (b 7 + b 19 + b 31) + (b 8 + b 20 + b 32) -
        (b 10 + b 22 + b 34) - (b 11 + b 23 + b 35) =
      b 1 + b 2 - b 4 - b 5 + b 7 + b 8 - b 10 - b 11 +
        b 13 + b 14 - b 16 - b 17 + b 19 + b 20 - b 22 - b 23 +
        b 25 + b 26 - b 28 - b 29 + b 31 + b 32 - b 34 - b 35
  constructor <;> ring

#print axioms projection36_phi6_count12_remainders_order20

end Fuglede
