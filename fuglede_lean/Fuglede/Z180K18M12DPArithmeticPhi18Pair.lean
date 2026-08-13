import Fuglede.Z180K18M12DPArithmeticDefs

/-!
# Pair leaf for the residual `(12,18)` arithmetic family

Fixing two three-fibre balances reduces the original six-balance Presburger
problem to one bounded difference.  This leaf is reused four times by the
`Phi_18` aggregator.
-/

namespace Fuglede

set_option maxHeartbeats 0

/-- Two balanced coordinates whose auxiliary coordinates are three times
integers in `[-1,1]` cannot differ by a nonzero multiple of five. -/
theorem z180_k18_m12_balanced_pair_diff_zero_of_five_mul
    (X Y W V eX eY z t k : Int)
    (hX : Z180K18M12ThreeFiberBalance X W eX)
    (hY : Z180K18M12ThreeFiberBalance Y V eY)
    (hzlo : -1 ≤ z) (hzhi : z ≤ 1)
    (htlo : -1 ≤ t) (hthi : t ≤ 1)
    (hW : W = 3 * z) (hV : V = 3 * t)
    (hfive : X - Y = 5 * k) :
    X - Y = 0 := by
  dsimp only [Z180K18M12ThreeFiberBalance] at hX hY
  omega

#print axioms z180_k18_m12_balanced_pair_diff_zero_of_five_mul

end Fuglede
