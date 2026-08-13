import Mathlib.Tactic

/-!
# Presburger kernel for the cardinality-eighteen `m = 12` branch

The semantic reduction still has to show that the five level-profile counts
below are odd and sum to six.  Once those facts are available, the terminal
arithmetic contradiction is this ten-variable Presburger lemma.  This module
does not assert or assume the missing semantic bridge.
-/

namespace Fuglede

/-- Five odd integers cannot sum to six.  In the `m = 12` application, each
`sᵢ` is the sum of two residue-profile coordinates in one nonempty level. -/
theorem z180_k18_m12_five_odd_sum_six_impossible
    (s0 s1 s2 s3 s4 k0 k1 k2 k3 k4 : Int)
    (hsum : s0 + s1 + s2 + s3 + s4 = 6)
    (h0 : s0 = 2 * k0 + 1)
    (h1 : s1 = 2 * k1 + 1)
    (h2 : s2 = 2 * k2 + 1)
    (h3 : s3 = 2 * k3 + 1)
    (h4 : s4 = 2 * k4 + 1) :
    False := by
  omega

#print axioms z180_k18_m12_five_odd_sum_six_impossible

end Fuglede
