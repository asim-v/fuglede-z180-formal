import Mathlib.Tactic

/-! Four-variable mass/parity core for the last cardinality-six branch. -/

namespace Fuglede

theorem z36_phi6_phi9_phi18_signed_kernel
    (t0 t1 t2 s : Int)
    (h0 : 0 ≤ t0) (h1 : 0 ≤ t1) (h2 : 0 ≤ t2)
    (hmass : 3 * (t0 + t1 + t2) = 6)
    (h0l : -t0 ≤ s) (h0u : s ≤ t0)
    (h1l : -t1 ≤ s) (h1u : s ≤ t1)
    (h2l : -t2 ≤ s) (h2u : s ≤ t2) :
    s = 0 := by
  omega

#print axioms z36_phi6_phi9_phi18_signed_kernel

end Fuglede
