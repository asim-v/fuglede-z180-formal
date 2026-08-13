import Mathlib.Tactic

/-! Seven-variable odd-parity core for the `Phi_3` plus `Phi_36` branch. -/

namespace Fuglede

theorem z36_phi3_phi36_odd_kernel
    (a1 a3 a5 a7 a9 a11 slack : Int)
    (h1l : 0 ≤ a1) (h1u : a1 ≤ 1)
    (h3l : 0 ≤ a3) (h3u : a3 ≤ 1)
    (h5l : 0 ≤ a5) (h5u : a5 ≤ 1)
    (h7l : 0 ≤ a7) (h7u : a7 ≤ 1)
    (h9l : 0 ≤ a9) (h9u : a9 ≤ 1)
    (h11l : 0 ≤ a11) (h11u : a11 ≤ 1)
    (hslack : 0 ≤ slack)
    (hmass : a1 + a3 + a5 + a7 + a9 + a11 + slack = 2)
    (he1 : a1 - a5 - a7 + a11 = 0)
    (he3 : a3 + a5 - a9 - a11 = 0) :
    a1 = a7 ∧ a3 = a9 ∧ a5 = a11 := by
  omega

#print axioms z36_phi3_phi36_odd_kernel

end Fuglede
