import Mathlib.Tactic

/-! Seven-variable even-parity core for the `Phi_3` plus `Phi_36` branch. -/

namespace Fuglede

theorem z36_phi3_phi36_even_kernel
    (a0 a2 a4 a6 a8 a10 slack : Int)
    (h0l : 0 ≤ a0) (h0u : a0 ≤ 1)
    (h2l : 0 ≤ a2) (h2u : a2 ≤ 1)
    (h4l : 0 ≤ a4) (h4u : a4 ≤ 1)
    (h6l : 0 ≤ a6) (h6u : a6 ≤ 1)
    (h8l : 0 ≤ a8) (h8u : a8 ≤ 1)
    (h10l : 0 ≤ a10) (h10u : a10 ≤ 1)
    (hslack : 0 ≤ slack)
    (hmass : a0 + a2 + a4 + a6 + a8 + a10 + slack = 2)
    (he0 : a0 - a4 - a6 + a10 = 0)
    (he2 : a2 + a4 - a8 - a10 = 0) :
    a0 = a6 ∧ a2 = a8 ∧ a4 = a10 := by
  omega

#print axioms z36_phi3_phi36_even_kernel

end Fuglede
