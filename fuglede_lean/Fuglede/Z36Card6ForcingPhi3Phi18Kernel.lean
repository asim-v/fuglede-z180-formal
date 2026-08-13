import Mathlib.Tactic

/-! One six-coordinate fibre used in the `Phi_3` plus `Phi_18` branch. -/

namespace Fuglede

theorem z36_phi3_phi18_fibre_kernel
    (c0 c1 c2 c3 c4 c5 : Int)
    (h0l : 0 ≤ c0) (h0u : c0 ≤ 2)
    (h1l : 0 ≤ c1) (h1u : c1 ≤ 2)
    (h2l : 0 ≤ c2) (h2u : c2 ≤ 2)
    (h3l : 0 ≤ c3) (h3u : c3 ≤ 2)
    (h4l : 0 ≤ c4) (h4u : c4 ≤ 2)
    (h5l : 0 ≤ c5) (h5u : c5 ≤ 2)
    (hmass : c0 + c1 + c2 + c3 + c4 + c5 = 2)
    (he0 : c0 - c2 - c3 + c5 = 0)
    (he1 : c1 + c2 - c4 - c5 = 0) :
    c0 + c2 + c4 = 1 ∧ c1 + c3 + c5 = 1 := by
  omega

#print axioms z36_phi3_phi18_fibre_kernel

end Fuglede
