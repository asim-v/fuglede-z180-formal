import Fuglede.Z36Card6ForcingPhi3Phi36EvenKernel
import Fuglede.Z36Card6ForcingPhi3Phi36OddKernel
import Mathlib.Tactic

/-! One twelve-bit residue fibre used in the `Phi_3` plus `Phi_36` branch. -/

namespace Fuglede

theorem z36_phi3_phi36_fibre_kernel
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Int)
    (h0l : 0 ≤ a0) (h0u : a0 ≤ 1)
    (h1l : 0 ≤ a1) (h1u : a1 ≤ 1)
    (h2l : 0 ≤ a2) (h2u : a2 ≤ 1)
    (h3l : 0 ≤ a3) (h3u : a3 ≤ 1)
    (h4l : 0 ≤ a4) (h4u : a4 ≤ 1)
    (h5l : 0 ≤ a5) (h5u : a5 ≤ 1)
    (h6l : 0 ≤ a6) (h6u : a6 ≤ 1)
    (h7l : 0 ≤ a7) (h7u : a7 ≤ 1)
    (h8l : 0 ≤ a8) (h8u : a8 ≤ 1)
    (h9l : 0 ≤ a9) (h9u : a9 ≤ 1)
    (h10l : 0 ≤ a10) (h10u : a10 ≤ 1)
    (h11l : 0 ≤ a11) (h11u : a11 ≤ 1)
    (hmass : a0 + a1 + a2 + a3 + a4 + a5 +
      a6 + a7 + a8 + a9 + a10 + a11 = 2)
    (he0 : a0 - a4 - a6 + a10 = 0)
    (he1 : a1 - a5 - a7 + a11 = 0)
    (he2 : a2 + a4 - a8 - a10 = 0)
    (he3 : a3 + a5 - a9 - a11 = 0) :
    a0 = a6 ∧ a1 = a7 ∧ a2 = a8 ∧
      a3 = a9 ∧ a4 = a10 ∧ a5 = a11 := by
  have heven := z36_phi3_phi36_even_kernel
    a0 a2 a4 a6 a8 a10 (a1 + a3 + a5 + a7 + a9 + a11)
    h0l h0u h2l h2u h4l h4u h6l h6u h8l h8u h10l h10u
    (by linarith only [h1l, h3l, h5l, h7l, h9l, h11l])
    (by linarith only [hmass]) he0 he2
  have hodd := z36_phi3_phi36_odd_kernel
    a1 a3 a5 a7 a9 a11 (a0 + a2 + a4 + a6 + a8 + a10)
    h1l h1u h3l h3u h5l h5u h7l h7u h9l h9u h11l h11u
    (by linarith only [h0l, h2l, h4l, h6l, h8l, h10l])
    (by linarith only [hmass]) he1 he3
  exact ⟨heven.1, hodd.1, heven.2.1, hodd.2.1, heven.2.2, hodd.2.2⟩

#print axioms z36_phi3_phi36_fibre_kernel

end Fuglede
