import Mathlib.Tactic

/-! Six-bit block kernel for the cardinality-six `Phi_36` forcing lemma. -/

namespace Fuglede

theorem z36_phi36_block_classify
    (a0 a1 a2 a3 a4 a5 : Int)
    (h0l : 0 ≤ a0) (h0u : a0 ≤ 1)
    (h1l : 0 ≤ a1) (h1u : a1 ≤ 1)
    (h2l : 0 ≤ a2) (h2u : a2 ≤ 1)
    (h3l : 0 ≤ a3) (h3u : a3 ≤ 1)
    (h4l : 0 ≤ a4) (h4u : a4 ≤ 1)
    (h5l : 0 ≤ a5) (h5u : a5 ≤ 1)
    (he0 : a0 - a2 - a3 + a5 = 0)
    (he1 : a1 + a2 - a4 - a5 = 0) :
    (a0 = a3 ∧ a1 = a4 ∧ a2 = a5) ∨
      ((a0 = a2 ∧ a2 = a4 ∧ a1 = a3 ∧ a3 = a5) ∧
        a0 + a1 + a2 + a3 + a4 + a5 = 3) := by
  omega

theorem z36_phi36_block_mass_cases
    (a0 a1 a2 a3 a4 a5 : Int)
    (h0l : 0 ≤ a0) (h0u : a0 ≤ 1)
    (h1l : 0 ≤ a1) (h1u : a1 ≤ 1)
    (h2l : 0 ≤ a2) (h2u : a2 ≤ 1)
    (h3l : 0 ≤ a3) (h3u : a3 ≤ 1)
    (h4l : 0 ≤ a4) (h4u : a4 ≤ 1)
    (h5l : 0 ≤ a5) (h5u : a5 ≤ 1)
    (he0 : a0 - a2 - a3 + a5 = 0)
    (he1 : a1 + a2 - a4 - a5 = 0) :
    let c := a0 + a1 + a2 + a3 + a4 + a5
    c = 0 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 6 := by
  dsimp only
  rcases z36_phi36_block_classify a0 a1 a2 a3 a4 a5
      h0l h0u h1l h1u h2l h2u h3l h3u h4l h4u h5l h5u he0 he1 with
    hanti | hcycle
  · rcases hanti with ⟨h03, h14, h25⟩
    omega
  · exact Or.inr (Or.inr (Or.inl hcycle.2))

#print axioms z36_phi36_block_classify
#print axioms z36_phi36_block_mass_cases

end Fuglede
