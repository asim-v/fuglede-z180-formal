import Mathlib.Tactic

/-! Tiny Presburger kernels for the cardinality-six `Phi_36` forcing lemma. -/

namespace Fuglede

/-- A 0/1 six-point residue block satisfying the two `Phi_36` remainder
equations is either antipodal or one of the two pure three-cycles. -/
theorem z36_phi36_six_bit_block_classify
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

/-- The possible masses of one such block are exactly `0,2,3,4,6`. -/
theorem z36_phi36_six_bit_block_mass_cases
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
  rcases z36_phi36_six_bit_block_classify a0 a1 a2 a3 a4 a5
      h0l h0u h1l h1u h2l h2u h3l h3u h4l h4u h5l h5u he0 he1 with
    hanti | hcycle
  · rcases hanti with ⟨h03, h14, h25⟩
    omega
  · exact Or.inr (Or.inr (Or.inl hcycle.2))

/-- Six allowed block masses summing to six either contain no three-block,
or consist only of zero-blocks and exactly two three-blocks. -/
theorem z36_phi36_six_block_mass_dichotomy
    (c0 c1 c2 c3 c4 c5 : Int)
    (h0 : c0 = 0 ∨ c0 = 2 ∨ c0 = 3 ∨ c0 = 4 ∨ c0 = 6)
    (h1 : c1 = 0 ∨ c1 = 2 ∨ c1 = 3 ∨ c1 = 4 ∨ c1 = 6)
    (h2 : c2 = 0 ∨ c2 = 2 ∨ c2 = 3 ∨ c2 = 4 ∨ c2 = 6)
    (h3 : c3 = 0 ∨ c3 = 2 ∨ c3 = 3 ∨ c3 = 4 ∨ c3 = 6)
    (h4 : c4 = 0 ∨ c4 = 2 ∨ c4 = 3 ∨ c4 = 4 ∨ c4 = 6)
    (h5 : c5 = 0 ∨ c5 = 2 ∨ c5 = 3 ∨ c5 = 4 ∨ c5 = 6)
    (hsum : c0 + c1 + c2 + c3 + c4 + c5 = 6) :
    (c0 ≠ 3 ∧ c1 ≠ 3 ∧ c2 ≠ 3 ∧ c3 ≠ 3 ∧ c4 ≠ 3 ∧ c5 ≠ 3) ∨
      ((c0 = 0 ∨ c0 = 3) ∧ (c1 = 0 ∨ c1 = 3) ∧
        (c2 = 0 ∨ c2 = 3) ∧ (c3 = 0 ∨ c3 = 3) ∧
        (c4 = 0 ∨ c4 = 3) ∧ (c5 = 0 ∨ c5 = 3)) := by
  by_cases hc0 : c0 = 3
  · right
    omega
  by_cases hc1 : c1 = 3
  · right
    omega
  by_cases hc2 : c2 = 3
  · right
    omega
  by_cases hc3 : c3 = 3
  · right
    omega
  by_cases hc4 : c4 = 3
  · right
    omega
  by_cases hc5 : c5 = 3
  · right
    omega
  · exact Or.inl ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩

#print axioms z36_phi36_six_bit_block_classify
#print axioms z36_phi36_six_bit_block_mass_cases
#print axioms z36_phi36_six_block_mass_dichotomy

end Fuglede
