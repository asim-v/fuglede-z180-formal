import Mathlib.Tactic

namespace Fuglede

private theorem six_eraseDups_length_le_two
    (a0 a1 a2 a3 a4 a5 b c : Nat)
    (h0 : a0 = b ∨ a0 = c)
    (h1 : a1 = b ∨ a1 = c)
    (h2 : a2 = b ∨ a2 = c)
    (h3 : a3 = b ∨ a3 = c)
    (h4 : a4 = b ∨ a4 = c)
    (h5 : a5 = b ∨ a5 = c) :
    [a0, a1, a2, a3, a4, a5].eraseDups.length ≤ 2 := by
  rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;>
    rcases h5 with h5 | h5 <;>
    by_cases hbc : b = c <;>
    simp [h0, h1, h2, h3, h4, h5, hbc]

end Fuglede
