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
  rcases h0 with rfl | rfl <;>
    rcases h1 with rfl | rfl <;>
    rcases h2 with rfl | rfl <;>
    rcases h3 with rfl | rfl <;>
    rcases h4 with rfl | rfl <;>
    rcases h5 with rfl | rfl <;>
    by_cases hbc : b = c <;> simp [hbc]

end Fuglede
