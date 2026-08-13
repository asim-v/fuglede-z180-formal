import Mathlib.Tactic

/-!
# Explicit five-term integral obstructions for the non-H Gram orbits
-/

namespace Fuglede

theorem z180_k30_five_pm_six_explicit
    (a0 a1 a2 a3 a4 : Int)
    (h0 : a0 = 6 \/ a0 = -6) (h1 : a1 = 6 \/ a1 = -6)
    (h2 : a2 = 6 \/ a2 = -6) (h3 : a3 = 6 \/ a3 = -6)
    (h4 : a4 = 6 \/ a4 = -6) :
    a0 + a1 + a2 + a3 + a4 ≠ 0 := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;> omega

set_option maxHeartbeats 0 in
theorem z180_k30_five_gram_pair_types_explicit
    (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 : Int)
    (h0 : (a0 = 6 /\ b0 = 0) \/ (a0 = -6 /\ b0 = 6) \/
      (a0 = 0 /\ b0 = -6))
    (h1 : (a1 = 6 /\ b1 = 0) \/ (a1 = -6 /\ b1 = 6) \/
      (a1 = 0 /\ b1 = -6))
    (h2 : (a2 = 6 /\ b2 = 0) \/ (a2 = -6 /\ b2 = 6) \/
      (a2 = 0 /\ b2 = -6))
    (h3 : (a3 = 6 /\ b3 = 0) \/ (a3 = -6 /\ b3 = 6) \/
      (a3 = 0 /\ b3 = -6))
    (h4 : (a4 = 6 /\ b4 = 0) \/ (a4 = -6 /\ b4 = 6) \/
      (a4 = 0 /\ b4 = -6)) :
    a0 + a1 + a2 + a3 + a4 ≠ 0 \/
      b0 + b1 + b2 + b3 + b4 ≠ 0 := by
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
    rcases h4 with h4 | h4 | h4 <;> omega

#print axioms z180_k30_five_pm_six_explicit
#print axioms z180_k30_five_gram_pair_types_explicit

end Fuglede
