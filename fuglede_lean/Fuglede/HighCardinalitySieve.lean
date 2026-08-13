import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Arithmetic sieve for high cardinalities

This module checks the finite natural-number sieve used in the high-cardinality
part of the `ZMod 2310` argument.  It does not formalize why Fourier or
cyclotomic hypotheses imply the divisibility assumptions below.
-/

namespace Fuglede

/-- Above `210`, the successive divisibility conditions at `330`, `462`, and
`770` leave exactly fifteen possible cardinalities up to `1155`. -/
theorem high_cardinality_arithmetic_sieve
    (k : ℕ)
    (hlo : 210 < k)
    (hhi : k ≤ 1155)
    (h11 : 11 ∣ k)
    (h7 : 330 < k → 7 ∣ k)
    (h5 : 462 < k → 5 ∣ k)
    (h3 : 770 < k → 3 ∣ k) :
    k = 220 ∨ k = 231 ∨ k = 242 ∨ k = 253 ∨ k = 264 ∨
    k = 275 ∨ k = 286 ∨ k = 297 ∨ k = 308 ∨ k = 319 ∨
    k = 330 ∨ k = 385 ∨ k = 462 ∨ k = 770 ∨ k = 1155 := by
  obtain ⟨n, rfl⟩ := h11
  have hnlo : 19 < n := by omega
  have hnhi : n ≤ 105 := by omega
  interval_cases n <;> norm_num at *

end Fuglede
