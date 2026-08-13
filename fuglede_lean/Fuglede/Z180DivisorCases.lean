import Mathlib.Tactic

/-!
# Explicit divisor case split for 180

These tiny arithmetic lemmas keep the eventual top-level `ZMod 180` proof
honest: after cardinality divisibility has been established, the remaining
tiling proof must discharge exactly the listed divisor cases.
-/

namespace Fuglede

/-- The complete positive-divisor list for 180. -/
theorem dvd_180_cases {k : Nat} (hpos : 0 < k) (hdvd : k ∣ 180) :
    k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
    k = 9 ∨ k = 10 ∨ k = 12 ∨ k = 15 ∨ k = 18 ∨
    k = 20 ∨ k = 30 ∨ k = 36 ∨ k = 45 ∨ k = 60 ∨
    k = 90 ∨ k = 180 := by
  have hk : k ∈ (180).divisors := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivisors : (180).divisors =
      ({1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} :
        Finset Nat) := by
    decide
  rw [hdivisors] at hk
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hk

/-- In the lower half of `ZMod 180`, divisibility leaves exactly seventeen
positive cardinalities. -/
theorem dvd_180_cases_of_le_ninety {k : Nat}
    (hpos : 0 < k) (hle : k <= 90) (hdvd : k ∣ 180) :
    k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
    k = 9 ∨ k = 10 ∨ k = 12 ∨ k = 15 ∨ k = 18 ∨
    k = 20 ∨ k = 30 ∨ k = 36 ∨ k = 45 ∨ k = 60 ∨
    k = 90 := by
  rcases dvd_180_cases hpos hdvd with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals omega

#print axioms dvd_180_cases_of_le_ninety

end Fuglede
