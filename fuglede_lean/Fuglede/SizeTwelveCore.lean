import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Finite arithmetic for the cardinality-twelve case

This file isolates the elementary arithmetic and pigeonhole facts used in the
cardinality-twelve branch of the search in `ZMod 2310`.  It deliberately makes
no assumption about Fourier analysis or cyclotomic divisibility.
-/

namespace Fuglede

/-- Among divisors of `210` that are multiples of `6`, only `6` can have a
quotient `210 / m` of at least `10`. -/
theorem divisor_210_eq_six_of_six_dvd_of_ten_le_quotient
    (m : ℕ) (hm : m ∣ 210) (h6 : 6 ∣ m) (hquot : 10 ≤ 210 / m) :
    m = 6 := by
  obtain ⟨k, rfl⟩ := h6
  have hk_le : k ≤ 35 := by
    have hle : 6 * k ≤ 210 := Nat.le_of_dvd (by norm_num) hm
    have hle' : 6 * k ≤ 6 * 35 := by simpa using hle
    exact Nat.le_of_mul_le_mul_left hle' (by norm_num)
  interval_cases k <;> norm_num at *

/-- Ten distinct points in a `5 × 7` grid contain two points in the same
row and two points in the same column.  Injectivity then ensures that the
other coordinate differs in each pair. -/
theorem ten_points_in_five_by_seven_have_both_collisions
    (f : Fin 10 → Fin 5 × Fin 7) (hf : Function.Injective f) :
    (∃ i j, i ≠ j ∧ (f i).1 = (f j).1 ∧ (f i).2 ≠ (f j).2) ∧
      ∃ i j, i ≠ j ∧ (f i).2 = (f j).2 ∧ (f i).1 ≠ (f j).1 := by
  obtain ⟨i, j, hij, hfirst⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k ↦ (f k).1) (by norm_num)
  obtain ⟨i', j', hij', hsecond⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k ↦ (f k).2) (by norm_num)
  constructor
  · refine ⟨i, j, hij, hfirst, ?_⟩
    intro heq
    exact hij (hf (Prod.ext hfirst heq))
  · refine ⟨i', j', hij', hsecond, ?_⟩
    intro heq
    exact hij' (hf (Prod.ext heq hsecond))

/-- The `5 × 7` grid has more points than a cardinality-twelve set. -/
theorem twelve_lt_thirty_five : 12 < 35 := by
  norm_num

/-- The final prime level, of size `11`, cannot evenly split twelve points. -/
theorem eleven_not_dvd_twelve : ¬11 ∣ 12 := by
  norm_num

/-- A nonzero difference inside the kernel of an order-six character has
order dividing `35`, and therefore can never have order `6`. This is the
shorter final obstruction in the cardinality-twelve proof. -/
theorem divisor_of_thirty_five_ne_six (d : ℕ) (hd : d ∣ 35) : d ≠ 6 := by
  intro h
  subst d
  norm_num at hd

end Fuglede
