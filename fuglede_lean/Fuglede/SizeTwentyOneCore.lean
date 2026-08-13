import Fuglede.SizeTwelveCore
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum

/-!
# Finite arithmetic for the cardinality-twenty-one stratum

This file records only the elementary natural-number facts used by the
cardinality-`21` search in `ZMod 2310`.  It does not formalize the Fourier,
cyclotomic, or profile-classification parts of that argument.
-/

namespace Fuglede

/-- The final prime does not divide a set of cardinality `21`. -/
theorem eleven_not_dvd_twenty_one : ¬(11 : ℕ) ∣ 21 := by
  norm_num

/-- Cardinality `21` is arithmetically compatible with the ambient group. -/
theorem twenty_one_dvd_2310 : (21 : ℕ) ∣ 2310 := by
  norm_num

/-- An order-`21` character on `ZMod 210` has a kernel of size `10`. -/
theorem two_hundred_ten_div_twenty_one : (210 : ℕ) / 21 = 10 := by
  norm_num

/-- Re-export the quotient bound used in the `21`-point reduction: among
divisors of `210` divisible by `6`, a kernel of size at least `10` forces
character order `6`. -/
theorem order_eq_six_of_large_kernel
    (m : ℕ) (hm : m ∣ 210) (h6 : 6 ∣ m) (hkernel : 10 ≤ 210 / m) :
    m = 6 :=
  divisor_210_eq_six_of_six_dvd_of_ten_le_quotient m hm h6 hkernel

/-- Every natural divisor of `35` is odd. -/
theorem divisor_of_thirty_five_is_odd (d : ℕ) (hd : d ∣ 35) : Odd d := by
  exact (show Odd 35 from ⟨17, by norm_num⟩).of_dvd_nat hd

/-- In particular, a difference whose order divides `35` cannot have order
divisible by `6`.  The nonzero condition used in the combinatorial argument
is stronger than needed for this arithmetic conclusion. -/
theorem six_not_dvd_divisor_of_thirty_five (d : ℕ) (hd : d ∣ 35) :
    ¬6 ∣ d := by
  intro h6
  have h2 : 2 ∣ d := dvd_trans (by norm_num : (2 : ℕ) ∣ 6) h6
  exact (divisor_of_thirty_five_is_odd d hd).not_two_dvd_nat h2

/-- The version matching the search invariant, where the difference is known
to be nonzero. -/
theorem nonzero_divisor_of_thirty_five_not_multiple_of_six
    (d : ℕ) (_hd0 : d ≠ 0) (hd : d ∣ 35) : ¬6 ∣ d :=
  six_not_dvd_divisor_of_thirty_five d hd

end Fuglede
