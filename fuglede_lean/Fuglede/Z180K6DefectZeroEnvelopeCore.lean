import Fuglede.Z180K6DefectLowOrderSieve
import Fuglede.Z180K6NonzeroFifthZero
import Mathlib.Tactic

/-!
# Assembling the cardinality-six defect zero envelope

This module contains no finite search.  It assembles the already checked
low-order sieve, the CRT fifth-coordinate dichotomy, and three explicit
high-order exclusions into the terminal `{4, 30}` zero envelope.

The exclusions at orders `12`, `18`, and `36` are parameters here.  Keeping
this purely logical assembler separate makes the exact boundary of the
three remaining arithmetic certificates visible in the theorem type.
-/

namespace Fuglede

open Polynomial

/-- The complete positive divisor list of `36`, in the form used by the CRT
zero-order assembly below. -/
private theorem eq_one_two_three_four_six_nine_twelve_eighteen_thirtySix_of_dvd
    (m : Nat) (hmpos : 0 < m) (hm36 : m ∣ 36) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 9 ∨
      m = 12 ∨ m = 18 ∨ m = 36 := by
  have hmle : m ≤ 36 := Nat.le_of_dvd (by norm_num) hm36
  interval_cases m <;> norm_num at hm36 <;> simp

/-- In a cardinality-six spectral pair, a `Phi_30`/not-`Phi_6` defect and
the three high-order exclusions force every nonzero Fourier-zero order into
the exact terminal set `{4, 30}`.

The nonzero fifth CRT coordinate is the order-`30` branch.  A zero fifth
coordinate makes the order divide `36`; the explicit divisor list and the
six supplied cyclotomic exclusions then leave only order `4`.
-/
theorem z180_k6_zeroEnvelope_of_phi30_defect_of_high_sieve
    {X L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 X L) (hcard : X.card = 6)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 X)
    (h6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 X)
    (h12 : ¬ cyclotomic 12 Int ∣ maskPolynomial 180 X)
    (h18 : ¬ cyclotomic 18 Int ∣ maskPolynomial 180 X)
    (h36 : ¬ cyclotomic 36 Int ∣ maskPolynomial 180 X) :
    Z180K6ZeroEnvelope X := by
  obtain ⟨h2, h3, h9⟩ :=
    z180_k6_defect_low_order_sieve X hcard h30 h6
  intro d hd hzero
  refine ⟨hd, ?_⟩
  by_cases hd5 : crt180FifthCoord (toCRT180 d) ≠ 0
  · exact Or.inr
      (z180_k6_frequencyOrder_eq_thirty_of_phi30_defect
        hSpec hcard h30 h6 hzero hd5)
  · have hd5zero : crt180FifthCoord (toCRT180 d) = 0 :=
      not_ne_iff.mp hd5
    have hord36 : frequencyOrder 180 d ∣ 36 := by
      simpa using
        frequencyOrder_fromCRT180_dvd_thirtySix_of_fifthCoord_eq_zero
          (toCRT180 d) hd5zero
    have hordpos : 0 < frequencyOrder 180 d := by
      rw [frequencyOrder_eq_addOrderOf (by norm_num)]
      exact addOrderOf_pos d
    have hcases :=
      eq_one_two_three_four_six_nine_twelve_eighteen_thirtySix_of_dvd
        (frequencyOrder 180 d) hordpos hord36
    rcases hcases with
      h1 | h2order | h3order | h4order | h6order | h9order |
        h12order | h18order | h36order
    · exact False.elim (hd ((frequencyOrder_eq_one_iff (by norm_num) d).mp h1))
    · exact False.elim (h2 (by simpa [CyclotomicZero, h2order] using hzero))
    · exact False.elim (h3 (by simpa [CyclotomicZero, h3order] using hzero))
    · exact Or.inl h4order
    · exact False.elim (h6 (by simpa [CyclotomicZero, h6order] using hzero))
    · exact False.elim (h9 (by simpa [CyclotomicZero, h9order] using hzero))
    · exact False.elim (h12 (by simpa [CyclotomicZero, h12order] using hzero))
    · exact False.elim (h18 (by simpa [CyclotomicZero, h18order] using hzero))
    · exact False.elim (h36 (by simpa [CyclotomicZero, h36order] using hzero))

/-- The terminal graph turns the assembled envelope into a contradiction.
This is the exact logical endpoint consumed by a future descent theorem. -/
theorem z180_k6_phi30_defect_impossible_of_spectral_of_high_sieve
    {X L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 X L) (hcard : X.card = 6)
    (h30 : cyclotomic 30 Int ∣ maskPolynomial 180 X)
    (h6 : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 X)
    (h12 : ¬ cyclotomic 12 Int ∣ maskPolynomial 180 X)
    (h18 : ¬ cyclotomic 18 Int ∣ maskPolynomial 180 X)
    (h36 : ¬ cyclotomic 36 Int ∣ maskPolynomial 180 X) : False := by
  exact z180_k6_zeroEnvelope_impossible_of_spectral hSpec hcard
    (z180_k6_zeroEnvelope_of_phi30_defect_of_high_sieve
      hSpec hcard h30 h6 h12 h18 h36)

#print axioms z180_k6_zeroEnvelope_of_phi30_defect_of_high_sieve
#print axioms z180_k6_phi30_defect_impossible_of_spectral_of_high_sieve

end Fuglede
