import Fuglede.Z180K18DescentDefect
import Fuglede.Z180K18ForcedPhi3Phi9
import Mathlib.Tactic

/-!
# The table-free core of the cardinality-eighteen terminal reduction

The exact terminal audit starts from two already formalized inputs: every
cardinality-eighteen spectral pair has `Phi_3` and `Phi_9` on both masks, and
a hypothetical non-tiler has a five-factor projection defect.  Before any
finite envelope or clique certificate is needed, the missing low factor in
the defect rules out base orders three and nine.

This file records precisely that table-free reduction.  It deliberately does
not claim the remaining six branches are closed.
-/

namespace Fuglede

open Polynomial

/-- The four core cyclotomic zeros forced on a cardinality-eighteen spectral
pair, in the canonical-frequency form used by the arithmetic certificate. -/
def Z180K18CorePhi3Phi9Zeros
    (A L : Finset (ZMod 180)) : Prop :=
  CyclotomicZero 180 A 60 ∧
    CyclotomicZero 180 A 20 ∧
    CyclotomicZero 180 L 60 ∧
    CyclotomicZero 180 L 20

/-- A five-factor defect with an explicitly named projected base order. -/
def Z180K18FiveFactorDefectAt
    (m : Nat) (A L : Finset (ZMod 180)) : Prop :=
  ∃ l₁ ∈ L, ∃ l₂ ∈ L, l₁ ≠ l₂ ∧
    frequencyOrder 36
      (z180K18Projection36 l₁ - z180K18Projection36 l₂) = m ∧
      frequencyOrder 180 (l₁ - l₂) = 5 * m ∧
      cyclotomic (5 * m) Int ∣ maskPolynomial 180 A ∧
      ¬ cyclotomic m Int ∣ maskPolynomial 180 A

/-- A five-factor defect whose base order has passed the table-free
`Phi_3`/`Phi_9` sieve.  The disjunction makes the six still-missing terminal
branch certificates visible in the type. -/
def Z180K18ReducedFiveFactorDefect
    (A L : Finset (ZMod 180)) : Prop :=
  Z180K18FiveFactorDefectAt 2 A L ∨
    Z180K18FiveFactorDefectAt 4 A L ∨
    Z180K18FiveFactorDefectAt 6 A L ∨
    Z180K18FiveFactorDefectAt 12 A L ∨
    Z180K18FiveFactorDefectAt 18 A L ∨
    Z180K18FiveFactorDefectAt 36 A L

private theorem z180_k18_base_divisor_cases
    (m : Nat) (hmpos : 0 < m) (hm36 : m ∣ 36) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 9 ∨
      m = 12 ∨ m = 18 ∨ m = 36 := by
  have hmle : m ≤ 36 := Nat.le_of_dvd (by norm_num) hm36
  interval_cases m <;> norm_num at hm36 <;> simp

/-- The forced core zeros are available independently of the descent
argument. -/
theorem z180_k18_corePhi3Phi9Zeros_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18) :
    Z180K18CorePhi3Phi9Zeros A L :=
  z180_k18_forced_phi3_phi9_both_sides hSpec hcard

/-- The exact table-free connection between the forced-zero certificate and
the descent defect.  Orders three and nine contradict the missing low
cyclotomic factor in the defect; order one contradicts `1 < m`. -/
theorem z180_k18_reducedFiveFactorDefect_of_fiveFactorDefect
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 18)
    (hdefect : Z180K18Projection36FiveFactorDefect A L) :
    Z180K18ReducedFiveFactorDefect A L := by
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hm36, hmgt, horderHigh,
    hhigh, hnotlow⟩ := hdefect
  let m : Nat := frequencyOrder 36
    (z180K18Projection36 l₁ - z180K18Projection36 l₂)
  change cyclotomic (5 * m) Int ∣ maskPolynomial 180 A at hhigh
  change ¬ cyclotomic m Int ∣ maskPolynomial 180 A at hnotlow
  have hcore := z180_k18_corePhi3Phi9Zeros_of_spectral hSpec hcard
  have hfreq60 : frequencyOrder 180 (60 : ZMod 180) = 3 := by decide
  have hfreq20 : frequencyOrder 180 (20 : ZMod 180) = 9 := by decide
  have hmask3 : cyclotomic 3 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq60] using hcore.1
  have hmask9 : cyclotomic 9 Int ∣ maskPolynomial 180 A := by
    simpa [Z180K18CorePhi3Phi9Zeros, CyclotomicZero, hfreq20] using hcore.2.1
  have hmpos : 0 < m := by omega
  have hcases : m = 2 ∨ m = 4 ∨ m = 6 ∨ m = 12 ∨ m = 18 ∨ m = 36 := by
    rcases z180_k18_base_divisor_cases m hmpos hm36 with
      h1 | h2 | h3 | h4 | h6 | h9 | h12 | h18 | h36
    · omega
    · exact Or.inl h2
    · exfalso
      apply hnotlow
      simpa [h3] using hmask3
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr (Or.inl h6))
    · exfalso
      apply hnotlow
      simpa [h9] using hmask9
    · exact Or.inr (Or.inr (Or.inr (Or.inl h12)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h18))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h36))))
  have hat : Z180K18FiveFactorDefectAt m A L :=
    ⟨l₁, hl₁, l₂, hl₂, hne, rfl, horderHigh, hhigh, hnotlow⟩
  rcases hcases with h2 | h4 | h6 | h12 | h18 | h36
  · exact Or.inl (by simpa [h2] using hat)
  · exact Or.inr (Or.inl (by simpa [h4] using hat))
  · exact Or.inr (Or.inr (Or.inl (by simpa [h6] using hat)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [h12] using hat))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [h18] using hat)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa [h36] using hat)))))

#print axioms z180_k18_corePhi3Phi9Zeros_of_spectral
#print axioms z180_k18_reducedFiveFactorDefect_of_fiveFactorDefect

end Fuglede
