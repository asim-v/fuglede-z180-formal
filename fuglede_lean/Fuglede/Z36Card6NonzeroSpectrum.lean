import Fuglede.Z36Card6NonzeroPatternCore
import Fuglede.SpectralFourier

/-!
# Explicit nonzero spectra for six-point subsets of `ZMod 36`

The forcing theorem selects one of eight fixed six-frequency sets.  Their
nonzero differences have exactly the orders listed in the corresponding
clause of `Z36Card6NonzeroPattern`.
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def z36NonzeroQ0 : Finset (ZMod 36) := {0, 1, 2, 3, 4, 5}
def z36NonzeroQ1 : Finset (ZMod 36) := {0, 1, 2, 9, 10, 11}
def z36NonzeroQ2 : Finset (ZMod 36) := {0, 1, 5, 9, 28, 32}
def z36NonzeroQ3 : Finset (ZMod 36) := {0, 1, 12, 13, 24, 25}
def z36NonzeroQ4 : Finset (ZMod 36) := {0, 3, 12, 15, 24, 27}
def z36NonzeroQ5 : Finset (ZMod 36) := {0, 1, 2, 18, 19, 20}
def z36NonzeroQ6 : Finset (ZMod 36) := {0, 2, 4, 18, 20, 22}
def z36NonzeroQ7 : Finset (ZMod 36) := {0, 6, 12, 18, 24, 30}

theorem z36NonzeroQ0_card : z36NonzeroQ0.card = 6 := by decide
theorem z36NonzeroQ1_card : z36NonzeroQ1.card = 6 := by decide
theorem z36NonzeroQ2_card : z36NonzeroQ2.card = 6 := by decide
theorem z36NonzeroQ3_card : z36NonzeroQ3.card = 6 := by decide
theorem z36NonzeroQ4_card : z36NonzeroQ4.card = 6 := by decide
theorem z36NonzeroQ5_card : z36NonzeroQ5.card = 6 := by decide
theorem z36NonzeroQ6_card : z36NonzeroQ6.card = 6 := by decide
theorem z36NonzeroQ7_card : z36NonzeroQ7.card = 6 := by decide

theorem z36NonzeroQ0_orders :
    ∀ x ∈ z36NonzeroQ0, ∀ y ∈ z36NonzeroQ0, x ≠ y →
      frequencyOrder 36 (x - y) = 9 ∨
      frequencyOrder 36 (x - y) = 12 ∨
      frequencyOrder 36 (x - y) = 18 ∨
      frequencyOrder 36 (x - y) = 36 := by decide

theorem z36NonzeroQ1_orders :
    ∀ x ∈ z36NonzeroQ1, ∀ y ∈ z36NonzeroQ1, x ≠ y →
      frequencyOrder 36 (x - y) = 4 ∨
      frequencyOrder 36 (x - y) = 9 ∨
      frequencyOrder 36 (x - y) = 18 ∨
      frequencyOrder 36 (x - y) = 36 := by decide

theorem z36NonzeroQ2_orders :
    ∀ x ∈ z36NonzeroQ2, ∀ y ∈ z36NonzeroQ2, x ≠ y →
      frequencyOrder 36 (x - y) = 4 ∨
      frequencyOrder 36 (x - y) = 9 ∨
      frequencyOrder 36 (x - y) = 36 := by decide

theorem z36NonzeroQ3_orders :
    ∀ x ∈ z36NonzeroQ3, ∀ y ∈ z36NonzeroQ3, x ≠ y →
      frequencyOrder 36 (x - y) = 3 ∨
      frequencyOrder 36 (x - y) = 36 := by decide

theorem z36NonzeroQ4_orders :
    ∀ x ∈ z36NonzeroQ4, ∀ y ∈ z36NonzeroQ4, x ≠ y →
      frequencyOrder 36 (x - y) = 3 ∨
      frequencyOrder 36 (x - y) = 4 ∨
      frequencyOrder 36 (x - y) = 12 := by decide

theorem z36NonzeroQ5_orders :
    ∀ x ∈ z36NonzeroQ5, ∀ y ∈ z36NonzeroQ5, x ≠ y →
      frequencyOrder 36 (x - y) = 2 ∨
      frequencyOrder 36 (x - y) = 9 ∨
      frequencyOrder 36 (x - y) = 18 ∨
      frequencyOrder 36 (x - y) = 36 := by decide

theorem z36NonzeroQ6_orders :
    ∀ x ∈ z36NonzeroQ6, ∀ y ∈ z36NonzeroQ6, x ≠ y →
      frequencyOrder 36 (x - y) = 2 ∨
      frequencyOrder 36 (x - y) = 9 ∨
      frequencyOrder 36 (x - y) = 18 := by decide

theorem z36NonzeroQ7_orders :
    ∀ x ∈ z36NonzeroQ7, ∀ y ∈ z36NonzeroQ7, x ≠ y →
      frequencyOrder 36 (x - y) = 2 ∨
      frequencyOrder 36 (x - y) = 3 ∨
      frequencyOrder 36 (x - y) = 6 := by decide

private theorem not_cyclotomicZero_of_not_zeroAtOrder
    {A : Finset (ZMod 36)} {d : ZMod 36} {m : Nat}
    (horder : frequencyOrder 36 d = m) (hn : ¬ Z36ZeroAtOrder A m) :
    ¬ CyclotomicZero 36 A d := by
  intro hz
  apply hn
  simpa [CyclotomicZero, Z36ZeroAtOrder, horder] using hz

/-- A six-point set has a six-frequency set on whose nonzero differences
its Fourier transform never vanishes. -/
theorem z36_exists_six_frequencies_complement_nonzero
    (A : Finset (ZMod 36)) (hcard : A.card = 6) :
    ∃ Q : Finset (ZMod 36), Q.card = 6 ∧
      ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ¬ CyclotomicZero 36 A (x - y) := by
  rcases z36_card6_nonzero_pattern A hcard with
    h | h | h | h | h | h | h | h
  · refine ⟨z36NonzeroQ0, z36NonzeroQ0_card, ?_⟩
    intro x hx y hy hxy
    rcases z36NonzeroQ0_orders x hx y hy hxy with h9 | h12 | h18 | h36
    · exact not_cyclotomicZero_of_not_zeroAtOrder h9 h.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h12 h.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h18 h.2.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h36 h.2.2.2
  · refine ⟨z36NonzeroQ1, z36NonzeroQ1_card, ?_⟩
    intro x hx y hy hxy
    rcases z36NonzeroQ1_orders x hx y hy hxy with h4 | h9 | h18 | h36
    · exact not_cyclotomicZero_of_not_zeroAtOrder h4 h.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h9 h.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h18 h.2.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h36 h.2.2.2
  · refine ⟨z36NonzeroQ2, z36NonzeroQ2_card, ?_⟩
    intro x hx y hy hxy
    rcases z36NonzeroQ2_orders x hx y hy hxy with h4 | h9 | h36
    · exact not_cyclotomicZero_of_not_zeroAtOrder h4 h.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h9 h.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h36 h.2.2
  · refine ⟨z36NonzeroQ3, z36NonzeroQ3_card, ?_⟩
    intro x hx y hy hxy
    rcases z36NonzeroQ3_orders x hx y hy hxy with h3 | h36
    · exact not_cyclotomicZero_of_not_zeroAtOrder h3 h.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h36 h.2
  · refine ⟨z36NonzeroQ4, z36NonzeroQ4_card, ?_⟩
    intro x hx y hy hxy
    rcases z36NonzeroQ4_orders x hx y hy hxy with h3 | h4 | h12
    · exact not_cyclotomicZero_of_not_zeroAtOrder h3 h.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h4 h.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h12 h.2.2
  · refine ⟨z36NonzeroQ5, z36NonzeroQ5_card, ?_⟩
    intro x hx y hy hxy
    rcases z36NonzeroQ5_orders x hx y hy hxy with h2 | h9 | h18 | h36
    · exact not_cyclotomicZero_of_not_zeroAtOrder h2 h.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h9 h.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h18 h.2.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h36 h.2.2.2
  · refine ⟨z36NonzeroQ6, z36NonzeroQ6_card, ?_⟩
    intro x hx y hy hxy
    rcases z36NonzeroQ6_orders x hx y hy hxy with h2 | h9 | h18
    · exact not_cyclotomicZero_of_not_zeroAtOrder h2 h.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h9 h.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h18 h.2.2
  · refine ⟨z36NonzeroQ7, z36NonzeroQ7_card, ?_⟩
    intro x hx y hy hxy
    rcases z36NonzeroQ7_orders x hx y hy hxy with h2 | h3 | h6
    · exact not_cyclotomicZero_of_not_zeroAtOrder h2 h.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h3 h.2.1
    · exact not_cyclotomicZero_of_not_zeroAtOrder h6 h.2.2

#print axioms z36_exists_six_frequencies_complement_nonzero

end Fuglede
