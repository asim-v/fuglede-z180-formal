import Fuglede.Z36Card6DifferenceCore
import Fuglede.Z36Card6ForcingClosure
import Fuglede.Z36Card6ForcingPhi6Phi36Semantic
import Fuglede.Z36Card18PrimePowerFiberCore

/-!
# A finite nonzero-frequency cover for six-point subsets of `ZMod 36`

The eight clauses below correspond to eight explicit six-frequency sets.
Each clause says that every nonzero difference order of the corresponding
frequency set avoids the cyclotomic zero set of `A`.
-/

namespace Fuglede

set_option maxHeartbeats 0
set_option maxRecDepth 10000

def Z36Card6NonzeroPattern (A : Finset (ZMod 36)) : Prop :=
  (¬ Z36ZeroAtOrder A 9 ∧ ¬ Z36ZeroAtOrder A 12 ∧
      ¬ Z36ZeroAtOrder A 18 ∧ ¬ Z36ZeroAtOrder A 36) ∨
  (¬ Z36ZeroAtOrder A 4 ∧ ¬ Z36ZeroAtOrder A 9 ∧
      ¬ Z36ZeroAtOrder A 18 ∧ ¬ Z36ZeroAtOrder A 36) ∨
  (¬ Z36ZeroAtOrder A 4 ∧ ¬ Z36ZeroAtOrder A 9 ∧
      ¬ Z36ZeroAtOrder A 36) ∨
  (¬ Z36ZeroAtOrder A 3 ∧ ¬ Z36ZeroAtOrder A 36) ∨
  (¬ Z36ZeroAtOrder A 3 ∧ ¬ Z36ZeroAtOrder A 4 ∧
      ¬ Z36ZeroAtOrder A 12) ∨
  (¬ Z36ZeroAtOrder A 2 ∧ ¬ Z36ZeroAtOrder A 9 ∧
      ¬ Z36ZeroAtOrder A 18 ∧ ¬ Z36ZeroAtOrder A 36) ∨
  (¬ Z36ZeroAtOrder A 2 ∧ ¬ Z36ZeroAtOrder A 9 ∧
      ¬ Z36ZeroAtOrder A 18) ∨
  (¬ Z36ZeroAtOrder A 2 ∧ ¬ Z36ZeroAtOrder A 3 ∧
      ¬ Z36ZeroAtOrder A 6)

private theorem z36_cyclotomicZero_of_zeroAtOrder_for_pattern
    {A : Finset (ZMod 36)} {m : Nat} (d : ZMod 36)
    (horder : frequencyOrder 36 d = m) (h : Z36ZeroAtOrder A m) :
    CyclotomicZero 36 A d := by
  simpa [CyclotomicZero, Z36ZeroAtOrder, horder] using h

theorem z36_not_zero_two_and_four_public
    (A : Finset (ZMod 36)) (hcard : A.card = 6) :
    ¬ (Z36ZeroAtOrder A 2 ∧ Z36ZeroAtOrder A 4) := by
  rintro ⟨h2, h4⟩
  have hdiv := z36_four_dvd_card_of_cyclotomicZero_orders_two_and_four
    A (d₂ := (18 : ZMod 36)) (d₄ := (9 : ZMod 36))
    (by decide) (by decide)
    (z36_cyclotomicZero_of_zeroAtOrder_for_pattern 18 (by decide) h2)
    (z36_cyclotomicZero_of_zeroAtOrder_for_pattern 9 (by decide) h4)
  rw [hcard] at hdiv
  norm_num at hdiv

/-- Every six-point subset of `ZMod 36` admits one of the eight explicit
nonzero difference-order patterns used below. -/
theorem z36_card6_nonzero_pattern
    (A : Finset (ZMod 36)) (hcard : A.card = 6) :
    Z36Card6NonzeroPattern A := by
  have hn24 := z36_not_zero_two_and_four_public A hcard
  have h39 := z36_zero_3_and_9_impossible A hcard
  have h318 := z36_zero_3_18_forces_2_6 A hcard
  have h336 := z36_zero_3_36_forces_4_12 A hcard
  have h36 := z36_zero_36_forces_12_or_18 A hcard
  have h6918 := z36_zero_6_9_18_forces_2 A hcard
  have h1236 := z36_zero_12_36_forces_4 A hcard
  have h636 := z36_zero_6_36_forces_2_or_3 A hcard
  by_cases h2 : Z36ZeroAtOrder A 2 <;>
  by_cases h3 : Z36ZeroAtOrder A 3 <;>
  by_cases h4 : Z36ZeroAtOrder A 4 <;>
  by_cases h6 : Z36ZeroAtOrder A 6 <;>
  by_cases h9 : Z36ZeroAtOrder A 9 <;>
  by_cases h12 : Z36ZeroAtOrder A 12 <;>
  by_cases h18 : Z36ZeroAtOrder A 18 <;>
  by_cases h36z : Z36ZeroAtOrder A 36 <;>
    simp_all [Z36Card6NonzeroPattern]

#print axioms z36_card6_nonzero_pattern

end Fuglede
