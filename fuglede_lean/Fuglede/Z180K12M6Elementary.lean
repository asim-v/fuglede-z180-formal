import Fuglede.PrimeCyclotomic
import Mathlib.Tactic

/-!
# Elementary exclusions in the cardinality-twelve `m = 6` branch

These are the two zero orders that require no finite enumeration: order five
is incompatible with cardinality twelve, and order six is ruled out directly
by the defining cyclotomic defect.
-/

namespace Fuglede

open Polynomial

theorem z180_k12_no_order5_zero
    {A : Finset (ZMod 180)} (hcard : A.card = 12)
    {d : ZMod 180} (horder : frequencyOrder 180 d = 5)
    (hzero : CyclotomicZero 180 A d) : False := by
  have hdiv : 5 ∣ A.card :=
    prime_dvd_card_of_cyclotomicZero
      (by norm_num) A d horder hzero
  rw [hcard] at hdiv
  norm_num at hdiv

theorem z180_k12_no_order6_zero
    {A : Finset (ZMod 180)}
    (hnot : ¬ cyclotomic 6 Int ∣ maskPolynomial 180 A)
    {d : ZMod 180} (horder : frequencyOrder 180 d = 6)
    (hzero : CyclotomicZero 180 A d) : False := by
  apply hnot
  simpa [CyclotomicZero, horder] using hzero

#print axioms z180_k12_no_order5_zero
#print axioms z180_k12_no_order6_zero

end Fuglede
