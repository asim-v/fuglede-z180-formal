import Fuglede.CyclicCertificate
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic.NormNum

/-!
# Prime cyclotomic zeros force cardinal divisibility

This file internalizes the elementary evaluation-at-one step used by the
multiaxis reduction.  It is deliberately stated first for an arbitrary prime
cyclotomic divisor and then connected to `CyclotomicZero`.
-/

namespace Fuglede

open Polynomial

/-- Evaluating a finite-set mask polynomial at one counts the set. -/
theorem eval_one_maskPolynomial {N : ℕ} (A : Finset (ZMod N)) :
    (maskPolynomial N A).eval 1 = (A.card : ℤ) := by
  simp [maskPolynomial, Polynomial.eval_finsetSum]

/-- A prime cyclotomic divisor of a mask polynomial forces that prime to
divide the cardinality of the underlying set. -/
theorem prime_dvd_card_of_cyclotomic_dvd_mask {N p : ℕ}
    (hp : p.Prime) (A : Finset (ZMod N))
    (hdiv : cyclotomic p ℤ ∣ maskPolynomial N A) :
    p ∣ A.card := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := hdiv
  have heval := congrArg (Polynomial.eval (1 : ℤ)) hQ
  have hint : (p : ℤ) ∣ (A.card : ℤ) := by
    refine ⟨Polynomial.eval 1 Q, ?_⟩
    simpa [eval_one_maskPolynomial, Polynomial.eval_mul] using heval
  exact_mod_cast hint

/-- The same divisibility consequence in the exact spectral-certificate
language used by this project. -/
theorem prime_dvd_card_of_cyclotomicZero {N p : ℕ}
    (hp : p.Prime) (A : Finset (ZMod N)) (d : ZMod N)
    (horder : frequencyOrder N d = p)
    (hzero : CyclotomicZero N A d) :
    p ∣ A.card := by
  apply prime_dvd_card_of_cyclotomic_dvd_mask hp A
  simpa [CyclotomicZero, horder] using hzero

end Fuglede
