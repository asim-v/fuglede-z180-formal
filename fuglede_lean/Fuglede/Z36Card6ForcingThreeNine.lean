import Fuglede.Z36Card6TilingCovers
import Fuglede.PrimeCyclotomic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

/-! A cardinality-six set cannot have simultaneous `Phi_3` and `Phi_9` zeros. -/

namespace Fuglede

open Polynomial

private theorem z36_cyclotomic_three_not_dvd_cyclotomic_nine :
    ¬ cyclotomic 3 Int ∣ cyclotomic 9 Int := by
  intro hdiv
  have hassoc : Associated (cyclotomic 3 Int) (cyclotomic 9 Int) :=
    Irreducible.associated_of_dvd
      (cyclotomic.irreducible (by norm_num : 0 < 3))
      (cyclotomic.irreducible (by norm_num : 0 < 9)) hdiv
  have hdegree : (cyclotomic 3 Int).natDegree =
      (cyclotomic 9 Int).natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
  rw [natDegree_cyclotomic, natDegree_cyclotomic] at hdegree
  have htotientThree : Nat.totient 3 = 2 := by
    simpa using Nat.totient_prime (by norm_num : Nat.Prime 3)
  have htotientNine : Nat.totient 9 = 6 := by
    rw [show 9 = 3 ^ 2 by norm_num,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num)]
    norm_num
  omega

private theorem z36_cyclotomic_three_mul_nine_dvd_mask
    (A : Finset (ZMod 36))
    (hthree : cyclotomic 3 Int ∣ maskPolynomial 36 A)
    (hnine : cyclotomic 9 Int ∣ maskPolynomial 36 A) :
    cyclotomic 3 Int * cyclotomic 9 Int ∣ maskPolynomial 36 A := by
  obtain ⟨Q, hQ⟩ := hnine
  rw [hQ] at hthree ⊢
  rcases (cyclotomic.irreducible (by norm_num : 0 < 3)).prime.dvd_mul.mp hthree with
    hbad | hdivQ
  · exact False.elim (z36_cyclotomic_three_not_dvd_cyclotomic_nine hbad)
  · obtain ⟨R, hR⟩ := hdivQ
    refine ⟨R, ?_⟩
    rw [hR]
    ring

theorem z36_nine_dvd_card_of_zeros_three_and_nine
    (A : Finset (ZMod 36))
    (hthree : Z36ZeroAtOrder A 3)
    (hnine : Z36ZeroAtOrder A 9) :
    9 ∣ A.card := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ :=
    z36_cyclotomic_three_mul_nine_dvd_mask A hthree hnine
  have heval := congrArg (Polynomial.eval (1 : Int)) hQ
  have hevalNine : Polynomial.eval (1 : Int) (cyclotomic 9 Int) = 3 := by
    convert (eval_one_cyclotomic_prime_pow (R := Int) (p := 3) 1) using 1 <;>
      norm_num
  have hint : (9 : Int) ∣ (A.card : Int) := by
    refine ⟨Polynomial.eval 1 Q, ?_⟩
    simpa [eval_one_maskPolynomial, Polynomial.eval_mul, hevalNine] using heval
  exact_mod_cast hint

theorem z36_zero_3_and_9_impossible
    (A : Finset (ZMod 36)) (hcard : A.card = 6)
    (hthree : Z36ZeroAtOrder A 3)
    (hnine : Z36ZeroAtOrder A 9) : False := by
  have hdiv := z36_nine_dvd_card_of_zeros_three_and_nine A hthree hnine
  rw [hcard] at hdiv
  norm_num at hdiv

#print axioms z36_nine_dvd_card_of_zeros_three_and_nine
#print axioms z36_zero_3_and_9_impossible

end Fuglede
