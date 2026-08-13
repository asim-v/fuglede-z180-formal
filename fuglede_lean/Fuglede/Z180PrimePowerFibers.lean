import Fuglede.Z180ProjectionTiles
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

/-!
# Prime-square cardinality obstruction at modulus 180

The appendix argument used for the `60` and `90` cardinality cases needs the
following elementary fact.  If the mask polynomial has zeros of both
prime-power orders `p` and `p^2`, then its value at one is divisible by
`p^2`.  We prove the two instances needed at modulus `180` directly in
`ℤ[X]`: distinct cyclotomic polynomials are irreducible, hence prime, so their
product divides the mask polynomial.
-/

namespace Fuglede

open Polynomial

private theorem cyclotomic_three_not_dvd_cyclotomic_nine :
    ¬ cyclotomic 3 ℤ ∣ cyclotomic 9 ℤ := by
  intro hdiv
  have hassoc : Associated (cyclotomic 3 ℤ) (cyclotomic 9 ℤ) :=
    Irreducible.associated_of_dvd
      (cyclotomic.irreducible (by norm_num : 0 < 3))
      (cyclotomic.irreducible (by norm_num : 0 < 9)) hdiv
  have hdegree : (cyclotomic 3 ℤ).natDegree =
      (cyclotomic 9 ℤ).natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
  rw [natDegree_cyclotomic, natDegree_cyclotomic] at hdegree
  have htotientThree : Nat.totient 3 = 2 := by
    simpa using Nat.totient_prime (by norm_num : Nat.Prime 3)
  have htotientNine : Nat.totient 9 = 6 := by
    rw [show 9 = 3 ^ 2 by norm_num,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num)]
    norm_num
  omega

private theorem cyclotomic_two_not_dvd_cyclotomic_four :
    ¬ cyclotomic 2 ℤ ∣ cyclotomic 4 ℤ := by
  intro hdiv
  have hassoc : Associated (cyclotomic 2 ℤ) (cyclotomic 4 ℤ) :=
    Irreducible.associated_of_dvd
      (cyclotomic.irreducible (by norm_num : 0 < 2))
      (cyclotomic.irreducible (by norm_num : 0 < 4)) hdiv
  have hdegree : (cyclotomic 2 ℤ).natDegree =
      (cyclotomic 4 ℤ).natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)
  rw [natDegree_cyclotomic, natDegree_cyclotomic] at hdegree
  have htotientTwo : Nat.totient 2 = 1 := Nat.totient_two
  have htotientFour : Nat.totient 4 = 2 := by
    rw [show 4 = 2 ^ 2 by norm_num,
      Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num)]
    norm_num
  omega

private theorem cyclotomic_three_mul_nine_dvd_mask
    (X : Finset (ZMod 180))
    (hthree : cyclotomic 3 ℤ ∣ maskPolynomial 180 X)
    (hnine : cyclotomic 9 ℤ ∣ maskPolynomial 180 X) :
    cyclotomic 3 ℤ * cyclotomic 9 ℤ ∣ maskPolynomial 180 X := by
  obtain ⟨Q, hQ⟩ := hnine
  rw [hQ] at hthree ⊢
  rcases (cyclotomic.irreducible (by norm_num : 0 < 3)).prime.dvd_mul.mp hthree with
    hbad | hdivQ
  · exact False.elim (cyclotomic_three_not_dvd_cyclotomic_nine hbad)
  · obtain ⟨R, hR⟩ := hdivQ
    refine ⟨R, ?_⟩
    rw [hR]
    ring

private theorem cyclotomic_two_mul_four_dvd_mask
    (X : Finset (ZMod 180))
    (htwo : cyclotomic 2 ℤ ∣ maskPolynomial 180 X)
    (hfour : cyclotomic 4 ℤ ∣ maskPolynomial 180 X) :
    cyclotomic 2 ℤ * cyclotomic 4 ℤ ∣ maskPolynomial 180 X := by
  obtain ⟨Q, hQ⟩ := hfour
  rw [hQ] at htwo ⊢
  rcases (cyclotomic.irreducible (by norm_num : 0 < 2)).prime.dvd_mul.mp htwo with
    hbad | hdivQ
  · exact False.elim (cyclotomic_two_not_dvd_cyclotomic_four hbad)
  · obtain ⟨R, hR⟩ := hdivQ
    refine ⟨R, ?_⟩
    rw [hR]
    ring

/-- Simultaneous order-three and order-nine cyclotomic zeros force a factor
of nine in the cardinality. -/
theorem nine_dvd_card_of_cyclotomic_three_and_nine
    (X : Finset (ZMod 180))
    (hthree : cyclotomic 3 ℤ ∣ maskPolynomial 180 X)
    (hnine : cyclotomic 9 ℤ ∣ maskPolynomial 180 X) :
    9 ∣ X.card := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := cyclotomic_three_mul_nine_dvd_mask X hthree hnine
  have heval := congrArg (Polynomial.eval (1 : ℤ)) hQ
  have hevalNine : Polynomial.eval (1 : ℤ) (cyclotomic 9 ℤ) = 3 := by
    convert (eval_one_cyclotomic_prime_pow (R := ℤ) (p := 3) 1) using 1 <;>
      norm_num
  have hint : (9 : ℤ) ∣ (X.card : ℤ) := by
    refine ⟨Polynomial.eval 1 Q, ?_⟩
    simpa [eval_one_maskPolynomial, Polynomial.eval_mul, hevalNine] using heval
  exact_mod_cast hint

/-- Simultaneous order-two and order-four cyclotomic zeros force a factor of
four in the cardinality. -/
theorem four_dvd_card_of_cyclotomic_two_and_four
    (X : Finset (ZMod 180))
    (htwo : cyclotomic 2 ℤ ∣ maskPolynomial 180 X)
    (hfour : cyclotomic 4 ℤ ∣ maskPolynomial 180 X) :
    4 ∣ X.card := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := cyclotomic_two_mul_four_dvd_mask X htwo hfour
  have heval := congrArg (Polynomial.eval (1 : ℤ)) hQ
  have hevalFour : Polynomial.eval (1 : ℤ) (cyclotomic 4 ℤ) = 2 := by
    convert (eval_one_cyclotomic_prime_pow (R := ℤ) (p := 2) 1) using 1 <;>
      norm_num
  have hint : (4 : ℤ) ∣ (X.card : ℤ) := by
    refine ⟨Polynomial.eval 1 Q, ?_⟩
    simpa [eval_one_maskPolynomial, Polynomial.eval_mul, hevalFour] using heval
  exact_mod_cast hint

/-- Frequency-form specialization used by the `|A| = 60` fibre argument. -/
theorem nine_dvd_card_of_cyclotomicZero_orders_three_and_nine
    (X : Finset (ZMod 180)) {d₃ d₉ : ZMod 180}
    (horder₃ : frequencyOrder 180 d₃ = 3)
    (horder₉ : frequencyOrder 180 d₉ = 9)
    (hzero₃ : CyclotomicZero 180 X d₃)
    (hzero₉ : CyclotomicZero 180 X d₉) :
    9 ∣ X.card := by
  apply nine_dvd_card_of_cyclotomic_three_and_nine X
  · simpa [CyclotomicZero, horder₃] using hzero₃
  · simpa [CyclotomicZero, horder₉] using hzero₉

/-- Frequency-form specialization used by the `|A| = 90` fibre argument. -/
theorem four_dvd_card_of_cyclotomicZero_orders_two_and_four
    (X : Finset (ZMod 180)) {d₂ d₄ : ZMod 180}
    (horder₂ : frequencyOrder 180 d₂ = 2)
    (horder₄ : frequencyOrder 180 d₄ = 4)
    (hzero₂ : CyclotomicZero 180 X d₂)
    (hzero₄ : CyclotomicZero 180 X d₄) :
    4 ∣ X.card := by
  apply four_dvd_card_of_cyclotomic_two_and_four X
  · simpa [CyclotomicZero, horder₂] using hzero₂
  · simpa [CyclotomicZero, horder₄] using hzero₄

/-! ## A generic fibrewise tiling endpoint -/

/-- If `B` lies in the kernel of a cyclic projection, nonzero differences
inside projection fibres of `A` have order `rA`, and nonzero differences in
`B` have a different order `rB`, then the addition map is injective.  The
cardinality identity upgrades it to a tiling. -/
private theorem tiles_of_projection_fiber_opposite_orders
    {A B : Finset (ZMod 180)} {m rA rB : Nat}
    (hm : m ∣ 180)
    (hcard : A.card * B.card = 180)
    (hBkernel : ∀ b ∈ B, (ZMod.cast b : ZMod m) = 0)
    (hAorder : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
      (ZMod.cast a : ZMod m) = ZMod.cast a' →
      frequencyOrder 180 (a - a') = rA)
    (hBorder : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' →
      frequencyOrder 180 (b - b') = rB)
    (horders : rA ≠ rB) :
    Tiles A B := by
  apply (Fintype.bijective_iff_injective_and_card (sumMap A B)).2
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ hsum
    have ha : a ∈ A := (Finset.mem_product.mp hab).1
    have hb : b ∈ B := (Finset.mem_product.mp hab).2
    have ha' : a' ∈ A := (Finset.mem_product.mp hab').1
    have hb' : b' ∈ B := (Finset.mem_product.mp hab').2
    change a + b = a' + b' at hsum
    have haa : a = a' := by
      by_contra hane
      have hcast : (ZMod.cast a : ZMod m) = ZMod.cast a' := by
        have hmapped := congrArg
          (fun z : ZMod 180 => (ZMod.cast z : ZMod m)) hsum
        simpa [ZMod.cast_add hm, hBkernel b hb, hBkernel b' hb'] using hmapped
      have hbbne : b' ≠ b := by
        intro hbb
        subst b'
        exact hane (add_right_cancel hsum)
      have hdiff : a - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add]
        simpa [add_comm] using hsum
      apply horders
      calc
        rA = frequencyOrder 180 (a - a') :=
          (hAorder a ha a' ha' hane hcast).symm
        _ = frequencyOrder 180 (b' - b) := congrArg _ hdiff
        _ = rB := hBorder b' hb' b hb hbbne
    subst a'
    have hbb : b = b' := add_left_cancel hsum
    subst b'
    rfl
  · simpa only [Fintype.card_coe, Finset.card_product, ZMod.card] using hcard

private def z180OrderNineComplement : Finset (ZMod 180) := {0, 20, 40}
private def z180OrderThreeComplement : Finset (ZMod 180) := {0, 60, 120}
private def z180OrderFourComplement : Finset (ZMod 180) := {0, 45}
private def z180OrderTwoComplement : Finset (ZMod 180) := {0, 90}

private theorem z180OrderNineComplement_cast20_zero
    {b : ZMod 180} (hb : b ∈ z180OrderNineComplement) :
    (ZMod.cast b : ZMod 20) = 0 := by
  simp only [z180OrderNineComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;> decide

private theorem z180OrderThreeComplement_cast20_zero
    {b : ZMod 180} (hb : b ∈ z180OrderThreeComplement) :
    (ZMod.cast b : ZMod 20) = 0 := by
  simp only [z180OrderThreeComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;> decide

private theorem z180OrderFourComplement_cast45_zero
    {b : ZMod 180} (hb : b ∈ z180OrderFourComplement) :
    (ZMod.cast b : ZMod 45) = 0 := by
  simp only [z180OrderFourComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl <;> decide

private theorem z180OrderTwoComplement_cast45_zero
    {b : ZMod 180} (hb : b ∈ z180OrderTwoComplement) :
    (ZMod.cast b : ZMod 45) = 0 := by
  simp only [z180OrderTwoComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl <;> decide

private theorem z180OrderNineComplement_difference_order
    {b b' : ZMod 180}
    (hb : b ∈ z180OrderNineComplement)
    (hb' : b' ∈ z180OrderNineComplement) (hne : b ≠ b') :
    frequencyOrder 180 (b - b') = 9 := by
  simp only [z180OrderNineComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb hb'
  rcases hb with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl
  all_goals first | exact (hne rfl).elim | decide

private theorem z180OrderThreeComplement_difference_order
    {b b' : ZMod 180}
    (hb : b ∈ z180OrderThreeComplement)
    (hb' : b' ∈ z180OrderThreeComplement) (hne : b ≠ b') :
    frequencyOrder 180 (b - b') = 3 := by
  simp only [z180OrderThreeComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb hb'
  rcases hb with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl
  all_goals first | exact (hne rfl).elim | decide

private theorem z180OrderFourComplement_difference_order
    {b b' : ZMod 180}
    (hb : b ∈ z180OrderFourComplement)
    (hb' : b' ∈ z180OrderFourComplement) (hne : b ≠ b') :
    frequencyOrder 180 (b - b') = 4 := by
  simp only [z180OrderFourComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb hb'
  rcases hb with rfl | rfl <;>
    rcases hb' with rfl | rfl
  all_goals first | exact (hne rfl).elim | decide

private theorem z180OrderTwoComplement_difference_order
    {b b' : ZMod 180}
    (hb : b ∈ z180OrderTwoComplement)
    (hb' : b' ∈ z180OrderTwoComplement) (hne : b ≠ b') :
    frequencyOrder 180 (b - b') = 2 := by
  simp only [z180OrderTwoComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb hb'
  rcases hb with rfl | rfl <;>
    rcases hb' with rfl | rfl
  all_goals first | exact (hne rfl).elim | decide

/-! ## The cardinalities 60 and 90 -/

/-- The prime-square quotient argument at cardinality `60`: all differences
inside a projection-modulo-20 fibre have the same 3-primary order.  The
opposite three-point kernel pattern is therefore a tiling complement. -/
theorem z180_exists_tiling_of_spectral_card_sixty
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 60) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  by_cases hthree : ∃ a ∈ A, ∃ a' ∈ A, a ≠ a' ∧
      (ZMod.cast a : ZMod 20) = ZMod.cast a' ∧
      frequencyOrder 180 (a - a') = 3
  · have hAllThree : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 20) = ZMod.cast a' →
        frequencyOrder 180 (a - a') = 3 := by
      intro a ha a' ha' hne hcast
      rcases z180_frequencyOrder_three_or_nine_of_cast20_eq a a' hne hcast with
        horder | horder
      · exact horder
      · rcases hthree with ⟨u, hu, u', hu', hune, hucast, huorder⟩
        have hdual := cyclotomicSpectrum_dual hSpec
        have hzeroThree : CyclotomicZero 180 L (u - u') :=
          hdual.2.2 u hu u' hu' hune
        have hzeroNine : CyclotomicZero 180 L (a - a') :=
          hdual.2.2 a ha a' ha' hne
        have hdivL := nine_dvd_card_of_cyclotomicZero_orders_three_and_nine
          L huorder horder hzeroThree hzeroNine
        have hdivA : 9 ∣ A.card := by simpa [hSpec.2.1] using hdivL
        omega
    refine ⟨z180OrderNineComplement, ?_⟩
    apply tiles_of_projection_fiber_opposite_orders
      (m := 20) (rA := 3) (rB := 9) (by norm_num)
    · rw [hcard]
      decide
    · intro b hb
      exact z180OrderNineComplement_cast20_zero hb
    · exact hAllThree
    · intro b hb b' hb' hne
      exact z180OrderNineComplement_difference_order hb hb' hne
    · norm_num
  · have hAllNine : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 20) = ZMod.cast a' →
        frequencyOrder 180 (a - a') = 9 := by
      intro a ha a' ha' hne hcast
      rcases z180_frequencyOrder_three_or_nine_of_cast20_eq a a' hne hcast with
        horder | horder
      · exact False.elim (hthree ⟨a, ha, a', ha', hne, hcast, horder⟩)
      · exact horder
    refine ⟨z180OrderThreeComplement, ?_⟩
    apply tiles_of_projection_fiber_opposite_orders
      (m := 20) (rA := 9) (rB := 3) (by norm_num)
    · rw [hcard]
      decide
    · intro b hb
      exact z180OrderThreeComplement_cast20_zero hb
    · exact hAllNine
    · intro b hb b' hb' hne
      exact z180OrderThreeComplement_difference_order hb hb' hne
    · norm_num

/-- The analogous prime-square quotient argument at cardinality `90`. -/
theorem z180_exists_tiling_of_spectral_card_ninety
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 90) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  by_cases htwo : ∃ a ∈ A, ∃ a' ∈ A, a ≠ a' ∧
      (ZMod.cast a : ZMod 45) = ZMod.cast a' ∧
      frequencyOrder 180 (a - a') = 2
  · have hAllTwo : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 45) = ZMod.cast a' →
        frequencyOrder 180 (a - a') = 2 := by
      intro a ha a' ha' hne hcast
      rcases z180_frequencyOrder_two_or_four_of_cast45_eq a a' hne hcast with
        horder | horder
      · exact horder
      · rcases htwo with ⟨u, hu, u', hu', hune, hucast, huorder⟩
        have hdual := cyclotomicSpectrum_dual hSpec
        have hzeroTwo : CyclotomicZero 180 L (u - u') :=
          hdual.2.2 u hu u' hu' hune
        have hzeroFour : CyclotomicZero 180 L (a - a') :=
          hdual.2.2 a ha a' ha' hne
        have hdivL := four_dvd_card_of_cyclotomicZero_orders_two_and_four
          L huorder horder hzeroTwo hzeroFour
        have hdivA : 4 ∣ A.card := by simpa [hSpec.2.1] using hdivL
        omega
    refine ⟨z180OrderFourComplement, ?_⟩
    apply tiles_of_projection_fiber_opposite_orders
      (m := 45) (rA := 2) (rB := 4) (by norm_num)
    · rw [hcard]
      decide
    · intro b hb
      exact z180OrderFourComplement_cast45_zero hb
    · exact hAllTwo
    · intro b hb b' hb' hne
      exact z180OrderFourComplement_difference_order hb hb' hne
    · norm_num
  · have hAllFour : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
        (ZMod.cast a : ZMod 45) = ZMod.cast a' →
        frequencyOrder 180 (a - a') = 4 := by
      intro a ha a' ha' hne hcast
      rcases z180_frequencyOrder_two_or_four_of_cast45_eq a a' hne hcast with
        horder | horder
      · exact False.elim (htwo ⟨a, ha, a', ha', hne, hcast, horder⟩)
      · exact horder
    refine ⟨z180OrderTwoComplement, ?_⟩
    apply tiles_of_projection_fiber_opposite_orders
      (m := 45) (rA := 4) (rB := 2) (by norm_num)
    · rw [hcard]
      decide
    · intro b hb
      exact z180OrderTwoComplement_cast45_zero hb
    · exact hAllFour
    · intro b hb b' hb' hne
      exact z180OrderTwoComplement_difference_order hb hb' hne
    · norm_num

#print axioms nine_dvd_card_of_cyclotomicZero_orders_three_and_nine
#print axioms four_dvd_card_of_cyclotomicZero_orders_two_and_four
#print axioms z180_exists_tiling_of_spectral_card_sixty
#print axioms z180_exists_tiling_of_spectral_card_ninety

end Fuglede
