import Fuglede.LabaMarshall
import Fuglede.FourierCrossImplications

/-!
# The cyclotomic-to-cuboid bridge at modulus 2310

This file supplies the Fourier-analytic part of the cuboid argument used in
Laba--Marshall Corollary 6.5.  The arithmetic endpoint remains in
`Fuglede.LabaMarshall`.
-/

namespace Fuglede

open scoped BigOperators ComplexConjugate
open Polynomial

/-- The Fourier coefficient of an alternating CRT cuboid. -/
noncomputable def crtCuboidFourierCoefficient
    (D : Finset (Fin 5)) (lo hi d : CRT2310) : ℂ :=
  ∏ i ∈ D,
    (standardCoordinateChar (-lo) i (d i) -
      standardCoordinateChar (-hi) i (d i))

theorem standardCoordinateChar_add (z w : CRT2310) (i : Fin 5)
    (a : ZMod (crt2310Modulus i)) :
    standardCoordinateChar z i a * standardCoordinateChar w i a =
      standardCoordinateChar (z + w) i a := by
  rw [standardCoordinateChar_apply, standardCoordinateChar_apply,
    standardCoordinateChar_apply, ← AddChar.map_add_eq_mul]
  congr 1
  change crt2310AddEquiv.symm _ + crt2310AddEquiv.symm _ =
    crt2310AddEquiv.symm _
  rw [← crt2310AddEquiv.symm.map_add]
  congr 1
  ext j
  by_cases hji : j = i
  · subst j
    simpa using (mul_add a (z i) (w i)).symm
  · simp [hji]

theorem standardCoordinateChar_neg_mul (z w : CRT2310) (i : Fin 5)
    (a : ZMod (crt2310Modulus i)) :
    standardCoordinateChar (-w) i a * standardCoordinateChar z i a =
      standardCoordinateChar (z - w) i a := by
  rw [standardCoordinateChar_add]
  congr 2
  abel

/-- One-dimensional Fourier inversion for the difference of two point
masses.  The distinctness hypothesis is essential: the ordered `if` used by
`crtCuboidSign` would otherwise not be an alternating difference. -/
theorem sum_nonzero_standardCoordinateChar_cuboid
    (z lo hi : CRT2310) (i : Fin 5) (hlohi : lo i ≠ hi i) :
    (∑ a ∈ nonzeroCoordinateFrequencies i,
        (standardCoordinateChar (-lo) i a -
            standardCoordinateChar (-hi) i a) *
          standardCoordinateChar z i a) =
      (crt2310Modulus i : ℂ) *
        (if z i = lo i then 1 else if z i = hi i then -1 else 0) := by
  classical
  simp_rw [sub_mul, standardCoordinateChar_neg_mul]
  rw [Finset.sum_sub_distrib,
    sum_nonzero_standardCoordinateChar,
    sum_nonzero_standardCoordinateChar]
  by_cases hzlo : z i = lo i
  · have hsublo : (z - lo) i = 0 := by simp [Pi.sub_apply, hzlo]
    have hsubhi : (z - hi) i ≠ 0 := by
      simpa [Pi.sub_apply, sub_ne_zero, hzlo] using hlohi
    rw [if_pos hsublo, if_neg hsubhi, if_pos hzlo]
    have hcast : (((crt2310Modulus i : Int) : ℂ)) =
        (crt2310Modulus i : ℂ) := by norm_cast
    rw [hcast]
    ring
  · by_cases hzhi : z i = hi i
    · have hsublo : (z - lo) i ≠ 0 := by
        simpa [Pi.sub_apply, sub_ne_zero] using hzlo
      have hsubhi : (z - hi) i = 0 := by simp [Pi.sub_apply, hzhi]
      rw [if_neg hsublo, if_pos hsubhi, if_neg hzlo, if_pos hzhi]
      have hcast : (((crt2310Modulus i : Int) : ℂ)) =
          (crt2310Modulus i : ℂ) := by norm_cast
      rw [hcast]
      ring
    · have hsublo : (z - lo) i ≠ 0 := by
        simpa [Pi.sub_apply, sub_ne_zero]
      have hsubhi : (z - hi) i ≠ 0 := by
        simpa [Pi.sub_apply, sub_ne_zero]
      rw [if_neg hsublo, if_neg hsubhi, if_neg hzlo, if_neg hzhi]
      ring

/-- The local factor whose product is one summand in the Fourier expansion
of a cuboid. -/
noncomputable def crtCuboidLocalFourierFactor
    (D : Finset (Fin 5)) (lo hi z : CRT2310) (i : Fin 5)
    (a : ZMod (crt2310Modulus i)) : ℂ :=
  if i ∈ D then
    (standardCoordinateChar (-lo) i a -
        standardCoordinateChar (-hi) i a) *
      standardCoordinateChar z i a
  else standardCoordinateChar z i a

private theorem cuboid_coefficient_mul_pairing_eq_prod_local
    (D : Finset (Fin 5)) (lo hi z d : CRT2310) :
    crtCuboidFourierCoefficient D lo hi d *
        standardCRTCharacterPairing z d =
      ∏ i, crtCuboidLocalFourierFactor D lo hi z i (d i) := by
  classical
  rw [crtCuboidFourierCoefficient,
    standardCRTCharacterPairing_eq_prod]
  have hext :
      (∏ i ∈ D,
          (standardCoordinateChar (-lo) i (d i) -
            standardCoordinateChar (-hi) i (d i))) =
        ∏ i, if i ∈ D then
          (standardCoordinateChar (-lo) i (d i) -
            standardCoordinateChar (-hi) i (d i)) else 1 := by
    calc
      (∏ i ∈ D,
          (standardCoordinateChar (-lo) i (d i) -
            standardCoordinateChar (-hi) i (d i))) =
          ∏ i ∈ D, if i ∈ D then
            (standardCoordinateChar (-lo) i (d i) -
              standardCoordinateChar (-hi) i (d i)) else 1 := by simp
      _ = ∏ i, if i ∈ D then
            (standardCoordinateChar (-lo) i (d i) -
              standardCoordinateChar (-hi) i (d i)) else 1 := by
        apply Finset.prod_subset (Finset.subset_univ D)
        intro i hi hiD
        simp [hiD]
  rw [hext, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [crtCuboidLocalFourierFactor]
  by_cases hiD : i ∈ D <;> simp [hiD]

/-- Product-form Fourier inversion for an alternating CRT cuboid. -/
theorem sum_exactCRTFrequencies_cuboid
    (D : Finset (Fin 5)) (lo hi z : CRT2310)
    (hdistinct : ∀ i ∈ D, lo i ≠ hi i) :
    (∑ d ∈ exactCRTFrequencies D,
        crtCuboidFourierCoefficient D lo hi d *
          standardCRTCharacterPairing z d) =
      (∏ i ∈ D, (crt2310Modulus i : ℂ)) *
        ∏ i ∈ D,
          (if z i = lo i then (1 : ℂ)
            else if z i = hi i then -1 else 0) := by
  classical
  simp_rw [cuboid_coefficient_mul_pairing_eq_prod_local]
  rw [exactCRTFrequencies]
  calc
    (∑ d ∈ Fintype.piFinset (coordinateFrequencySet D),
        ∏ i, crtCuboidLocalFourierFactor D lo hi z i (d i)) =
        ∏ i, ∑ a ∈ coordinateFrequencySet D i,
          crtCuboidLocalFourierFactor D lo hi z i a := by
      exact (Finset.prod_univ_sum (coordinateFrequencySet D)
        (fun i a ↦ crtCuboidLocalFourierFactor D lo hi z i a)).symm
    _ = ∏ i ∈ D,
          ((crt2310Modulus i : ℂ) *
            (if z i = lo i then (1 : ℂ)
              else if z i = hi i then -1 else 0)) := by
      symm
      apply Finset.prod_subset_one_on_sdiff (Finset.subset_univ D)
      · intro i hi
        have hiD : i ∉ D := (Finset.mem_sdiff.mp hi).2
        simp [coordinateFrequencySet, crtCuboidLocalFourierFactor, hiD]
      · intro i hiD
        simp only [coordinateFrequencySet, crtCuboidLocalFourierFactor,
          if_pos hiD]
        exact (sum_nonzero_standardCoordinateChar_cuboid
          z lo hi i (hdistinct i hiD)).symm
    _ = (∏ i ∈ D, (crt2310Modulus i : ℂ)) *
          ∏ i ∈ D,
            (if z i = lo i then (1 : ℂ)
              else if z i = hi i then -1 else 0) := by
      rw [Finset.prod_mul_distrib]

/-- Complex coercion of the integer cuboid sign in CRT coordinates. -/
theorem crtCuboidSign_cast
    (D : Finset (Fin 5)) (lo hi z : CRT2310) :
    ((crtCuboidSign D lo hi (fromCRT2310 z) : Int) : ℂ) =
      ∏ i ∈ D,
        (if z i = lo i then (1 : ℂ)
          else if z i = hi i then -1 else 0) := by
  classical
  rw [crtCuboidSign]
  push_cast
  apply Finset.prod_congr rfl
  intro i hiD
  rw [toCRT2310_fromCRT2310]

/-- Fourier expansion of an integer cuboid evaluation of a finite set. -/
theorem sum_exactCRTFrequencies_cuboid_mul_fourierSum
    (A : Finset (ZMod 2310)) (D : Finset (Fin 5))
    (lo hi : CRT2310) (hdistinct : ∀ i ∈ D, lo i ≠ hi i) :
    (∑ d ∈ exactCRTFrequencies D,
        crtCuboidFourierCoefficient D lo hi d *
          fourierSum A (fromCRT2310 d)) =
      (supportModulus D : ℂ) *
        (signedFinsetEvaluation A (crtCuboidSign D lo hi) : ℂ) := by
  classical
  simp_rw [← standardCRTFourierSum_eq_fourierSum]
  simp only [standardCRTFourierSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ A, ∑ d ∈ exactCRTFrequencies D,
        crtCuboidFourierCoefficient D lo hi d *
          standardCRTCharacterPairing (toCRT2310 x) d) =
        ∑ x ∈ A,
          ((∏ i ∈ D, (crt2310Modulus i : ℂ)) *
            ∏ i ∈ D,
              (if toCRT2310 x i = lo i then (1 : ℂ)
                else if toCRT2310 x i = hi i then -1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_exactCRTFrequencies_cuboid
        D lo hi (toCRT2310 x) hdistinct
    _ = ∑ x ∈ A,
          ((∏ i ∈ D, (crt2310Modulus i : ℂ)) *
            (crtCuboidSign D lo hi x : ℂ)) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      rw [← crtCuboidSign_cast D lo hi (toCRT2310 x)]
      simp
    _ = (∏ i ∈ D, (crt2310Modulus i : ℂ)) *
          ∑ x ∈ A, (crtCuboidSign D lo hi x : ℂ) := by
      rw [Finset.mul_sum]
    _ = (supportModulus D : ℂ) *
          (signedFinsetEvaluation A (crtCuboidSign D lo hi) : ℂ) := by
      rw [signedFinsetEvaluation]
      push_cast
      simp [supportModulus]

/-- A cyclotomic divisor at exact CRT support `D` annihilates every
alternating `D`-cuboid.  This is the cuboid-test implication used inside
Lemma 6.1 of the specialized Laba--Marshall argument. -/
theorem signedFinsetEvaluation_crtCuboidSign_eq_zero_of_cyclotomic
    (A : Finset (ZMod 2310)) (D : Finset (Fin 5))
    (lo hi : CRT2310) (hdistinct : ∀ i ∈ D, lo i ≠ hi i)
    (hcyclo : cyclotomic (supportModulus D) ℤ ∣ maskPolynomial 2310 A) :
    signedFinsetEvaluation A (crtCuboidSign D lo hi) = 0 := by
  have hzero : ∀ d ∈ exactCRTFrequencies D,
      fourierSum A (fromCRT2310 d) = 0 := by
    intro d hd
    apply (cyclotomicZero_iff_fourierSum_zero A (fromCRT2310 d)).1
    unfold CyclotomicZero
    rw [frequencyOrder_eq_supportModulus]
    have hs : crt2310Support (fromCRT2310 d) = D := by
      have hdSupport : crtVectorSupport d = D :=
        mem_exactCRTFrequencies.mp hd
      calc
        crt2310Support (fromCRT2310 d) = crtVectorSupport d := by
          unfold crt2310Support crtVectorSupport
          rw [toCRT2310_fromCRT2310]
        _ = D := hdSupport
    simpa [hs] using hcyclo
  have hexpansion := sum_exactCRTFrequencies_cuboid_mul_fourierSum
    A D lo hi hdistinct
  have hlhs :
      (∑ d ∈ exactCRTFrequencies D,
          crtCuboidFourierCoefficient D lo hi d *
            fourierSum A (fromCRT2310 d)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    simp [hzero d hd]
  rw [hlhs] at hexpansion
  have hmod : (supportModulus D : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Finset.prod_pos fun i hi ↦
      Nat.zero_lt_of_ne_zero (NeZero.ne (crt2310Modulus i)))
  have hcast :
      (signedFinsetEvaluation A (crtCuboidSign D lo hi) : ℂ) = 0 :=
    (mul_eq_zero.mp hexpansion.symm).resolve_left hmod
  exact_mod_cast hcast

/-- Difference of two signed fiber evaluations, written as one alternating
axis evaluation. -/
theorem signedLevelEvaluation_sub
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (A : Finset alpha) (sign : alpha → Int) (coord : alpha → beta)
    (b c : beta) (hbc : b ≠ c) :
    signedLevelEvaluation A sign coord b -
        signedLevelEvaluation A sign coord c =
      signedFinsetEvaluation A (fun x ↦
        sign x * (if coord x = b then 1
          else if coord x = c then -1 else 0)) := by
  classical
  rw [signedLevelEvaluation, signedLevelEvaluation,
    signedFinsetEvaluation]
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hcb : c ≠ b := Ne.symm hbc
  by_cases hxb : coord x = b
  · have hxc : coord x ≠ c := fun e ↦ hbc (hxb.symm.trans e)
    simp [hxb, hbc]
  · by_cases hxc : coord x = c
    · simp [hxc, hcb]
    · simp [hxb, hxc]

/-- Adding one fresh CRT axis to a cuboid multiplies its sign by the
alternating sign on that axis. -/
theorem crtCuboidSign_insert
    (D : Finset (Fin 5)) (i : Fin 5) (hiD : i ∉ D)
    (lo hi : CRT2310) (b c : ZMod (crt2310Modulus i))
    (x : ZMod 2310) :
    crtCuboidSign (insert i D) (Function.update lo i b)
        (Function.update hi i c) x =
      (if toCRT2310 x i = b then 1
        else if toCRT2310 x i = c then -1 else 0) *
        crtCuboidSign D lo hi x := by
  classical
  rw [crtCuboidSign, Finset.prod_insert hiD, crtCuboidSign]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hjD
  have hji : j ≠ i := by
    intro e
    subst j
    exact hiD hjD
  simp [Function.update, hji]

/-- The missing forward bridge in Lemma 6.1 of Laba--Marshall, specialized
to square-free modulus `2310`: a divisor `Φ_(m p_i)` makes every signed
`m`-cuboid evaluation constant across the fresh `p_i` coordinate. -/
theorem signedLevelEvaluation_crtCuboid_eq_of_cyclotomic
    (A : Finset (ZMod 2310)) (D : Finset (Fin 5))
    (i : Fin 5) (hiD : i ∉ D) (lo hi : CRT2310)
    (hdistinct : ∀ j ∈ D, lo j ≠ hi j)
    (hcyclo : cyclotomic (supportModulus (insert i D)) ℤ ∣
      maskPolynomial 2310 A)
    (b c : ZMod (crt2310Modulus i)) :
    signedLevelEvaluation A (crtCuboidSign D lo hi)
        (fun x ↦ toCRT2310 x i) b =
      signedLevelEvaluation A (crtCuboidSign D lo hi)
        (fun x ↦ toCRT2310 x i) c := by
  classical
  by_cases hbc : b = c
  · subst c
    rfl
  · have hfullDistinct :
        ∀ j ∈ insert i D,
          Function.update lo i b j ≠ Function.update hi i c j := by
      intro j hj
      rcases Finset.mem_insert.mp hj with (rfl | hjD)
      · simpa using hbc
      · have hji : j ≠ i := by
          intro e
          subst j
          exact hiD hjD
        simpa [Function.update, hji] using hdistinct j hjD
    have hfull :=
      signedFinsetEvaluation_crtCuboidSign_eq_zero_of_cyclotomic
        A (insert i D) (Function.update lo i b)
          (Function.update hi i c) hfullDistinct hcyclo
    have hsub := signedLevelEvaluation_sub A (crtCuboidSign D lo hi)
      (fun x ↦ toCRT2310 x i) b c hbc
    apply sub_eq_zero.mp
    rw [hsub]
    calc
      signedFinsetEvaluation A (fun x ↦
          crtCuboidSign D lo hi x *
            (if toCRT2310 x i = b then 1
              else if toCRT2310 x i = c then -1 else 0)) =
          signedFinsetEvaluation A
            (crtCuboidSign (insert i D) (Function.update lo i b)
              (Function.update hi i c)) := by
        rw [signedFinsetEvaluation, signedFinsetEvaluation]
        apply Finset.sum_congr rfl
        intro x hx
        rw [crtCuboidSign_insert D i hiD lo hi b c x]
        ring
      _ = 0 := hfull

/-- Corollary 6.5 after a particular nonzero base cuboid has been chosen.
All prime-axis divisibilities are now derived from the cyclotomic parent
divisors, rather than accepted as extra hypotheses. -/
theorem labaMarshall_2310_cuboid_of_cyclotomic_parents
    (baseAxes addedAxes : Finset (Fin 5))
    (hdisjoint : Disjoint baseAxes addedAxes)
    (A : Finset (ZMod 2310)) (lo hi : CRT2310)
    (hdistinct : ∀ j ∈ baseAxes, lo j ≠ hi j)
    (hparents : ∀ i ∈ addedAxes,
      cyclotomic (supportModulus (insert i baseAxes)) ℤ ∣
        maskPolynomial 2310 A)
    (hne : signedFinsetEvaluation A
      (crtCuboidSign baseAxes lo hi) ≠ 0) :
    supportModulus addedAxes ≤ A.card := by
  apply labaMarshall_2310_cuboid_of_levelwise_constant
    baseAxes addedAxes A lo hi
  · intro i hiAdded b c
    have hiBase : i ∉ baseAxes := by
      exact fun hiBase ↦
        (Finset.disjoint_left.mp hdisjoint) hiBase hiAdded
    exact signedLevelEvaluation_crtCuboid_eq_of_cyclotomic
      A baseAxes i hiBase lo hi hdistinct (hparents i hiAdded) b c
  · exact hne

/-! ## Producing the nonzero base cuboid -/

theorem standardCoordinateChar_swap (z d : CRT2310) (i : Fin 5) :
    standardCoordinateChar z i (d i) =
      standardCoordinateChar d i (z i) := by
  rw [standardCoordinateChar_apply, standardCoordinateChar_apply]
  congr 3
  exact mul_comm _ _

/-- Reverse one-dimensional Fourier expansion: differences from the zero
level span every nontrivial coordinate character. -/
theorem sum_nonzero_standardCoordinateChar_pointMass
    (z d : CRT2310) (i : Fin 5) (hd : d i ≠ 0) :
    (∑ a ∈ nonzeroCoordinateFrequencies i,
        standardCoordinateChar d i a *
          (if z i = a then (1 : ℂ)
            else if z i = 0 then -1 else 0)) =
      standardCoordinateChar z i (d i) := by
  classical
  by_cases hz : z i = 0
  · calc
      (∑ a ∈ nonzeroCoordinateFrequencies i,
          standardCoordinateChar d i a *
            (if z i = a then (1 : ℂ)
              else if z i = 0 then -1 else 0)) =
          -(∑ a ∈ nonzeroCoordinateFrequencies i,
            standardCoordinateChar d i a) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        have ha0 : a ≠ 0 := mem_nonzeroCoordinateFrequencies.mp ha
        have h0a : (0 : ZMod (crt2310Modulus i)) ≠ a := Ne.symm ha0
        simp [hz, h0a]
      _ = 1 := by
        rw [sum_nonzero_standardCoordinateChar]
        simp [hd]
      _ = standardCoordinateChar z i (d i) := by
        simp [standardCoordinateChar_apply, hz]
  · rw [Finset.sum_eq_single (z i)]
    · simpa [hz] using standardCoordinateChar_swap d z i
    · intro a ha hane
      have hznea : z i ≠ a := Ne.symm hane
      simp [hznea, hz]
    · intro hzmem
      exact (hzmem (mem_nonzeroCoordinateFrequencies.mpr hz)).elim

noncomputable def crtCuboidReverseLocalFactor
    (D : Finset (Fin 5)) (z d : CRT2310) (i : Fin 5)
    (a : ZMod (crt2310Modulus i)) : ℂ :=
  standardCoordinateChar d i a *
    (if i ∈ D then
      (if z i = a then (1 : ℂ)
        else if z i = 0 then -1 else 0)
    else 1)

private theorem pairing_mul_cuboidSign_cast_eq_prod_reverseLocal
    (D : Finset (Fin 5)) (lo z d : CRT2310) :
    standardCRTCharacterPairing lo d *
        (crtCuboidSign D lo 0 (fromCRT2310 z) : ℂ) =
      ∏ i, crtCuboidReverseLocalFactor D z d i (lo i) := by
  classical
  rw [standardCRTCharacterPairing_eq_prod,
    crtCuboidSign_cast D lo 0 z]
  simp only [Pi.zero_apply]
  have hpair :
      (∏ i, standardCoordinateChar lo i (d i)) =
        ∏ i, standardCoordinateChar d i (lo i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact standardCoordinateChar_swap lo d i
  rw [hpair]
  have hsign :
      (∏ i ∈ D,
          (if z i = lo i then (1 : ℂ)
            else if z i = 0 then -1 else 0)) =
        ∏ i, if i ∈ D then
          (if z i = lo i then (1 : ℂ)
            else if z i = 0 then -1 else 0) else 1 := by
    calc
      (∏ i ∈ D,
          (if z i = lo i then (1 : ℂ)
            else if z i = 0 then -1 else 0)) =
          ∏ i ∈ D, if i ∈ D then
            (if z i = lo i then (1 : ℂ)
              else if z i = 0 then -1 else 0) else 1 := by simp
      _ = ∏ i, if i ∈ D then
            (if z i = lo i then (1 : ℂ)
              else if z i = 0 then -1 else 0) else 1 := by
        apply Finset.prod_subset (Finset.subset_univ D)
        intro i hi hiD
        simp [hiD]
  rw [hsign, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rfl

/-- Reverse product Fourier expansion for the cuboid basis based at zero. -/
theorem sum_exactCRTFrequencies_pairing_mul_cuboidSign
    (D : Finset (Fin 5)) (z d : CRT2310)
    (hd : d ∈ exactCRTFrequencies D) :
    (∑ lo ∈ exactCRTFrequencies D,
        standardCRTCharacterPairing lo d *
          (crtCuboidSign D lo 0 (fromCRT2310 z) : ℂ)) =
      standardCRTCharacterPairing z d := by
  classical
  have hdSupport : crtVectorSupport d = D :=
    mem_exactCRTFrequencies.mp hd
  simp_rw [pairing_mul_cuboidSign_cast_eq_prod_reverseLocal]
  rw [exactCRTFrequencies]
  calc
    (∑ lo ∈ Fintype.piFinset (coordinateFrequencySet D),
        ∏ i, crtCuboidReverseLocalFactor D z d i (lo i)) =
        ∏ i, ∑ a ∈ coordinateFrequencySet D i,
          crtCuboidReverseLocalFactor D z d i a := by
      exact (Finset.prod_univ_sum (coordinateFrequencySet D)
        (fun i a ↦ crtCuboidReverseLocalFactor D z d i a)).symm
    _ = ∏ i, standardCoordinateChar z i (d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hiD : i ∈ D
      · have hdi : d i ≠ 0 := by
          rw [← mem_crtVectorSupport, hdSupport]
          exact hiD
        simp only [coordinateFrequencySet, crtCuboidReverseLocalFactor,
          if_pos hiD]
        exact sum_nonzero_standardCoordinateChar_pointMass z d i hdi
      · have hdi : d i = 0 := by
          by_contra hne
          apply hiD
          rw [← hdSupport, mem_crtVectorSupport]
          exact hne
        simp [coordinateFrequencySet, crtCuboidReverseLocalFactor,
          hiD, hdi]
    _ = standardCRTCharacterPairing z d :=
      (standardCRTCharacterPairing_eq_prod z d).symm

/-- Reverse expansion after summing over the finite set `A`. -/
theorem sum_exactCRTFrequencies_pairing_mul_signedCuboid
    (A : Finset (ZMod 2310)) (D : Finset (Fin 5))
    (d : CRT2310) (hd : d ∈ exactCRTFrequencies D) :
    (∑ lo ∈ exactCRTFrequencies D,
        standardCRTCharacterPairing lo d *
          (signedFinsetEvaluation A (crtCuboidSign D lo 0) : ℂ)) =
      fourierSum A (fromCRT2310 d) := by
  classical
  rw [← standardCRTFourierSum_eq_fourierSum]
  simp only [standardCRTFourierSum, signedFinsetEvaluation]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simpa using sum_exactCRTFrequencies_pairing_mul_cuboidSign
    D (toCRT2310 x) d hd

/-- A concrete frequency vector with prescribed exact CRT support. -/
noncomputable def canonicalCRTFrequency (D : Finset (Fin 5)) : CRT2310 :=
  fun i ↦ if i ∈ D then 1 else 0

theorem canonicalCRTFrequency_mem_exact (D : Finset (Fin 5)) :
    canonicalCRTFrequency D ∈ exactCRTFrequencies D := by
  rw [mem_exactCRTFrequencies]
  ext i
  by_cases hi : i ∈ D
  · simp only [mem_crtVectorSupport, canonicalCRTFrequency, hi, if_pos,
      iff_true]
    fin_cases i <;> decide
  · simp [canonicalCRTFrequency, hi]

/-- The converse cuboid test needed in Corollary 6.5: failure of the base
cyclotomic divisor supplies a nonzero alternating base cuboid. -/
theorem exists_nonzero_crtCuboid_of_not_cyclotomic
    (A : Finset (ZMod 2310)) (D : Finset (Fin 5))
    (hnot : ¬ cyclotomic (supportModulus D) ℤ ∣
      maskPolynomial 2310 A) :
    ∃ lo ∈ exactCRTFrequencies D,
      signedFinsetEvaluation A (crtCuboidSign D lo 0) ≠ 0 := by
  classical
  let d : CRT2310 := canonicalCRTFrequency D
  have hd : d ∈ exactCRTFrequencies D :=
    canonicalCRTFrequency_mem_exact D
  have hsupport : crt2310Support (fromCRT2310 d) = D := by
    have hdSupport : crtVectorSupport d = D :=
      mem_exactCRTFrequencies.mp hd
    calc
      crt2310Support (fromCRT2310 d) = crtVectorSupport d := by
        unfold crt2310Support crtVectorSupport
        rw [toCRT2310_fromCRT2310]
      _ = D := hdSupport
  have hfourier : fourierSum A (fromCRT2310 d) ≠ 0 := by
    intro hzero
    apply hnot
    have hcz : CyclotomicZero 2310 A (fromCRT2310 d) :=
      (cyclotomicZero_iff_fourierSum_zero A (fromCRT2310 d)).2 hzero
    unfold CyclotomicZero at hcz
    rw [frequencyOrder_eq_supportModulus, hsupport] at hcz
    exact hcz
  by_contra hexists
  push Not at hexists
  have hsumzero :
      (∑ lo ∈ exactCRTFrequencies D,
          standardCRTCharacterPairing lo d *
            (signedFinsetEvaluation A (crtCuboidSign D lo 0) : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro lo hlo
    simp [hexists lo hlo]
  have hexpansion :=
    sum_exactCRTFrequencies_pairing_mul_signedCuboid A D d hd
  rw [hsumzero] at hexpansion
  exact hfourier hexpansion.symm

/-- Full square-free `ZMod 2310` specialization of Laba--Marshall
Corollary 6.5. -/
theorem labaMarshall_2310_cyclotomic
    (baseAxes addedAxes : Finset (Fin 5))
    (hdisjoint : Disjoint baseAxes addedAxes)
    (A : Finset (ZMod 2310))
    (hparents : ∀ i ∈ addedAxes,
      cyclotomic (supportModulus (insert i baseAxes)) ℤ ∣
        maskPolynomial 2310 A)
    (hbase : ¬ cyclotomic (supportModulus baseAxes) ℤ ∣
      maskPolynomial 2310 A) :
    supportModulus addedAxes ≤ A.card := by
  obtain ⟨lo, hlo, hne⟩ :=
    exists_nonzero_crtCuboid_of_not_cyclotomic A baseAxes hbase
  have hloSupport : crtVectorSupport lo = baseAxes :=
    mem_exactCRTFrequencies.mp hlo
  have hdistinct : ∀ i ∈ baseAxes, lo i ≠ (0 : CRT2310) i := by
    intro i hi
    simpa only [Pi.zero_apply] using
      (show lo i ≠ 0 by
        rw [← mem_crtVectorSupport, hloSupport]
        exact hi)
  exact labaMarshall_2310_cuboid_of_cyclotomic_parents
    baseAxes addedAxes hdisjoint A lo 0 hdistinct hparents hne

/-- Exact-support energy vanishing is the cyclotomic divisor indexed by the
same CRT support.  This local spelling keeps the Laba--Marshall corollary
independent of the later abstract multiaxis specification. -/
theorem supportEnergy_eq_zero_iff_cyclotomicSupport_labaMarshall
    (A : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    supportEnergy A D = 0 ↔
      cyclotomic (supportModulus D) Int ∣ maskPolynomial 2310 A := by
  constructor
  · intro henergy
    have hall :=
      (supportEnergy_eq_zero_iff_cyclotomicZero_fromCRT2310 A D).mp
        henergy
    let d : CRT2310 := canonicalCRTFrequency D
    have hd : d ∈ exactCRTFrequencies D := by
      simpa [d] using canonicalCRTFrequency_mem_exact D
    have hzero := hall d hd
    unfold CyclotomicZero at hzero
    rw [frequencyOrder_fromCRT2310_eq_supportModulus,
      mem_exactCRTFrequencies.mp hd] at hzero
    exact hzero
  · intro hdiv
    rw [supportEnergy_eq_zero_iff_cyclotomicZero_fromCRT2310]
    intro d hd
    unfold CyclotomicZero
    rw [frequencyOrder_fromCRT2310_eq_supportModulus,
      mem_exactCRTFrequencies.mp hd]
    exact hdiv

/-- Energy-form Laba--Marshall clause used directly by the finite multiaxis
constraints: vanishing on every one-axis enlargement forces vanishing on the
base support whenever the added prime product is larger than the set. -/
theorem supportEnergy_base_eq_zero_of_labaMarshall
    (A : Finset (ZMod 2310)) (baseAxes addedAxes : Finset (Fin 5))
    (hdisjoint : Disjoint baseAxes addedAxes)
    (hlarge : A.card < supportModulus addedAxes)
    (hparents : ∀ i ∈ addedAxes,
      supportEnergy A (insert i baseAxes) = 0) :
    supportEnergy A baseAxes = 0 := by
  by_contra hbaseEnergy
  have hbound : supportModulus addedAxes ≤ A.card := by
    apply labaMarshall_2310_cyclotomic baseAxes addedAxes hdisjoint A
    · intro i hi
      exact
        (supportEnergy_eq_zero_iff_cyclotomicSupport_labaMarshall
          A (insert i baseAxes)).mp (hparents i hi)
    · intro hbaseDivisor
      apply hbaseEnergy
      exact
        (supportEnergy_eq_zero_iff_cyclotomicSupport_labaMarshall
          A baseAxes).mpr hbaseDivisor
  exact (Nat.not_lt_of_ge hbound) hlarge

end Fuglede
