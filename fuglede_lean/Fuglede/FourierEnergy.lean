import Fuglede.CRT2310
import Fuglede.InnerDistribution
import Fuglede.SpectralFourier
import Mathlib.Algebra.Star.BigOperators
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Exact-support Krawtchouk coefficients and local character sums

This file defines the signed coefficient attached to two coordinate supports
`D, T \subseteq Fin 5`, together with the corresponding integer transform of
the inner distribution.  The key analytic input is proved one coordinate at
a time: summing a primitive additive character over the nonzero frequencies
of a coordinate gives `p - 1` at zero and `-1` away from zero.

The resulting product identity is the local kernel needed for the full
Fourier-energy formula.  No numerical approximation to a root of unity is
used.
-/

namespace Fuglede

open scoped BigOperators ComplexConjugate

/-- The exact-support Krawtchouk coefficient.  A coordinate in `D \cap T`
contributes `-1`, while a coordinate in `D \ T` contributes `p_i - 1`. -/
noncomputable def krawtchoukCoeff
    (D T : Finset (Fin 5)) : ℤ :=
  (-1 : ℤ) ^ (D ∩ T).card *
    ∏ i ∈ D \ T, ((crt2310Modulus i : ℤ) - 1)

/-- The signed Krawtchouk transform of the exact inner distribution. -/
noncomputable def supportEnergy
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) : ℤ :=
  ∑ T : Finset (Fin 5),
    krawtchoukCoeff D T * innerDistributionInt X T

@[simp]
theorem krawtchoukCoeff_empty_left (T : Finset (Fin 5)) :
    krawtchoukCoeff ∅ T = 1 := by
  simp [krawtchoukCoeff]

@[simp]
theorem krawtchoukCoeff_empty_right (D : Finset (Fin 5)) :
    krawtchoukCoeff D ∅ =
      ∏ i ∈ D, ((crt2310Modulus i : ℤ) - 1) := by
  simp [krawtchoukCoeff]

@[simp]
theorem supportEnergy_empty (X : Finset (ZMod 2310)) :
    supportEnergy X ∅ = (X.card : ℤ) ^ 2 := by
  rw [supportEnergy]
  simp only [krawtchoukCoeff_empty_left, one_mul, innerDistributionInt]
  exact_mod_cast sum_innerDistribution X

/-- Frequencies which are nonzero in one CRT coordinate. -/
noncomputable def nonzeroCoordinateFrequencies (i : Fin 5) :
    Finset (ZMod (crt2310Modulus i)) :=
  Finset.univ.erase 0

@[simp]
theorem mem_nonzeroCoordinateFrequencies {i : Fin 5}
    {d : ZMod (crt2310Modulus i)} :
    d ∈ nonzeroCoordinateFrequencies i ↔ d ≠ 0 := by
  simp [nonzeroCoordinateFrequencies]

/-- The local character sum over the nonzero frequencies of one coordinate.
It is `p_i - 1` when the spatial difference is zero and `-1` otherwise. -/
theorem sum_nonzero_stdAddChar_mul (i : Fin 5)
    (z : ZMod (crt2310Modulus i)) :
    ∑ d ∈ nonzeroCoordinateFrequencies i, ZMod.stdAddChar (d * z) =
      if z = 0 then ((crt2310Modulus i : ℤ) - 1 : ℂ) else -1 := by
  classical
  by_cases hz : z = 0
  · subst z
    have hp : 1 ≤ crt2310Modulus i :=
      Nat.one_le_iff_ne_zero.mpr (NeZero.ne (crt2310Modulus i))
    simp [nonzeroCoordinateFrequencies, ZMod.card, hp, Nat.cast_sub]
  · rw [if_neg hz]
    have hfull :
        ∑ d : ZMod (crt2310Modulus i), ZMod.stdAddChar (d * z) = 0 := by
      have hsum := AddChar.sum_mulShift z (ZMod.isPrimitive_stdAddChar
        (crt2310Modulus i))
      rw [if_neg hz] at hsum
      simpa [mul_comm] using hsum
    have hsplit :
        ∑ d : ZMod (crt2310Modulus i), ZMod.stdAddChar (d * z) =
          ZMod.stdAddChar (0 * z) +
            ∑ d ∈ nonzeroCoordinateFrequencies i,
              ZMod.stdAddChar (d * z) := by
      rw [nonzeroCoordinateFrequencies]
      simpa [add_comm] using (Finset.sum_erase_add Finset.univ _
        (Finset.mem_univ (0 : ZMod (crt2310Modulus i)))).symm
    rw [hfull] at hsplit
    simpa using eq_neg_of_add_eq_zero_right hsplit.symm

/-- Support of a vector already written in CRT coordinates. -/
noncomputable def crtVectorSupport (z : CRT2310) : Finset (Fin 5) :=
  Finset.univ.filter fun i ↦ z i ≠ 0

@[simp]
theorem mem_crtVectorSupport {z : CRT2310} {i : Fin 5} :
    i ∈ crtVectorSupport z ↔ z i ≠ 0 := by
  classical
  simp [crtVectorSupport]

/-- Product of the five local character sums for an exact frequency support
`D`.  Coordinates outside `D` contribute the neutral factor `1`. -/
noncomputable def localCharacterKernel
    (D : Finset (Fin 5)) (z : CRT2310) : ℂ :=
  ∏ i ∈ D,
    ∑ d ∈ nonzeroCoordinateFrequencies i, ZMod.stdAddChar (d * z i)

private theorem local_product_eq_closed
    (m : Fin 5 → ℤ) (D T : Finset (Fin 5)) :
    (∏ i ∈ D, if i ∈ T then (-1 : ℤ) else m i) =
      (-1 : ℤ) ^ (D ∩ T).card * ∏ i ∈ D \ T, m i := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a D ha ih =>
      by_cases hT : a ∈ T
      · have hdiff : insert a D \ T = D \ T := by
          ext i
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hi | hiD, hiT⟩
            · subst i
              exact (hiT hT).elim
            · exact ⟨hiD, hiT⟩
          · rintro ⟨hiD, hiT⟩
            exact ⟨Or.inr hiD, hiT⟩
        simp [ha, hT, ih, hdiff, pow_succ]
      · have hdiff : insert a D \ T = insert a (D \ T) := by
          ext i
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨hi | hiD, hiT⟩
            · exact Or.inl hi
            · exact Or.inr ⟨hiD, hiT⟩
          · rintro (hi | ⟨hiD, hiT⟩)
            · subst i
              exact ⟨Or.inl rfl, hT⟩
            · exact ⟨Or.inr hiD, hiT⟩
        simp [ha, hT, ih, hdiff]
        ring

/-- Equivalent coordinatewise product form of `krawtchoukCoeff`. -/
theorem krawtchoukCoeff_eq_prod_local (D T : Finset (Fin 5)) :
    krawtchoukCoeff D T =
      ∏ i ∈ D,
        if i ∈ T then (-1 : ℤ) else (crt2310Modulus i : ℤ) - 1 := by
  classical
  rw [krawtchoukCoeff]
  exact (local_product_eq_closed
    (fun i ↦ (crt2310Modulus i : ℤ) - 1) D T).symm

/-- The product of the exact local character sums depends only on the
support of `z`, and is exactly the signed Krawtchouk coefficient. -/
theorem localCharacterKernel_eq_krawtchoukCoeff
    (D : Finset (Fin 5)) (z : CRT2310) :
    localCharacterKernel D z =
      (krawtchoukCoeff D (crtVectorSupport z) : ℂ) := by
  classical
  rw [localCharacterKernel, krawtchoukCoeff_eq_prod_local]
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  rw [sum_nonzero_stdAddChar_mul]
  by_cases hz : z i = 0
  · simp [hz]
  · simp [hz]

/-- Pair-expanded version of the signed inner-distribution transform. -/
noncomputable def pairKernelSum
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) : ℤ :=
  ∑ p ∈ X ×ˢ X, krawtchoukCoeff D (differenceSupport p.1 p.2)

/-- Grouping ordered pairs by their exact difference support recovers the
inner-distribution definition of `supportEnergy`. -/
theorem supportEnergy_eq_pairKernelSum
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    supportEnergy X D = pairKernelSum X D := by
  classical
  rw [supportEnergy, pairKernelSum]
  simp only [innerDistributionInt, innerDistribution]
  calc
    (∑ T : Finset (Fin 5),
        krawtchoukCoeff D T *
          (((X ×ˢ X).filter fun p ↦ differenceSupport p.1 p.2 = T).card : ℤ)) =
        ∑ T : Finset (Fin 5),
          ∑ p ∈ (X ×ˢ X).filter
              (fun p ↦ differenceSupport p.1 p.2 = T),
            krawtchoukCoeff D T := by
      apply Finset.sum_congr rfl
      intro T hT
      simp [mul_comm]
    _ = ∑ p ∈ X ×ˢ X,
          krawtchoukCoeff D (differenceSupport p.1 p.2) := by
      let g : ZMod 2310 × ZMod 2310 → Finset (Fin 5) :=
        fun p ↦ differenceSupport p.1 p.2
      let f : ZMod 2310 × ZMod 2310 → ℤ :=
        fun p ↦ krawtchoukCoeff D (g p)
      have hfiber :
          (∑ T : Finset (Fin 5),
              ∑ p ∈ (X ×ˢ X).filter (fun p ↦ g p = T), f p) =
            ∑ p ∈ X ×ˢ X, f p := by
        simpa using Finset.sum_fiberwise_eq_sum_filter
          (X ×ˢ X) (Finset.univ : Finset (Finset (Fin 5))) g f
      rw [← hfiber]
      apply Finset.sum_congr rfl
      intro T hT
      apply Finset.sum_congr rfl
      intro p hp
      have hsupport : g p = T := (Finset.mem_filter.mp hp).2
      simp only [f]
      rw [hsupport]

theorem crtVectorSupport_toCRT_sub (x y : ZMod 2310) :
    crtVectorSupport (toCRT2310 (x - y)) = differenceSupport x y := by
  rfl

/-- Fully expanded exact character kernel.  This is the combinatorial side
of the Fourier-energy identity before the finite frequency sums are
reassembled into squared Fourier coefficients. -/
theorem supportEnergy_cast_eq_sum_localCharacterKernel
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    (supportEnergy X D : ℂ) =
      ∑ p ∈ X ×ˢ X,
        localCharacterKernel D (toCRT2310 (p.1 - p.2)) := by
  rw [supportEnergy_eq_pairKernelSum, pairKernelSum]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  rw [localCharacterKernel_eq_krawtchoukCoeff,
    crtVectorSupport_toCRT_sub]

/-- Allowed values of one coordinate for a frequency having exact support
`D`: nonzero on `D` and zero off `D`. -/
noncomputable def coordinateFrequencySet
    (D : Finset (Fin 5)) (i : Fin 5) :
    Finset (ZMod (crt2310Modulus i)) :=
  if i ∈ D then nonzeroCoordinateFrequencies i else {0}

/-- All CRT frequency vectors with exact coordinate support `D`. -/
noncomputable def exactCRTFrequencies (D : Finset (Fin 5)) :
    Finset CRT2310 :=
  Fintype.piFinset (coordinateFrequencySet D)

@[simp]
theorem mem_exactCRTFrequencies {D : Finset (Fin 5)} {d : CRT2310} :
    d ∈ exactCRTFrequencies D ↔ crtVectorSupport d = D := by
  classical
  rw [exactCRTFrequencies, Fintype.mem_piFinset]
  constructor
  · intro hd
    ext i
    by_cases hi : i ∈ D
    · have hdi := hd i
      simp [coordinateFrequencySet, hi] at hdi
      simp [hi, hdi]
    · have hdi := hd i
      simp [coordinateFrequencySet, hi] at hdi
      simp [hi, hdi]
  · intro hs i
    by_cases hi : i ∈ D
    · have hdi : d i ≠ 0 := by
        rw [← mem_crtVectorSupport, hs]
        exact hi
      simp [coordinateFrequencySet, hi, hdi]
    · have hdi : d i = 0 := by
        by_contra hne
        apply hi
        rw [← hs, mem_crtVectorSupport]
        exact hne
      simp [coordinateFrequencySet, hi, hdi]

/-- The product character pairing on the five CRT coordinate groups. -/
noncomputable def crtCharacterPairing (z d : CRT2310) : ℂ :=
  ∏ i, ZMod.stdAddChar (d i * z i)

/-- Exact-support character orthogonality, assembled from the five local
coordinate sums. -/
theorem sum_exactCRTFrequencies_crtCharacterPairing
    (D : Finset (Fin 5)) (z : CRT2310) :
    ∑ d ∈ exactCRTFrequencies D, crtCharacterPairing z d =
      localCharacterKernel D z := by
  classical
  simp only [exactCRTFrequencies, crtCharacterPairing]
  calc
    (∑ d ∈ Fintype.piFinset (coordinateFrequencySet D),
        ∏ i, ZMod.stdAddChar (d i * z i)) =
        ∏ i, ∑ a ∈ coordinateFrequencySet D i,
          ZMod.stdAddChar (a * z i) := by
      exact (Finset.prod_univ_sum (coordinateFrequencySet D)
        (fun i a ↦ ZMod.stdAddChar (a * z i))).symm
    _ = localCharacterKernel D z := by
      rw [localCharacterKernel]
      calc
        (∏ i, ∑ a ∈ coordinateFrequencySet D i,
            ZMod.stdAddChar (a * z i)) =
            ∏ i ∈ D, ∑ a ∈ coordinateFrequencySet D i,
              ZMod.stdAddChar (a * z i) := by
          symm
          apply Finset.prod_subset (Finset.subset_univ D)
          intro i hiuniv hiD
          simp [coordinateFrequencySet, hiD]
        _ = ∏ i ∈ D,
            ∑ a ∈ nonzeroCoordinateFrequencies i,
              ZMod.stdAddChar (a * z i) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [coordinateFrequencySet, hi]

/-- Multiplying one product character by the conjugate of another evaluates
the same character on their difference. -/
theorem crtCharacterPairing_mul_star
    (x y d : CRT2310) :
    crtCharacterPairing x d * star (crtCharacterPairing y d) =
      crtCharacterPairing (x - y) d := by
  classical
  simp only [crtCharacterPairing, star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [star_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [Pi.sub_apply]
  ring

/-- Fourier coefficient for the canonical product character in CRT
coordinates. -/
noncomputable def crtFourierSum
    (X : Finset (ZMod 2310)) (d : CRT2310) : ℂ :=
  ∑ x ∈ X, crtCharacterPairing (toCRT2310 x) d

/-- Complex spelling of the exact-support energy; each summand is in fact a
nonnegative real number. -/
noncomputable def crtSupportEnergyComplex
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) : ℂ :=
  ∑ d ∈ exactCRTFrequencies D,
    crtFourierSum X d * star (crtFourierSum X d)

theorem crtFourierSum_mul_star
    (X : Finset (ZMod 2310)) (d : CRT2310) :
    crtFourierSum X d * star (crtFourierSum X d) =
      ∑ p ∈ X ×ˢ X,
        crtCharacterPairing (toCRT2310 (p.1 - p.2)) d := by
  classical
  simp only [crtFourierSum, star_sum]
  rw [Finset.sum_mul_sum]
  calc
    (∑ x ∈ X, ∑ y ∈ X,
        crtCharacterPairing (toCRT2310 x) d *
          star (crtCharacterPairing (toCRT2310 y) d)) =
        ∑ p ∈ X ×ˢ X,
          crtCharacterPairing (toCRT2310 p.1) d *
            star (crtCharacterPairing (toCRT2310 p.2) d) := by
      exact (Finset.sum_product X X (fun p ↦
        crtCharacterPairing (toCRT2310 p.1) d *
          star (crtCharacterPairing (toCRT2310 p.2) d))).symm
    _ = ∑ p ∈ X ×ˢ X,
        crtCharacterPairing (toCRT2310 (p.1 - p.2)) d := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [crtCharacterPairing_mul_star, ← toCRT2310_sub]

/-- The signed inner-distribution transform is exactly the sum of squared
canonical CRT Fourier coefficients with frequency support `D`. -/
theorem crtSupportEnergyComplex_eq_supportEnergy
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    crtSupportEnergyComplex X D = (supportEnergy X D : ℂ) := by
  rw [crtSupportEnergyComplex]
  simp_rw [crtFourierSum_mul_star]
  calc
    (∑ d ∈ exactCRTFrequencies D,
        ∑ p ∈ X ×ˢ X,
          crtCharacterPairing (toCRT2310 (p.1 - p.2)) d) =
        ∑ p ∈ X ×ˢ X,
          ∑ d ∈ exactCRTFrequencies D,
            crtCharacterPairing (toCRT2310 (p.1 - p.2)) d := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ X ×ˢ X,
          localCharacterKernel D (toCRT2310 (p.1 - p.2)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sum_exactCRTFrequencies_crtCharacterPairing D _
    _ = (supportEnergy X D : ℂ) := by
      exact (supportEnergy_cast_eq_sum_localCharacterKernel X D).symm

/-- The real-valued exact-support Fourier energy. -/
noncomputable def crtSupportEnergy
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) : ℝ :=
  ∑ d ∈ exactCRTFrequencies D, Complex.normSq (crtFourierSum X d)

theorem crtSupportEnergyComplex_eq_coe
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    crtSupportEnergyComplex X D = (crtSupportEnergy X D : ℂ) := by
  classical
  rw [crtSupportEnergyComplex, crtSupportEnergy]
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_comm]
  exact (Complex.normSq_eq_conj_mul_self (z := crtFourierSum X d)).symm

/-- Real form of the exact energy identity. -/
theorem supportEnergy_cast_real_eq_crtSupportEnergy
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    (supportEnergy X D : ℝ) = crtSupportEnergy X D := by
  have hcomplex : (crtSupportEnergy X D : ℂ) =
      (supportEnergy X D : ℂ) := by
    rw [← crtSupportEnergyComplex_eq_coe]
    exact crtSupportEnergyComplex_eq_supportEnergy X D
  have hre := congrArg Complex.re hcomplex
  simpa using hre.symm

/-- The Krawtchouk transform is nonnegative because it is a finite sum of
complex squared norms. -/
theorem supportEnergy_nonneg
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    0 ≤ supportEnergy X D := by
  have hreal : (0 : ℝ) ≤ (supportEnergy X D : ℝ) := by
    rw [supportEnergy_cast_real_eq_crtSupportEnergy, crtSupportEnergy]
    exact Finset.sum_nonneg fun d hd ↦ Complex.normSq_nonneg _
  exact_mod_cast hreal

/-- Vanishing of an exact-support energy is equivalent to simultaneous
vanishing of every canonical CRT Fourier coefficient on that support. -/
theorem supportEnergy_eq_zero_iff
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    supportEnergy X D = 0 ↔
      ∀ d ∈ exactCRTFrequencies D, crtFourierSum X d = 0 := by
  constructor
  · intro hzero
    have hreal : crtSupportEnergy X D = 0 := by
      rw [← supportEnergy_cast_real_eq_crtSupportEnergy, hzero]
      norm_num
    have hall : ∀ d ∈ exactCRTFrequencies D,
        Complex.normSq (crtFourierSum X d) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun d hd ↦ Complex.normSq_nonneg (crtFourierSum X d))).mp
      exact hreal
    intro d hd
    exact Complex.normSq_eq_zero.mp (hall d hd)
  · intro hall
    have hreal : crtSupportEnergy X D = 0 := by
      rw [crtSupportEnergy]
      apply Finset.sum_eq_zero
      intro d hd
      simp [hall d hd]
    have hcast : (supportEnergy X D : ℝ) = 0 := by
      rw [supportEnergy_cast_real_eq_crtSupportEnergy, hreal]
    exact_mod_cast hcast

/-! ## Bridge to the standard character of `ZMod 2310` -/

/-- Include one CRT coordinate and reconstruct the corresponding residue
modulo `2310`. -/
noncomputable def crtCoordinateEmbedding (i : Fin 5) :
    ZMod (crt2310Modulus i) →+ ZMod 2310 :=
  crt2310AddEquiv.symm.toAddMonoidHom.comp
    (AddMonoidHom.single (fun j ↦ ZMod (crt2310Modulus j)) i)

@[simp]
theorem fromCRT2310_zero : fromCRT2310 (0 : CRT2310) = 0 :=
  crt2310AddEquiv.symm.map_zero

@[simp]
theorem crtCoordinateEmbedding_apply (i : Fin 5)
    (a : ZMod (crt2310Modulus i)) :
    crtCoordinateEmbedding i a = fromCRT2310 (Pi.single i a) := by
  rfl

/-- Restriction of the standard character of `ZMod 2310` to coordinate `i`,
after multiplication by the spatial coordinate `z i`. -/
noncomputable def standardCoordinateChar (z : CRT2310) (i : Fin 5) :
    AddChar (ZMod (crt2310Modulus i)) ℂ :=
  (ZMod.stdAddChar (N := 2310)).compAddMonoidHom
    ((crtCoordinateEmbedding i).comp (AddMonoidHom.mulRight (z i)))

@[simp]
theorem standardCoordinateChar_apply (z : CRT2310) (i : Fin 5)
    (a : ZMod (crt2310Modulus i)) :
    standardCoordinateChar z i a =
      ZMod.stdAddChar (fromCRT2310 (Pi.single i (a * z i))) := by
  rfl

theorem standardCoordinateChar_eq_one_iff (z : CRT2310) (i : Fin 5) :
    standardCoordinateChar z i = 1 ↔ z i = 0 := by
  constructor
  · intro hchar
    have hvalue := congrArg
      (fun ψ : AddChar (ZMod (crt2310Modulus i)) ℂ ↦ ψ 1) hchar
    have hstd :
        ZMod.stdAddChar (fromCRT2310 (Pi.single i (z i))) =
          ZMod.stdAddChar (0 : ZMod 2310) := by
      simpa using hvalue
    have hfrom : fromCRT2310 (Pi.single i (z i)) = 0 :=
      ZMod.injective_stdAddChar hstd
    have hcoords := congrArg toCRT2310 hfrom
    have hsingle : Pi.single i (z i) = (0 : CRT2310) := by
      simpa using hcoords
    have hi := congrFun hsingle i
    simpa using hi
  · intro hz
    apply AddChar.ext
    intro a
    rw [standardCoordinateChar_apply, hz, mul_zero]
    have hfromZero : fromCRT2310 (0 : CRT2310) = 0 :=
      crt2310AddEquiv.symm.map_zero
    simpa [hfromZero]

/-- The standard `ZMod 2310` character has the same local nonzero-frequency
sum as the canonical coordinate character. -/
theorem sum_nonzero_standardCoordinateChar (z : CRT2310) (i : Fin 5) :
    ∑ a ∈ nonzeroCoordinateFrequencies i, standardCoordinateChar z i a =
      if z i = 0 then ((crt2310Modulus i : ℤ) - 1 : ℂ) else -1 := by
  classical
  by_cases hz : z i = 0
  · rw [if_pos hz]
    have hchar : standardCoordinateChar z i = 1 :=
      (standardCoordinateChar_eq_one_iff z i).2 hz
    rw [hchar]
    have hp : 1 ≤ crt2310Modulus i :=
      Nat.one_le_iff_ne_zero.mpr (NeZero.ne (crt2310Modulus i))
    simp [nonzeroCoordinateFrequencies, ZMod.card, hp, Nat.cast_sub]
  · rw [if_neg hz]
    have hne : standardCoordinateChar z i ≠ 1 :=
      (standardCoordinateChar_eq_one_iff z i).not.mpr hz
    have hfull :
        ∑ a : ZMod (crt2310Modulus i), standardCoordinateChar z i a = 0 :=
      AddChar.sum_eq_zero_of_ne_one hne
    have hsplit :
        ∑ a : ZMod (crt2310Modulus i), standardCoordinateChar z i a =
          standardCoordinateChar z i 0 +
            ∑ a ∈ nonzeroCoordinateFrequencies i,
              standardCoordinateChar z i a := by
      change
        (∑ a : ZMod (crt2310Modulus i), standardCoordinateChar z i a) =
          standardCoordinateChar z i 0 +
            ∑ a ∈ Finset.univ.erase 0, standardCoordinateChar z i a
      calc
        (∑ a : ZMod (crt2310Modulus i), standardCoordinateChar z i a) =
            (∑ a ∈ Finset.univ.erase 0, standardCoordinateChar z i a) +
              standardCoordinateChar z i 0 :=
          (Finset.sum_erase_add Finset.univ
            (fun a ↦ standardCoordinateChar z i a)
            (Finset.mem_univ (0 : ZMod (crt2310Modulus i)))).symm
        _ = standardCoordinateChar z i 0 +
              ∑ a ∈ Finset.univ.erase 0, standardCoordinateChar z i a :=
          add_comm _ _
    rw [hfull] at hsplit
    simpa using eq_neg_of_add_eq_zero_right hsplit.symm

/-- The standard character pairing transported through the CRT
equivalence. -/
noncomputable def standardCRTCharacterPairing (z d : CRT2310) : ℂ :=
  ZMod.stdAddChar (fromCRT2310 (d * z))

/-- A character on the CRT product factors as the product of its five
coordinate restrictions. -/
theorem standardCRTCharacterPairing_eq_prod
    (z d : CRT2310) :
    standardCRTCharacterPairing z d =
      ∏ i, standardCoordinateChar z i (d i) := by
  classical
  have hdecomp :
      (∑ i, Pi.single i (d i * z i)) = d * z := by
    funext i
    change (∑ j, Pi.single j (d j * z j) i) = d i * z i
    exact Fintype.sum_pi_single i (fun j ↦ d j * z j)
  have hfromSum :
      fromCRT2310 (∑ i, Pi.single i (d i * z i)) =
        ∑ i, fromCRT2310 (Pi.single i (d i * z i)) := by
    change crt2310AddEquiv.symm (∑ i, Pi.single i (d i * z i)) = _
    exact map_sum crt2310AddEquiv.symm
      (fun i ↦ Pi.single i (d i * z i)) Finset.univ
  have hcharSum (s : Finset (Fin 5)) :
      ZMod.stdAddChar
          (∑ i ∈ s, fromCRT2310 (Pi.single i (d i * z i))) =
        ∏ i ∈ s,
          ZMod.stdAddChar (fromCRT2310 (Pi.single i (d i * z i))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha,
          AddChar.map_add_eq_mul, ih]
  rw [standardCRTCharacterPairing, ← hdecomp, hfromSum]
  simpa [standardCoordinateChar_apply] using
    hcharSum (Finset.univ : Finset (Fin 5))

/-- Exact-support orthogonality for the character transported from the
standard character of `ZMod 2310`. -/
theorem sum_exactCRTFrequencies_standardCRTCharacterPairing
    (D : Finset (Fin 5)) (z : CRT2310) :
    ∑ d ∈ exactCRTFrequencies D, standardCRTCharacterPairing z d =
      localCharacterKernel D z := by
  classical
  simp only [exactCRTFrequencies, standardCRTCharacterPairing_eq_prod]
  calc
    (∑ d ∈ Fintype.piFinset (coordinateFrequencySet D),
        ∏ i, standardCoordinateChar z i (d i)) =
        ∏ i, ∑ a ∈ coordinateFrequencySet D i,
          standardCoordinateChar z i a := by
      exact (Finset.prod_univ_sum (coordinateFrequencySet D)
        (fun i a ↦ standardCoordinateChar z i a)).symm
    _ = ∏ i ∈ D,
          ∑ a ∈ nonzeroCoordinateFrequencies i,
            standardCoordinateChar z i a := by
      symm
      calc
        (∏ i ∈ D,
            ∑ a ∈ nonzeroCoordinateFrequencies i,
              standardCoordinateChar z i a) =
            ∏ i ∈ D,
              ∑ a ∈ coordinateFrequencySet D i,
                standardCoordinateChar z i a := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [coordinateFrequencySet, hi]
        _ = ∏ i,
              ∑ a ∈ coordinateFrequencySet D i,
                standardCoordinateChar z i a := by
          apply Finset.prod_subset (Finset.subset_univ D)
          intro i hiuniv hiD
          simp [coordinateFrequencySet, hiD]
    _ = localCharacterKernel D z := by
      rw [localCharacterKernel]
      apply Finset.prod_congr rfl
      intro i hi
      rw [sum_nonzero_standardCoordinateChar,
        sum_nonzero_stdAddChar_mul]

@[simp]
theorem fromCRT2310_mul (x y : CRT2310) :
    fromCRT2310 (x * y) = fromCRT2310 x * fromCRT2310 y := by
  change crt2310RingEquiv.symm (x * y) =
    crt2310RingEquiv.symm x * crt2310RingEquiv.symm y
  exact crt2310RingEquiv.symm.map_mul x y

theorem standardCRTCharacterPairing_mul_star
    (x y d : CRT2310) :
    standardCRTCharacterPairing x d *
        star (standardCRTCharacterPairing y d) =
      standardCRTCharacterPairing (x - y) d := by
  rw [standardCRTCharacterPairing, standardCRTCharacterPairing,
    standardCRTCharacterPairing, star_stdAddChar,
    ← AddChar.map_add_eq_mul]
  congr 1
  rw [← sub_eq_add_neg]
  change fromCRT2310 (d * x) - fromCRT2310 (d * y) =
    fromCRT2310 (d * (x - y))
  unfold fromCRT2310
  rw [← crt2310AddEquiv.symm.map_sub]
  congr 1
  ring

/-- Fourier coefficient obtained by transporting the standard character of
`ZMod 2310` into CRT frequency coordinates. -/
noncomputable def standardCRTFourierSum
    (X : Finset (ZMod 2310)) (d : CRT2310) : ℂ :=
  ∑ x ∈ X, standardCRTCharacterPairing (toCRT2310 x) d

/-- The transported coefficient is literally the existing `fourierSum` at
the reconstructed frequency. -/
theorem standardCRTFourierSum_eq_fourierSum
    (X : Finset (ZMod 2310)) (d : CRT2310) :
    standardCRTFourierSum X d = fourierSum X (fromCRT2310 d) := by
  calc
    standardCRTFourierSum X d =
        ∑ x ∈ X, ZMod.stdAddChar (x * fromCRT2310 d) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [standardCRTFourierSum, standardCRTCharacterPairing, mul_comm]
    _ = ∑ x : ↥X, ZMod.stdAddChar (x.1 * fromCRT2310 d) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach X
          (fun x ↦ ZMod.stdAddChar (x * fromCRT2310 d))).symm
    _ = fourierSum X (fromCRT2310 d) := rfl

noncomputable def standardCRTSupportEnergyComplex
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) : ℂ :=
  ∑ d ∈ exactCRTFrequencies D,
    standardCRTFourierSum X d * star (standardCRTFourierSum X d)

theorem standardCRTFourierSum_mul_star
    (X : Finset (ZMod 2310)) (d : CRT2310) :
    standardCRTFourierSum X d * star (standardCRTFourierSum X d) =
      ∑ p ∈ X ×ˢ X,
        standardCRTCharacterPairing (toCRT2310 (p.1 - p.2)) d := by
  classical
  simp only [standardCRTFourierSum, star_sum]
  rw [Finset.sum_mul_sum]
  calc
    (∑ x ∈ X, ∑ y ∈ X,
        standardCRTCharacterPairing (toCRT2310 x) d *
          star (standardCRTCharacterPairing (toCRT2310 y) d)) =
        ∑ p ∈ X ×ˢ X,
          standardCRTCharacterPairing (toCRT2310 p.1) d *
            star (standardCRTCharacterPairing (toCRT2310 p.2) d) := by
      exact (Finset.sum_product X X (fun p ↦
        standardCRTCharacterPairing (toCRT2310 p.1) d *
          star (standardCRTCharacterPairing (toCRT2310 p.2) d))).symm
    _ = ∑ p ∈ X ×ˢ X,
        standardCRTCharacterPairing (toCRT2310 (p.1 - p.2)) d := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [standardCRTCharacterPairing_mul_star, ← toCRT2310_sub]

/-- Exact-support energy identity using the standard character, hence the
project's original `fourierSum`. -/
theorem standardCRTSupportEnergyComplex_eq_supportEnergy
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    standardCRTSupportEnergyComplex X D = (supportEnergy X D : ℂ) := by
  rw [standardCRTSupportEnergyComplex]
  simp_rw [standardCRTFourierSum_mul_star]
  calc
    (∑ d ∈ exactCRTFrequencies D,
        ∑ p ∈ X ×ˢ X,
          standardCRTCharacterPairing (toCRT2310 (p.1 - p.2)) d) =
        ∑ p ∈ X ×ˢ X,
          ∑ d ∈ exactCRTFrequencies D,
            standardCRTCharacterPairing (toCRT2310 (p.1 - p.2)) d := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ X ×ˢ X,
          localCharacterKernel D (toCRT2310 (p.1 - p.2)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sum_exactCRTFrequencies_standardCRTCharacterPairing D _
    _ = (supportEnergy X D : ℂ) := by
      exact (supportEnergy_cast_eq_sum_localCharacterKernel X D).symm

/-- Literal real-valued formulation requested for the Fuglede bridge:
`q_X(D)` is the sum of `‖fourierSum X d‖²` over all frequencies whose CRT
support is exactly `D` (parametrized bijectively by `fromCRT2310`). -/
theorem supportEnergy_cast_real_eq_sum_normSq_fourierSum
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    (supportEnergy X D : ℝ) =
      ∑ d ∈ exactCRTFrequencies D,
        Complex.normSq (fourierSum X (fromCRT2310 d)) := by
  have hcomplex :
      (∑ d ∈ exactCRTFrequencies D,
          (Complex.normSq (fourierSum X (fromCRT2310 d)) : ℂ)) =
        (supportEnergy X D : ℂ) := by
    rw [← standardCRTSupportEnergyComplex_eq_supportEnergy X D]
    rw [standardCRTSupportEnergyComplex]
    apply Finset.sum_congr rfl
    intro d hd
    rw [standardCRTFourierSum_eq_fourierSum, mul_comm]
    exact Complex.normSq_eq_conj_mul_self
      (z := fourierSum X (fromCRT2310 d))
  have hre := congrArg Complex.re hcomplex
  push_cast at hre
  simpa using hre.symm

end Fuglede
