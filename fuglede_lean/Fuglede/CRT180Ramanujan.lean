import Fuglede.CRT180
import Fuglede.ExactOrderEnergy
import Fuglede.Z180ExactOrderTransform

/-!
# The Ramanujan identity at modulus 180

This file removes `Z180RamanujanIdentity` as a trust boundary.  The proof
uses the prime-power CRT decomposition `180 = 4 * 9 * 5`, character
orthogonality on the three local factors, and an exact grouping of ordered
pairs by the additive order of their difference.
-/

namespace Fuglede

open scoped BigOperators ComplexConjugate

/-! ## The standard character in CRT coordinates -/

/-- Include one CRT coordinate and reconstruct its residue modulo `180`. -/
noncomputable def crt180CoordinateEmbedding (i : Fin 3) :
    ZMod (crt180Modulus i) →+ ZMod 180 :=
  crt180AddEquiv.symm.toAddMonoidHom.comp
    (AddMonoidHom.single (fun j ↦ ZMod (crt180Modulus j)) i)

@[simp]
theorem crt180CoordinateEmbedding_apply (i : Fin 3)
    (a : ZMod (crt180Modulus i)) :
    crt180CoordinateEmbedding i a = fromCRT180 (Pi.single i a) := by
  rfl

/-- Restriction of the standard character of `ZMod 180` to one CRT factor,
after multiplication by the spatial coordinate. -/
noncomputable def z180StandardCoordinateChar (z : CRT180) (i : Fin 3) :
    AddChar (ZMod (crt180Modulus i)) ℂ :=
  (ZMod.stdAddChar (N := 180)).compAddMonoidHom
    ((crt180CoordinateEmbedding i).comp (AddMonoidHom.mulRight (z i)))

@[simp]
theorem z180StandardCoordinateChar_apply (z : CRT180) (i : Fin 3)
    (a : ZMod (crt180Modulus i)) :
    z180StandardCoordinateChar z i a =
      ZMod.stdAddChar (fromCRT180 (Pi.single i (a * z i))) := by
  rfl

theorem z180StandardCoordinateChar_eq_one_iff (z : CRT180) (i : Fin 3) :
    z180StandardCoordinateChar z i = 1 ↔ z i = 0 := by
  constructor
  · intro hchar
    have hvalue := congrArg
      (fun ψ : AddChar (ZMod (crt180Modulus i)) ℂ ↦ ψ 1) hchar
    have hstd :
        ZMod.stdAddChar (fromCRT180 (Pi.single i (z i))) =
          ZMod.stdAddChar (0 : ZMod 180) := by
      simpa using hvalue
    have hfrom : fromCRT180 (Pi.single i (z i)) = 0 :=
      ZMod.injective_stdAddChar hstd
    have hcoords := congrArg toCRT180 hfrom
    have hsingle : Pi.single i (z i) = (0 : CRT180) := by
      simpa using hcoords
    have hi := congrFun hsingle i
    simpa using hi
  · intro hz
    apply AddChar.ext
    intro a
    rw [z180StandardCoordinateChar_apply, hz, mul_zero]
    have hsingle : Pi.single i (0 : ZMod (crt180Modulus i)) =
        (0 : CRT180) := by
      ext j
      simp [Pi.single_apply]
    have hzero : fromCRT180 (0 : CRT180) = 0 :=
      crt180AddEquiv.symm.map_zero
    rw [hsingle, hzero]
    simp

theorem z180StandardCoordinateChar_apply_eq_one_iff
    (z : CRT180) (i : Fin 3) (a : ZMod (crt180Modulus i)) :
    z180StandardCoordinateChar z i a = 1 ↔ a * z i = 0 := by
  constructor
  · intro hchar
    have hstd :
        ZMod.stdAddChar (fromCRT180 (Pi.single i (a * z i))) =
          ZMod.stdAddChar (0 : ZMod 180) := by
      simpa using hchar
    have hfrom : fromCRT180 (Pi.single i (a * z i)) = 0 :=
      ZMod.injective_stdAddChar hstd
    have hcoords := congrArg toCRT180 hfrom
    have hsingle : Pi.single i (a * z i) = (0 : CRT180) := by
      simpa using hcoords
    have hi := congrFun hsingle i
    simpa using hi
  · intro haz
    rw [z180StandardCoordinateChar_apply, haz]
    have hsingle : Pi.single i (0 : ZMod (crt180Modulus i)) =
        (0 : CRT180) := by
      ext j
      simp [Pi.single_apply]
    have hzero : fromCRT180 (0 : CRT180) = 0 :=
      crt180AddEquiv.symm.map_zero
    rw [hsingle, hzero]
    simp

theorem sum_z180StandardCoordinateChar (z : CRT180) (i : Fin 3) :
    ∑ a : ZMod (crt180Modulus i), z180StandardCoordinateChar z i a =
      if z i = 0 then (crt180Modulus i : ℂ) else 0 := by
  classical
  by_cases hz : z i = 0
  · rw [if_pos hz]
    have hchar : z180StandardCoordinateChar z i = 1 :=
      (z180StandardCoordinateChar_eq_one_iff z i).2 hz
    simpa [hchar]
  · rw [if_neg hz]
    exact AddChar.sum_eq_zero_of_ne_one
      ((z180StandardCoordinateChar_eq_one_iff z i).not.mpr hz)

/-! ## Exact local frequency fibres -/

noncomputable def z180LocalExactFrequencies (i : Fin 3) (q : Nat) :
    Finset (ZMod (crt180Modulus i)) :=
  exactOrderFrequencies (N := crt180Modulus i) q

@[simp]
theorem mem_z180LocalExactFrequencies {i : Fin 3} {q : Nat}
    {a : ZMod (crt180Modulus i)} :
    a ∈ z180LocalExactFrequencies i q ↔
      frequencyOrder (crt180Modulus i) a = q := by
  simp [z180LocalExactFrequencies]

private theorem z180LocalExactFrequencies_four_one :
    z180LocalExactFrequencies 0 1 = {0} := by
  decide

private theorem z180LocalExactFrequencies_four_two :
    z180LocalExactFrequencies 0 2 = {2} := by
  decide

private theorem z180LocalExactFrequencies_four_four :
    z180LocalExactFrequencies 0 4 = {1, 3} := by
  decide

private theorem z180LocalExactFrequencies_nine_one :
    z180LocalExactFrequencies 1 1 = {0} := by
  decide

private theorem z180LocalExactFrequencies_nine_three :
    z180LocalExactFrequencies 1 3 = {3, 6} := by
  decide

private theorem z180LocalExactFrequencies_nine_nine :
    z180LocalExactFrequencies 1 9 = {1, 2, 4, 5, 7, 8} := by
  decide

private theorem z180LocalExactFrequencies_five_one :
    z180LocalExactFrequencies 2 1 = {0} := by
  decide

private theorem z180LocalExactFrequencies_five_five :
    z180LocalExactFrequencies 2 5 = {1, 2, 3, 4} := by
  decide

/-- The local exact-order character kernel. -/
noncomputable def z180LocalCharacterKernel
    (z : CRT180) (i : Fin 3) (q : Nat) : ℂ :=
  ∑ a ∈ z180LocalExactFrequencies i q,
    z180StandardCoordinateChar z i a

private theorem z180LocalCharacterKernel_four_one (z : CRT180) :
    z180LocalCharacterKernel z 0 1 = 1 := by
  rw [z180LocalCharacterKernel, z180LocalExactFrequencies_four_one]
  simp only [Finset.sum_singleton]
  exact (z180StandardCoordinateChar_apply_eq_one_iff z 0 0).2 (zero_mul _)

private theorem z180LocalCharacterKernel_four_two (z : CRT180) :
    z180LocalCharacterKernel z 0 2 =
      if (2 : ZMod (crt180Modulus 0)) * z 0 = 0 then 1 else -1 := by
  rw [z180LocalCharacterKernel, z180LocalExactFrequencies_four_two]
  simp only [Finset.sum_singleton]
  by_cases htwo : (2 : ZMod (crt180Modulus 0)) * z 0 = 0
  · rw [if_pos htwo]
    exact (z180StandardCoordinateChar_apply_eq_one_iff z 0 2).2 htwo
  · rw [if_neg htwo]
    let u : ℂ := z180StandardCoordinateChar z 0 2
    have hune : u ≠ 1 :=
      (z180StandardCoordinateChar_apply_eq_one_iff z 0 2).not.mpr htwo
    have husq : u ^ 2 = 1 := by
      change (z180StandardCoordinateChar z 0 2) ^ 2 = 1
      rw [← AddChar.map_nsmul_eq_pow]
      apply (z180StandardCoordinateChar_apply_eq_one_iff z 0 _).2
      change (0 : ZMod (crt180Modulus 0)) * z 0 = 0
      norm_num
    exact (sq_eq_one_iff.mp husq).resolve_left hune

private theorem z180LocalCharacterKernel_four_four (z : CRT180) :
    z180LocalCharacterKernel z 0 4 =
      if z 0 = 0 then 2
      else if (2 : ZMod (crt180Modulus 0)) * z 0 = 0 then -2 else 0 := by
  classical
  have hpart :
      (Finset.univ : Finset (ZMod 4)) =
        z180LocalExactFrequencies 0 1 ∪
          z180LocalExactFrequencies 0 2 ∪
            z180LocalExactFrequencies 0 4 := by
    rw [z180LocalExactFrequencies_four_one,
      z180LocalExactFrequencies_four_two,
      z180LocalExactFrequencies_four_four]
    decide
  have hdisj12 : Disjoint
      (z180LocalExactFrequencies 0 1)
      (z180LocalExactFrequencies 0 2) := by
    rw [z180LocalExactFrequencies_four_one,
      z180LocalExactFrequencies_four_two]
    decide
  have hdisj124 : Disjoint
      (z180LocalExactFrequencies 0 1 ∪
        z180LocalExactFrequencies 0 2)
      (z180LocalExactFrequencies 0 4) := by
    rw [z180LocalExactFrequencies_four_one,
      z180LocalExactFrequencies_four_two,
      z180LocalExactFrequencies_four_four]
    decide
  have hsplit :
      (∑ a : ZMod (crt180Modulus 0),
        z180StandardCoordinateChar z 0 a) =
        z180LocalCharacterKernel z 0 1 +
          z180LocalCharacterKernel z 0 2 +
            z180LocalCharacterKernel z 0 4 := by
    calc
      (∑ a : ZMod (crt180Modulus 0),
        z180StandardCoordinateChar z 0 a) =
          ∑ a ∈ (z180LocalExactFrequencies 0 1 ∪
              z180LocalExactFrequencies 0 2 ∪
                z180LocalExactFrequencies 0 4),
            z180StandardCoordinateChar z 0 a := by
              rw [← hpart]
              rfl
      _ = _ := by
        rw [Finset.sum_union hdisj124, Finset.sum_union hdisj12]
        rfl
  have hfull := sum_z180StandardCoordinateChar z 0
  rw [hsplit] at hfull
  rw [z180LocalCharacterKernel_four_one,
    z180LocalCharacterKernel_four_two] at hfull
  by_cases hz : z 0 = 0
  · rw [if_pos hz]
    rw [if_pos hz] at hfull
    have htwo : (2 : ZMod (crt180Modulus 0)) * z 0 = 0 := by
      rw [hz, mul_zero]
    rw [if_pos htwo] at hfull
    norm_num [crt180Modulus] at hfull
    linear_combination hfull
  · rw [if_neg hz]
    rw [if_neg hz] at hfull
    by_cases htwo : (2 : ZMod (crt180Modulus 0)) * z 0 = 0
    · rw [if_pos htwo]
      rw [if_pos htwo] at hfull
      norm_num [crt180Modulus] at hfull
      linear_combination hfull
    · rw [if_neg htwo]
      rw [if_neg htwo] at hfull
      norm_num [crt180Modulus] at hfull
      linear_combination hfull

private theorem z180LocalCharacterKernel_nine_one (z : CRT180) :
    z180LocalCharacterKernel z 1 1 = 1 := by
  rw [z180LocalCharacterKernel, z180LocalExactFrequencies_nine_one]
  simp only [Finset.sum_singleton]
  exact (z180StandardCoordinateChar_apply_eq_one_iff z 1 0).2 (zero_mul _)

private theorem z180LocalCharacterKernel_nine_three (z : CRT180) :
    z180LocalCharacterKernel z 1 3 =
      if (3 : ZMod (crt180Modulus 1)) * z 1 = 0 then 2 else -1 := by
  rw [z180LocalCharacterKernel, z180LocalExactFrequencies_nine_three]
  have h36 : (3 : ZMod (crt180Modulus 1)) ∉
      ({6} : Finset (ZMod (crt180Modulus 1))) := by
    decide
  rw [Finset.sum_insert h36, Finset.sum_singleton]
  by_cases hthree : (3 : ZMod (crt180Modulus 1)) * z 1 = 0
  · rw [if_pos hthree]
    have h3 : z180StandardCoordinateChar z 1 3 = 1 :=
      (z180StandardCoordinateChar_apply_eq_one_iff z 1 3).2 hthree
    have h6 : z180StandardCoordinateChar z 1 6 = 1 := by
      have h6zero : (6 : ZMod (crt180Modulus 1)) * z 1 = 0 := by
        calc
          (6 : ZMod (crt180Modulus 1)) * z 1 =
              (2 : ZMod (crt180Modulus 1)) *
                ((3 : ZMod (crt180Modulus 1)) * z 1) := by ring
          _ = 0 := by rw [hthree, mul_zero]
      exact (z180StandardCoordinateChar_apply_eq_one_iff z 1 6).2 h6zero
    rw [h3, h6]
    norm_num
  · rw [if_neg hthree]
    let u : ℂ := z180StandardCoordinateChar z 1 3
    have hune : u ≠ 1 :=
      (z180StandardCoordinateChar_apply_eq_one_iff z 1 3).not.mpr hthree
    have h6 : z180StandardCoordinateChar z 1 6 = u ^ 2 := by
      calc
        z180StandardCoordinateChar z 1 6 =
            z180StandardCoordinateChar z 1
              (2 • (3 : ZMod (crt180Modulus 1))) := by norm_num
        _ = (z180StandardCoordinateChar z 1 3) ^ 2 :=
          AddChar.map_nsmul_eq_pow (z180StandardCoordinateChar z 1) 2 3
        _ = u ^ 2 := by rfl
    have hucube : u ^ 3 = 1 := by
      change (z180StandardCoordinateChar z 1 3) ^ 3 = 1
      rw [← AddChar.map_nsmul_eq_pow]
      apply (z180StandardCoordinateChar_apply_eq_one_iff z 1 _).2
      change (0 : ZMod (crt180Modulus 1)) * z 1 = 0
      norm_num
    have hfactor : (u - 1) * (u ^ 2 + u + 1) = 0 := by
      calc
        (u - 1) * (u ^ 2 + u + 1) = u ^ 3 - 1 := by ring
        _ = 0 := by rw [hucube]; ring
    have hpoly : u ^ 2 + u + 1 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hune)
    rw [h6]
    linear_combination hpoly

private theorem z180LocalCharacterKernel_nine_nine (z : CRT180) :
    z180LocalCharacterKernel z 1 9 =
      if z 1 = 0 then 6
      else if (3 : ZMod (crt180Modulus 1)) * z 1 = 0 then -3 else 0 := by
  classical
  have hpart :
      (Finset.univ : Finset (ZMod 9)) =
        z180LocalExactFrequencies 1 1 ∪
          z180LocalExactFrequencies 1 3 ∪
            z180LocalExactFrequencies 1 9 := by
    rw [z180LocalExactFrequencies_nine_one,
      z180LocalExactFrequencies_nine_three,
      z180LocalExactFrequencies_nine_nine]
    decide
  have hdisj13 : Disjoint
      (z180LocalExactFrequencies 1 1)
      (z180LocalExactFrequencies 1 3) := by
    rw [z180LocalExactFrequencies_nine_one,
      z180LocalExactFrequencies_nine_three]
    decide
  have hdisj139 : Disjoint
      (z180LocalExactFrequencies 1 1 ∪
        z180LocalExactFrequencies 1 3)
      (z180LocalExactFrequencies 1 9) := by
    rw [z180LocalExactFrequencies_nine_one,
      z180LocalExactFrequencies_nine_three,
      z180LocalExactFrequencies_nine_nine]
    decide
  have hsplit :
      (∑ a : ZMod (crt180Modulus 1),
        z180StandardCoordinateChar z 1 a) =
        z180LocalCharacterKernel z 1 1 +
          z180LocalCharacterKernel z 1 3 +
            z180LocalCharacterKernel z 1 9 := by
    calc
      (∑ a : ZMod (crt180Modulus 1),
        z180StandardCoordinateChar z 1 a) =
          ∑ a ∈ (z180LocalExactFrequencies 1 1 ∪
              z180LocalExactFrequencies 1 3 ∪
                z180LocalExactFrequencies 1 9),
            z180StandardCoordinateChar z 1 a := by
              rw [← hpart]
              rfl
      _ = _ := by
        rw [Finset.sum_union hdisj139, Finset.sum_union hdisj13]
        rfl
  have hfull := sum_z180StandardCoordinateChar z 1
  rw [hsplit] at hfull
  rw [z180LocalCharacterKernel_nine_one,
    z180LocalCharacterKernel_nine_three] at hfull
  by_cases hz : z 1 = 0
  · rw [if_pos hz]
    rw [if_pos hz] at hfull
    have hthree : (3 : ZMod (crt180Modulus 1)) * z 1 = 0 := by
      rw [hz, mul_zero]
    rw [if_pos hthree] at hfull
    norm_num [crt180Modulus] at hfull
    linear_combination hfull
  · rw [if_neg hz]
    rw [if_neg hz] at hfull
    by_cases hthree : (3 : ZMod (crt180Modulus 1)) * z 1 = 0
    · rw [if_pos hthree]
      rw [if_pos hthree] at hfull
      norm_num [crt180Modulus] at hfull
      linear_combination hfull
    · rw [if_neg hthree]
      rw [if_neg hthree] at hfull
      norm_num [crt180Modulus] at hfull
      linear_combination hfull

private theorem z180LocalCharacterKernel_five_one (z : CRT180) :
    z180LocalCharacterKernel z 2 1 = 1 := by
  rw [z180LocalCharacterKernel, z180LocalExactFrequencies_five_one]
  simp only [Finset.sum_singleton]
  exact (z180StandardCoordinateChar_apply_eq_one_iff z 2 0).2 (zero_mul _)

private theorem z180LocalCharacterKernel_five_five (z : CRT180) :
    z180LocalCharacterKernel z 2 5 =
      if z 2 = 0 then 4 else -1 := by
  classical
  have hpart :
      (Finset.univ : Finset (ZMod 5)) =
        z180LocalExactFrequencies 2 1 ∪
          z180LocalExactFrequencies 2 5 := by
    rw [z180LocalExactFrequencies_five_one,
      z180LocalExactFrequencies_five_five]
    decide
  have hdisj : Disjoint
      (z180LocalExactFrequencies 2 1)
      (z180LocalExactFrequencies 2 5) := by
    rw [z180LocalExactFrequencies_five_one,
      z180LocalExactFrequencies_five_five]
    decide
  have hsplit :
      (∑ a : ZMod (crt180Modulus 2),
        z180StandardCoordinateChar z 2 a) =
        z180LocalCharacterKernel z 2 1 +
          z180LocalCharacterKernel z 2 5 := by
    calc
      (∑ a : ZMod (crt180Modulus 2),
        z180StandardCoordinateChar z 2 a) =
          ∑ a ∈ (z180LocalExactFrequencies 2 1 ∪
              z180LocalExactFrequencies 2 5),
            z180StandardCoordinateChar z 2 a := by
              rw [← hpart]
              rfl
      _ = _ := by
        rw [Finset.sum_union hdisj]
        rfl
  have hfull := sum_z180StandardCoordinateChar z 2
  rw [hsplit] at hfull
  rw [z180LocalCharacterKernel_five_one] at hfull
  by_cases hz : z 2 = 0
  · rw [if_pos hz]
    rw [if_pos hz] at hfull
    rw [crt180Modulus_two] at hfull
    norm_num at hfull
    linear_combination hfull
  · rw [if_neg hz]
    rw [if_neg hz] at hfull
    norm_num at hfull
    linear_combination hfull

/-! ## Integer spelling of the local kernels -/

def z180RamanujanFour (q r : Nat) : Int :=
  match q, r with
  | 1, _ => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 2, 4 => -1
  | 4, 1 => 2
  | 4, 2 => -2
  | 4, 4 => 0
  | _, _ => 0

def z180RamanujanNine (q r : Nat) : Int :=
  match q, r with
  | 1, _ => 1
  | 3, 1 => 2
  | 3, 3 => 2
  | 3, 9 => -1
  | 9, 1 => 6
  | 9, 3 => -3
  | 9, 9 => 0
  | _, _ => 0

def z180RamanujanFive (q r : Nat) : Int :=
  match q, r with
  | 1, _ => 1
  | 5, 1 => 4
  | 5, 5 => -1
  | _, _ => 0

def z180LocalRamanujanCoeff (i : Fin 3) (q r : Nat) : Int :=
  ![z180RamanujanFour q r,
    z180RamanujanNine q r,
    z180RamanujanFive q r] i

private theorem z180_four_two_condition :
    ∀ a : ZMod 4,
      (if (2 : ZMod 4) * a = 0 then (1 : Int) else -1) =
        z180RamanujanFour 2 (frequencyOrder 4 a) := by
  decide

private theorem z180_four_four_condition :
    ∀ a : ZMod 4,
      (if a = 0 then (2 : Int)
        else if (2 : ZMod 4) * a = 0 then -2 else 0) =
        z180RamanujanFour 4 (frequencyOrder 4 a) := by
  decide

private theorem z180_nine_three_condition :
    ∀ a : ZMod 9,
      (if (3 : ZMod 9) * a = 0 then (2 : Int) else -1) =
        z180RamanujanNine 3 (frequencyOrder 9 a) := by
  decide

private theorem z180_nine_nine_condition :
    ∀ a : ZMod 9,
      (if a = 0 then (6 : Int)
        else if (3 : ZMod 9) * a = 0 then -3 else 0) =
        z180RamanujanNine 9 (frequencyOrder 9 a) := by
  decide

private theorem z180_five_five_condition :
    ∀ a : ZMod 5,
      (if a = 0 then (4 : Int) else -1) =
        z180RamanujanFive 5 (frequencyOrder 5 a) := by
  decide

theorem z180LocalCharacterKernel_four_one_coeff (z : CRT180) :
    z180LocalCharacterKernel z 0 1 =
      (z180RamanujanFour 1 (frequencyOrder 4 (z 0)) : ℂ) := by
  rw [z180LocalCharacterKernel_four_one]
  norm_num [z180RamanujanFour]

theorem z180LocalCharacterKernel_four_two_coeff (z : CRT180) :
    z180LocalCharacterKernel z 0 2 =
      (z180RamanujanFour 2 (frequencyOrder 4 (z 0)) : ℂ) := by
  rw [z180LocalCharacterKernel_four_two]
  exact_mod_cast z180_four_two_condition (z 0)

theorem z180LocalCharacterKernel_four_four_coeff (z : CRT180) :
    z180LocalCharacterKernel z 0 4 =
      (z180RamanujanFour 4 (frequencyOrder 4 (z 0)) : ℂ) := by
  rw [z180LocalCharacterKernel_four_four]
  exact_mod_cast z180_four_four_condition (z 0)

theorem z180LocalCharacterKernel_nine_one_coeff (z : CRT180) :
    z180LocalCharacterKernel z 1 1 =
      (z180RamanujanNine 1 (frequencyOrder 9 (z 1)) : ℂ) := by
  rw [z180LocalCharacterKernel_nine_one]
  norm_num [z180RamanujanNine]

theorem z180LocalCharacterKernel_nine_three_coeff (z : CRT180) :
    z180LocalCharacterKernel z 1 3 =
      (z180RamanujanNine 3 (frequencyOrder 9 (z 1)) : ℂ) := by
  rw [z180LocalCharacterKernel_nine_three]
  exact_mod_cast z180_nine_three_condition (z 1)

theorem z180LocalCharacterKernel_nine_nine_coeff (z : CRT180) :
    z180LocalCharacterKernel z 1 9 =
      (z180RamanujanNine 9 (frequencyOrder 9 (z 1)) : ℂ) := by
  rw [z180LocalCharacterKernel_nine_nine]
  exact_mod_cast z180_nine_nine_condition (z 1)

theorem z180LocalCharacterKernel_five_one_coeff (z : CRT180) :
    z180LocalCharacterKernel z 2 1 =
      (z180RamanujanFive 1 (frequencyOrder 5 (z 2)) : ℂ) := by
  rw [z180LocalCharacterKernel_five_one]
  norm_num [z180RamanujanFive]

theorem z180LocalCharacterKernel_five_five_coeff (z : CRT180) :
    z180LocalCharacterKernel z 2 5 =
      (z180RamanujanFive 5 (frequencyOrder 5 (z 2)) : ℂ) := by
  rw [z180LocalCharacterKernel_five_five]
  exact_mod_cast z180_five_five_condition (z 2)

/-! ## Product character and Fourier expansion -/

/-- The standard character pairing transported to CRT coordinates. -/
noncomputable def z180StandardCRTCharacterPairing (z d : CRT180) : ℂ :=
  ZMod.stdAddChar (fromCRT180 (d * z))

/-- The transported standard character factors over the three CRT factors. -/
theorem z180StandardCRTCharacterPairing_eq_prod (z d : CRT180) :
    z180StandardCRTCharacterPairing z d =
      ∏ i, z180StandardCoordinateChar z i (d i) := by
  classical
  have hdecomp :
      (∑ i, Pi.single i (d i * z i)) = d * z := by
    funext i
    change (∑ j, Pi.single j (d j * z j) i) = d i * z i
    exact Fintype.sum_pi_single i (fun j ↦ d j * z j)
  have hfromSum :
      fromCRT180 (∑ i, Pi.single i (d i * z i)) =
        ∑ i, fromCRT180 (Pi.single i (d i * z i)) := by
    change crt180AddEquiv.symm (∑ i, Pi.single i (d i * z i)) = _
    exact map_sum crt180AddEquiv.symm
      (fun i ↦ Pi.single i (d i * z i)) Finset.univ
  have hcharSum (s : Finset (Fin 3)) :
      ZMod.stdAddChar
          (∑ i ∈ s, fromCRT180 (Pi.single i (d i * z i))) =
        ∏ i ∈ s,
          ZMod.stdAddChar (fromCRT180 (Pi.single i (d i * z i))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha,
          AddChar.map_add_eq_mul, ih]
  rw [z180StandardCRTCharacterPairing, ← hdecomp, hfromSum]
  simpa [z180StandardCoordinateChar_apply] using
    hcharSum (Finset.univ : Finset (Fin 3))

@[simp]
theorem fromCRT180_mul (x y : CRT180) :
    fromCRT180 (x * y) = fromCRT180 x * fromCRT180 y := by
  change crt180RingEquiv.symm (x * y) =
    crt180RingEquiv.symm x * crt180RingEquiv.symm y
  exact crt180RingEquiv.symm.map_mul x y

theorem z180StandardCRTCharacterPairing_mul_star
    (x y d : CRT180) :
    z180StandardCRTCharacterPairing x d *
        star (z180StandardCRTCharacterPairing y d) =
      z180StandardCRTCharacterPairing (x - y) d := by
  rw [z180StandardCRTCharacterPairing,
    z180StandardCRTCharacterPairing,
    z180StandardCRTCharacterPairing,
    star_stdAddChar, ← AddChar.map_add_eq_mul]
  congr 1
  rw [← sub_eq_add_neg]
  change fromCRT180 (d * x) - fromCRT180 (d * y) =
    fromCRT180 (d * (x - y))
  unfold fromCRT180
  rw [← crt180AddEquiv.symm.map_sub]
  congr 1
  ring

noncomputable def z180StandardCRTFourierSum
    (X : Finset (ZMod 180)) (d : CRT180) : ℂ :=
  ∑ x ∈ X, z180StandardCRTCharacterPairing (toCRT180 x) d

theorem z180StandardCRTFourierSum_eq_fourierSum
    (X : Finset (ZMod 180)) (d : CRT180) :
    z180StandardCRTFourierSum X d = fourierSum X (fromCRT180 d) := by
  calc
    z180StandardCRTFourierSum X d =
        ∑ x ∈ X, ZMod.stdAddChar (x * fromCRT180 d) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [z180StandardCRTFourierSum,
        z180StandardCRTCharacterPairing, mul_comm]
    _ = ∑ x : ↥X, ZMod.stdAddChar (x.1 * fromCRT180 d) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach X
          (fun x ↦ ZMod.stdAddChar (x * fromCRT180 d))).symm
    _ = fourierSum X (fromCRT180 d) := rfl

theorem z180StandardCRTFourierSum_mul_star
    (X : Finset (ZMod 180)) (d : CRT180) :
    z180StandardCRTFourierSum X d * star (z180StandardCRTFourierSum X d) =
      ∑ p ∈ X ×ˢ X,
        z180StandardCRTCharacterPairing (toCRT180 (p.1 - p.2)) d := by
  classical
  simp only [z180StandardCRTFourierSum, star_sum]
  rw [Finset.sum_mul_sum]
  calc
    (∑ x ∈ X, ∑ y ∈ X,
        z180StandardCRTCharacterPairing (toCRT180 x) d *
          star (z180StandardCRTCharacterPairing (toCRT180 y) d)) =
        ∑ p ∈ X ×ˢ X,
          z180StandardCRTCharacterPairing (toCRT180 p.1) d *
            star (z180StandardCRTCharacterPairing (toCRT180 p.2) d) := by
      exact (Finset.sum_product X X (fun p ↦
        z180StandardCRTCharacterPairing (toCRT180 p.1) d *
          star (z180StandardCRTCharacterPairing (toCRT180 p.2) d))).symm
    _ = ∑ p ∈ X ×ˢ X,
        z180StandardCRTCharacterPairing (toCRT180 (p.1 - p.2)) d := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [z180StandardCRTCharacterPairing_mul_star, ← toCRT180_sub]

/-! ## Grouping pairs by the order of their difference -/

/-- Product of the three prime-power Ramanujan coefficients. -/
def z180RamanujanCoeff (e r : Nat) : Int :=
  z180RamanujanFour (Nat.gcd e 4) (Nat.gcd r 4) *
    z180RamanujanNine (Nat.gcd e 9) (Nat.gcd r 9) *
      z180RamanujanFive (Nat.gcd e 5) (Nat.gcd r 5)

private theorem z180_divisors_explicit :
    (180).divisors =
      {1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180} := by
  decide

noncomputable def z180PairKernelSum
    (X : Finset (ZMod 180)) (e : Nat) : Int :=
  ∑ p ∈ X ×ˢ X,
    z180RamanujanCoeff e (frequencyOrder 180 (p.1 - p.2))

theorem z180_sum_distribution_eq_pairKernelSum
    (X : Finset (ZMod 180)) (e : Nat) :
    (∑ r ∈ (180).divisors,
        exactOrderDistributionInt X r * z180RamanujanCoeff e r) =
      z180PairKernelSum X e := by
  classical
  rw [z180PairKernelSum]
  simp only [exactOrderDistributionInt, exactOrderDistribution,
    exactOrderPairs]
  calc
    (∑ r ∈ (180).divisors,
        (((X ×ˢ X).filter fun p ↦ frequencyOrder 180 (p.1 - p.2) = r).card : Int) *
          z180RamanujanCoeff e r) =
        ∑ r ∈ (180).divisors,
          ∑ p ∈ (X ×ˢ X).filter
              (fun p ↦ frequencyOrder 180 (p.1 - p.2) = r),
            z180RamanujanCoeff e r := by
      apply Finset.sum_congr rfl
      intro r hr
      simp
    _ = ∑ r ∈ (180).divisors,
          ∑ p ∈ (X ×ˢ X).filter
              (fun p ↦ frequencyOrder 180 (p.1 - p.2) = r),
            z180RamanujanCoeff e (frequencyOrder 180 (p.1 - p.2)) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = ∑ p ∈ X ×ˢ X,
          z180RamanujanCoeff e (frequencyOrder 180 (p.1 - p.2)) := by
      let g : ZMod 180 × ZMod 180 → Nat :=
        fun p ↦ frequencyOrder 180 (p.1 - p.2)
      let f : ZMod 180 × ZMod 180 → Int :=
        fun p ↦ z180RamanujanCoeff e (g p)
      have hvalues : ∀ p ∈ X ×ˢ X, g p ∈ (180).divisors := by
        intro p hp
        exact Nat.mem_divisors.mpr
          ⟨frequencyOrder_dvd_modulus (p.1 - p.2), by norm_num⟩
      have hfiber := Finset.sum_fiberwise_eq_sum_filter
        (X ×ˢ X) (180).divisors g f
      have hfilter :
          (X ×ˢ X).filter (fun p ↦ g p ∈ (180).divisors) = X ×ˢ X :=
        Finset.filter_eq_self.mpr hvalues
      rw [hfilter] at hfiber
      simpa [g, f] using hfiber

set_option maxHeartbeats 0 in
/-- The generated 18-by-18 table is exactly the product Ramanujan table. -/
theorem z180ExactOrderTransform_eq_sum_distribution
    (X : Finset (ZMod 180)) {e : Nat}
    (he : e ∈ (180).divisors) :
    z180ExactOrderTransform X e =
      ∑ r ∈ (180).divisors,
        exactOrderDistributionInt X r * z180RamanujanCoeff e r := by
  rw [z180_divisors_explicit] at he ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [z180ExactOrderTransform, z180RamanujanCoeff,
      z180RamanujanFour, z180RamanujanNine, z180RamanujanFive] <;> ring

theorem z180ExactOrderTransform_eq_pairKernelSum
    (X : Finset (ZMod 180)) {e : Nat}
    (he : e ∈ (180).divisors) :
    z180ExactOrderTransform X e = z180PairKernelSum X e := by
  rw [z180ExactOrderTransform_eq_sum_distribution X he,
    z180_sum_distribution_eq_pairKernelSum]

end Fuglede
