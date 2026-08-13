import Fuglede.SupportOrder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The arithmetic endpoint of the Laba--Marshall cuboid bound

For Corollary 6.5 of Laba--Marshall, the cuboid argument has three logically
separate parts:

1. every added prime axis divides each lower-dimensional cuboid evaluation;
2. pairwise coprimality turns the individual divisibilities into divisibility
   by their product;
3. a nonzero signed evaluation is at least that product in absolute value,
   while nonnegative multiplicities and signs in `{-1, 0, 1}` bound it by the
   total mass.

This file kernel-checks parts (2) and (3), including the exact specialization
to the five CRT axes of `ZMod 2310`.  The still-separate cyclotomic/cube-rule
bridge is intentionally not postulated here.
-/

namespace Fuglede

open scoped BigOperators

/-- The integer evaluation of nonnegative weights against a signed test
function.  Cuboid evaluations are instances in which the test function has
values in `{-1, 0, 1}`. -/
def weightedSignedEvaluation {alpha : Type*} [Fintype alpha]
    (weight : alpha -> Nat) (sign : alpha -> Int) : Int :=
  ∑ x, (weight x : Int) * sign x

/-- The total mass of a nonnegative integer-valued multiset. -/
def totalWeight {alpha : Type*} [Fintype alpha]
    (weight : alpha -> Nat) : Nat :=
  ∑ x, weight x

/-- A signed cuboid evaluation cannot have absolute value larger than the
total mass.  Only the pointwise estimate `|sign| <= 1` is used. -/
theorem natAbs_weightedSignedEvaluation_le_totalWeight
    {alpha : Type*} [Fintype alpha]
    (weight : alpha -> Nat) (sign : alpha -> Int)
    (hsign : forall x, (sign x).natAbs <= 1) :
    (weightedSignedEvaluation weight sign).natAbs <= totalWeight weight := by
  classical
  rw [weightedSignedEvaluation, totalWeight]
  calc
    (∑ x, (weight x : Int) * sign x).natAbs <=
        ∑ x, (((weight x : Int) * sign x).natAbs) := by
      simpa only [Finset.sum_attach] using
        Int.natAbs_sum_le (Finset.univ : Finset alpha)
          (fun x => (weight x : Int) * sign x)
    _ = ∑ x, weight x * (sign x).natAbs := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Int.natAbs_mul]
    _ <= ∑ x, weight x := by
      apply Finset.sum_le_sum
      intro x hx
      simpa using Nat.mul_le_mul_left (weight x) (hsign x)

/-- Evaluation of an ordinary finite set against an integer-valued signed
test function. -/
def signedFinsetEvaluation {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (sign : alpha -> Int) : Int :=
  ∑ x ∈ A, sign x

/-- Finite-set version of the mass bound used in the Fuglede application. -/
theorem natAbs_signedFinsetEvaluation_le_card
    {alpha : Type*} [DecidableEq alpha]
    (A : Finset alpha) (sign : alpha -> Int)
    (hsign : forall x, x ∈ A -> (sign x).natAbs <= 1) :
    (signedFinsetEvaluation A sign).natAbs <= A.card := by
  rw [signedFinsetEvaluation]
  calc
    (∑ x ∈ A, sign x).natAbs <= ∑ x ∈ A, (sign x).natAbs :=
      Int.natAbs_sum_le A sign
    _ <= ∑ _x ∈ A, 1 := by
      exact Finset.sum_le_sum fun x hx => hsign x hx
    _ = A.card := by simp

/-- Alternating sign of a CRT cuboid supported on `D`.  Coordinates in `D`
must equal the corresponding low or high vertex; points outside the cuboid
receive coefficient zero.  Coordinates outside `D` are projected away, so
they do not enter the sign. -/
noncomputable def crtCuboidSign (D : Finset (Fin 5))
    (lo hi : CRT2310) (x : ZMod 2310) : Int :=
  ∏ i ∈ D,
    if toCRT2310 x i = lo i then 1
    else if toCRT2310 x i = hi i then -1
    else 0

/-- Every CRT cuboid coefficient belongs to `{-1, 0, 1}` in the precise
form needed by the mass bound. -/
theorem natAbs_crtCuboidSign_le_one (D : Finset (Fin 5))
    (lo hi : CRT2310) (x : ZMod 2310) :
    (crtCuboidSign D lo hi x).natAbs <= 1 := by
  classical
  induction D using Finset.induction_on with
  | empty => simp [crtCuboidSign]
  | @insert i D hiD ih =>
      rw [crtCuboidSign, Finset.prod_insert hiD, Int.natAbs_mul]
      rw [show (∏ j ∈ D,
        if toCRT2310 x j = lo j then (1 : Int)
        else if toCRT2310 x j = hi j then -1 else 0) =
          crtCuboidSign D lo hi x by rfl]
      by_cases hlo : toCRT2310 x i = lo i
      · rw [if_pos hlo]
        simpa using ih
      · by_cases hhi : toCRT2310 x i = hi i
        · rw [if_neg hlo, if_pos hhi]
          simpa using ih
        · rw [if_neg hlo, if_neg hhi]
          simp

/-- Contribution to a signed evaluation from one fiber of a finite-valued
coordinate.  In the cuboid proof this is the evaluation of one level. -/
def signedLevelEvaluation {alpha beta : Type*}
    [DecidableEq alpha] [DecidableEq beta]
    (A : Finset alpha) (sign : alpha -> Int) (coord : alpha -> beta)
    (b : beta) : Int :=
  ∑ x ∈ A.filter (fun x => coord x = b), sign x

/-- Summing all level evaluations recovers the original signed evaluation.
This is the formal fiber decomposition behind equation (6.3) in the
Laba--Marshall proof. -/
theorem sum_signedLevelEvaluation_eq_signedFinsetEvaluation
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta] [Fintype beta]
    (A : Finset alpha) (sign : alpha -> Int) (coord : alpha -> beta) :
    (∑ b, signedLevelEvaluation A sign coord b) =
      signedFinsetEvaluation A sign := by
  classical
  simpa [signedLevelEvaluation, signedFinsetEvaluation] using
    Finset.sum_fiberwise_eq_sum_filter A (Finset.univ : Finset beta)
      coord sign

/-- If all levels of an integer evaluation are equal, their sum is divisible
by the number of levels.  This is the arithmetic content of equation (6.7).
-/
theorem fintypeCard_dvd_sum_of_pairwise_eq
    {beta : Type*} [Fintype beta] [Nonempty beta]
    (levelEval : beta -> Int)
    (hlevel : forall b c, levelEval b = levelEval c) :
    (Fintype.card beta : Int) ∣ ∑ b, levelEval b := by
  classical
  let b0 : beta := Classical.choice inferInstance
  refine ⟨levelEval b0, ?_⟩
  calc
    (∑ b, levelEval b) = ∑ _b : beta, levelEval b0 := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hlevel b b0
    _ = (Fintype.card beta : Int) * levelEval b0 := by simp

/-- Equal signed evaluations on all fibers of a coordinate force the
coordinate cardinality to divide the total signed evaluation. -/
theorem fintypeCard_dvd_signedFinsetEvaluation_of_levels_eq
    {alpha beta : Type*}
    [DecidableEq alpha] [DecidableEq beta] [Fintype beta] [Nonempty beta]
    (A : Finset alpha) (sign : alpha -> Int) (coord : alpha -> beta)
    (hlevel : forall b c,
      signedLevelEvaluation A sign coord b =
        signedLevelEvaluation A sign coord c) :
    (Fintype.card beta : Int) ∣ signedFinsetEvaluation A sign := by
  have hdiv := fintypeCard_dvd_sum_of_pairwise_eq
    (fun b => signedLevelEvaluation A sign coord b) hlevel
  rw [sum_signedLevelEvaluation_eq_signedFinsetEvaluation] at hdiv
  exact hdiv

/-- For one CRT coordinate, levelwise constancy gives precisely divisibility
by its prime modulus. -/
theorem crt2310Modulus_dvd_signedFinsetEvaluation_of_levels_eq
    (A : Finset (ZMod 2310)) (sign : ZMod 2310 -> Int) (i : Fin 5)
    (hlevel : forall b c : ZMod (crt2310Modulus i),
      signedLevelEvaluation A sign (fun x => toCRT2310 x i) b =
        signedLevelEvaluation A sign (fun x => toCRT2310 x i) c) :
    (crt2310Modulus i : Int) ∣ signedFinsetEvaluation A sign := by
  simpa using fintypeCard_dvd_signedFinsetEvaluation_of_levels_eq
    A sign (fun x => toCRT2310 x i) hlevel

/-- Pairwise-coprime natural factors which all divide an integer divide its
absolute value as a product. -/
theorem prod_dvd_natAbs_of_pairwise_coprime
    {iota : Type*} (axes : Finset iota) (factor : iota -> Nat)
    (hcoprime : (axes : Set iota).Pairwise
      (fun i j => Nat.Coprime (factor i) (factor j)))
    {evaluation : Int}
    (hdiv : forall i, i ∈ axes -> (factor i : Int) ∣ evaluation) :
    (∏ i ∈ axes, factor i) ∣ evaluation.natAbs := by
  classical
  have hdivNat : forall i, i ∈ axes -> factor i ∣ evaluation.natAbs := by
    intro i hi
    rw [← Int.natCast_dvd]
    exact hdiv i hi
  induction axes using Finset.induction_on with
  | empty => simp
  | @insert a axes ha ih =>
      rw [Finset.prod_insert ha]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.prod_right
        intro i hi
        exact hcoprime (by simp) (by simp [hi])
          (ne_of_mem_of_not_mem hi ha).symm
      · exact hdivNat a (Finset.mem_insert_self a axes)
      · apply ih
        · exact hcoprime.mono (by simp)
        · intro i hi
          exact hdiv i (Finset.mem_insert_of_mem hi)
        · intro i hi
          exact hdivNat i (Finset.mem_insert_of_mem hi)

/-- Pure arithmetic endpoint of Laba--Marshall Corollary 6.5: if the product
of the added prime axes divides a nonzero cuboid evaluation and that
evaluation is bounded by the mass, the prime product is bounded by the mass.
-/
theorem labaMarshall_arithmetic_endpoint
    {primeProduct mass : Nat} {evaluation : Int}
    (hdiv : (primeProduct : Int) ∣ evaluation)
    (hne : evaluation ≠ 0)
    (hbound : evaluation.natAbs <= mass) :
    primeProduct <= mass := by
  have hdivNat : primeProduct ∣ evaluation.natAbs := by
    rw [← Int.natCast_dvd]
    exact hdiv
  exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hdivNat).trans hbound

/-- Multi-axis version in which the individual divisibilities are supplied
by the levelwise cube argument (Lemma 6.1 in Laba--Marshall). -/
theorem labaMarshall_of_axis_divisibility
    {iota : Type*} (axes : Finset iota) (factor : iota -> Nat)
    (hcoprime : (axes : Set iota).Pairwise
      (fun i j => Nat.Coprime (factor i) (factor j)))
    {mass : Nat} {evaluation : Int}
    (haxis : forall i, i ∈ axes -> (factor i : Int) ∣ evaluation)
    (hne : evaluation ≠ 0)
    (hbound : evaluation.natAbs <= mass) :
    (∏ i ∈ axes, factor i) <= mass := by
  have hprod : (∏ i ∈ axes, factor i) ∣ evaluation.natAbs :=
    prod_dvd_natAbs_of_pairwise_coprime axes factor hcoprime haxis
  exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hprod).trans hbound

/-- Exact `ZMod 2310` specialization.  `D` is the set of added prime CRT
axes; its product is `supportModulus D`. -/
theorem labaMarshall_2310_of_axis_divisibility
    (D : Finset (Fin 5)) {mass : Nat} {evaluation : Int}
    (haxis : forall i, i ∈ D ->
      (crt2310Modulus i : Int) ∣ evaluation)
    (hne : evaluation ≠ 0)
    (hbound : evaluation.natAbs <= mass) :
    supportModulus D <= mass := by
  unfold supportModulus
  exact labaMarshall_of_axis_divisibility D crt2310Modulus
    (crt2310Modulus_pairwise.set_pairwise D) haxis hne hbound

/-- Finite-set endpoint for `ZMod 2310`: once the cube-rule layer produces a
nonzero signed cuboid witness and the axis divisibilities, the desired
cardinality bound follows with no additional mathematical assumption. -/
theorem labaMarshall_2310_finset_endpoint
    (D : Finset (Fin 5)) (A : Finset (ZMod 2310))
    (sign : ZMod 2310 -> Int)
    (hsign : forall x, x ∈ A -> (sign x).natAbs <= 1)
    (haxis : forall i, i ∈ D ->
      (crt2310Modulus i : Int) ∣ signedFinsetEvaluation A sign)
    (hne : signedFinsetEvaluation A sign ≠ 0) :
    supportModulus D <= A.card := by
  apply labaMarshall_2310_of_axis_divisibility D haxis hne
  exact natAbs_signedFinsetEvaluation_le_card A sign hsign

/-- Levelwise form of the complete arithmetic/cuboidal endpoint for
`ZMod 2310`.  The only remaining input for the cyclotomic theorem is now the
implication from each divisor `Phi_(d*p_i)` to equality of the displayed
level evaluations. -/
theorem labaMarshall_2310_finset_of_levelwise_constant
    (D : Finset (Fin 5)) (A : Finset (ZMod 2310))
    (sign : ZMod 2310 -> Int)
    (hsign : forall x, x ∈ A -> (sign x).natAbs <= 1)
    (hlevel : forall i, i ∈ D ->
      forall b c : ZMod (crt2310Modulus i),
        signedLevelEvaluation A sign (fun x => toCRT2310 x i) b =
          signedLevelEvaluation A sign (fun x => toCRT2310 x i) c)
    (hne : signedFinsetEvaluation A sign ≠ 0) :
    supportModulus D <= A.card := by
  apply labaMarshall_2310_finset_endpoint D A sign hsign
  · intro i hi
    exact crt2310Modulus_dvd_signedFinsetEvaluation_of_levels_eq
      A sign i (hlevel i hi)
  · exact hne

/-- Concrete cuboid-sign form, simultaneously covering all `2^5 = 32`
possible base supports and every set of added prime axes.  The levelwise
constancy hypothesis is exactly what the enlarged cube rules must supply. -/
theorem labaMarshall_2310_cuboid_of_levelwise_constant
    (baseAxes addedAxes : Finset (Fin 5))
    (A : Finset (ZMod 2310)) (lo hi : CRT2310)
    (hlevel : forall i, i ∈ addedAxes ->
      forall b c : ZMod (crt2310Modulus i),
        signedLevelEvaluation A (crtCuboidSign baseAxes lo hi)
            (fun x => toCRT2310 x i) b =
          signedLevelEvaluation A (crtCuboidSign baseAxes lo hi)
            (fun x => toCRT2310 x i) c)
    (hne : signedFinsetEvaluation A (crtCuboidSign baseAxes lo hi) ≠ 0) :
    supportModulus addedAxes <= A.card := by
  apply labaMarshall_2310_finset_of_levelwise_constant
    addedAxes A (crtCuboidSign baseAxes lo hi)
  · intro x hx
    exact natAbs_crtCuboidSign_le_one baseAxes lo hi x
  · exact hlevel
  · exact hne

end Fuglede
