import Fuglede.Z180K18M12PhaseCharacter
import Fuglede.Z180K18M12PhaseCountArithmetic
import Mathlib.Tactic

/-!
# Reindexing fifth-level Fourier sums by the nine oriented pairs

This module contains the finite-sum bookkeeping for the analytic part of
block B.  It proves two exact identities:

* a fifth-level Fourier sum is the common pair factor times the sum of its
  nine-pair phases in that level;
* evaluation of the normalized phase-count polynomial is the corresponding
  normalized phase-character sum.
-/

namespace Fuglede

open Polynomial
open scoped BigOperators

/-- Raw phase-character sum of the pair indices in one fifth level. -/
noncomputable def z180K18M12PairPhaseSum
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (c : ZMod 5) : ℂ :=
  ∑ r ∈ z180K18M12PairLevelFiber p c,
    z180K18M12PhaseChar (z180K18M12PairPhase p r)

/-- Normalized phase-character sum of the pair indices in one fifth level. -/
noncomputable def z180K18M12NormalizedPhaseSum
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (c : ZMod 5) : ℂ :=
  ∑ r ∈ z180K18M12PairLevelFiber p c,
    z180K18M12PhaseChar (z180K18M12NormalizedPairPhase p shift r)

/-- Point set in one fifth-coordinate level, using the direct cast spelling. -/
def z180K18M12PointLevel
    (A : Finset (ZMod 180)) (c : ZMod 5) : Finset (ZMod 180) :=
  A.filter fun x => (ZMod.cast x : ZMod 5) = c

/-- Reorienting a pair only swaps its two summands. -/
theorem z180K18M12_oriented_sum
    {A : Finset (ZMod 180)} {R : Type*} [AddCommMonoid R]
    (p : Z180K18M12PairFibres A) (w : ZMod 180 → R) (r : ZMod 9) :
    w (z180K18M12OrientedFirst p r) +
        w (z180K18M12OrientedSecond p r) =
      w (p.first r) + w (p.second r) := by
  unfold z180K18M12OrientedFirst z180K18M12OrientedSecond
  split_ifs
  · rfl
  · rw [add_comm]

/-- Intersecting one point level with a modulo-nine fibre gives either the
named pair or the empty set. -/
theorem z180K18M12PointLevel_nineFiber
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (c : ZMod 5) (r : ZMod 9) :
    (z180K18M12PointLevel A c).filter
        (fun x => (ZMod.cast x : ZMod 9) = r) =
      if p.level r = c then {p.first r, p.second r} else ∅ := by
  classical
  by_cases hrc : p.level r = c
  · rw [if_pos hrc]
    ext x
    constructor
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hxLevel, hx9⟩
      rcases Finset.mem_filter.mp hxLevel with ⟨hxA, hx5⟩
      have hxFiber : x ∈ z180K18M12NineFiber A r :=
        Finset.mem_filter.mpr ⟨hxA, hx9⟩
      rw [p.fiber_eq_pair r] at hxFiber
      exact hxFiber
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨
          Finset.mem_filter.mpr
            ⟨p.first_mem r, (p.first_level r).trans hrc⟩,
          p.first_cast_nine r⟩
      · exact Finset.mem_filter.mpr ⟨
          Finset.mem_filter.mpr
            ⟨p.second_mem r, (p.second_level r).trans hrc⟩,
          p.second_cast_nine r⟩
  · rw [if_neg hrc]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxLevel, hx9⟩
    rcases Finset.mem_filter.mp hxLevel with ⟨hxA, hx5⟩
    have hxFiber : x ∈ z180K18M12NineFiber A r :=
      Finset.mem_filter.mpr ⟨hxA, hx9⟩
    rw [p.fiber_eq_pair r] at hxFiber
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxFiber
    rcases hxFiber with rfl | rfl
    · exact hrc ((p.first_level r).symm.trans hx5)
    · exact hrc ((p.second_level r).symm.trans hx5)

/-- Reindex one fifth-level Fourier sum by its oriented pairs. -/
theorem z180K18M12_fiveLevelFourierSum_eq_pairWeights
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (c : ZMod 5) :
    z180FiveLevelFourierSum A z180K18M12OrderTwelveBaseFrequency c =
      ∑ r ∈ z180K18M12PairLevelFiber p c,
        (z180StandardCRTCharacterPairing
            (toCRT180 (z180K18M12OrientedFirst p r))
            z180K18M12OrderTwelveBaseFrequency +
          z180StandardCRTCharacterPairing
            (toCRT180 (z180K18M12OrientedSecond p r))
            z180K18M12OrderTwelveBaseFrequency) := by
  classical
  have hlevel :
      A.filter (fun x => crt180FifthCoord (toCRT180 x) = c) =
        z180K18M12PointLevel A c := by
    ext x
    simp only [Finset.mem_filter, z180K18M12PointLevel]
    rw [crt180FifthCoord_toCRT180]
  unfold z180FiveLevelFourierSum
  rw [hlevel]
  let w : ZMod 180 → ℂ := fun x =>
    z180StandardCRTCharacterPairing (toCRT180 x)
      z180K18M12OrderTwelveBaseFrequency
  change (∑ x ∈ z180K18M12PointLevel A c, w x) =
    ∑ r ∈ z180K18M12PairLevelFiber p c,
      (w (z180K18M12OrientedFirst p r) +
        w (z180K18M12OrientedSecond p r))
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    (z180K18M12PointLevel A c) (Finset.univ : Finset (ZMod 9))
      (fun x => (ZMod.cast x : ZMod 9))
      w
  calc
    _ = ∑ r : ZMod 9,
        ∑ x ∈ (z180K18M12PointLevel A c).filter
          (fun x => (ZMod.cast x : ZMod 9) = r), w x := by
      simpa using hfiber.symm
    _ = ∑ r : ZMod 9, if p.level r = c then
        (w (p.first r) + w (p.second r)) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [z180K18M12PointLevel_nineFiber p c r]
      split_ifs
      · simp [p.first_ne_second r]
      · simp
    _ = ∑ r : ZMod 9, if p.level r = c then
        (w (z180K18M12OrientedFirst p r) +
          w (z180K18M12OrientedSecond p r)) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrc : p.level r = c
      · rw [if_pos hrc, if_pos hrc, z180K18M12_oriented_sum]
      · rw [if_neg hrc, if_neg hrc]
    _ = _ := by
      rw [z180K18M12PairLevelFiber, Finset.sum_filter]

/-- The preceding reindexing and the local pair identity give the common
factorisation of every fifth-level Fourier sum. -/
theorem z180K18M12_fiveLevelFourierSum_factor
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (c : ZMod 5) :
    z180FiveLevelFourierSum A z180K18M12OrderTwelveBaseFrequency c =
      z180K18M12PairRootFactor * z180K18M12PairPhaseSum p c := by
  rw [z180K18M12_fiveLevelFourierSum_eq_pairWeights,
    z180K18M12PairPhaseSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact z180K18M12_orientedPair_factor p r

/-- The singleton pair level has raw phase sum equal to its one phase. -/
theorem z180K18M12_pairPhaseSum_singleton
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (c0 : ZMod 5) (r0 : ZMod 9)
    (hsingleton : z180K18M12PairLevelFiber p c0 = {r0}) :
    z180K18M12PairPhaseSum p c0 =
      z180K18M12PhaseChar (z180K18M12PairPhase p r0) := by
  simp [z180K18M12PairPhaseSum, hsingleton]

/-- Multiplication by the common shift takes the normalized phase sum back to
the raw phase sum. -/
theorem z180K18M12_shift_mul_normalizedPhaseSum
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (c : ZMod 5) :
    z180K18M12PhaseChar shift *
        z180K18M12NormalizedPhaseSum p shift c =
      z180K18M12PairPhaseSum p c := by
  rw [z180K18M12NormalizedPhaseSum, z180K18M12PairPhaseSum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact z180K18M12PhaseChar_shift_mul_normalized p shift r

/-- Evaluation of the normalized count polynomial is exactly the normalized
phase-character sum. -/
theorem z180K18M12_aeval_normalizedPhasePolynomial
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (c : ZMod 5) :
    Polynomial.aeval z180K18M12Root
        (z180K18M12NormalizedPhasePolynomial p shift c) =
      z180K18M12NormalizedPhaseSum p shift c := by
  classical
  have hterm : ∀ q : ZMod 12,
      (((z180K18M12NormalizedPhaseCount p shift c q : Int) : ℂ) *
          z180K18M12Root ^ q.val) =
        ∑ r ∈ z180K18M12NormalizedPhaseFiber p shift c q,
          z180K18M12PhaseChar
            (z180K18M12NormalizedPairPhase p shift r) := by
    intro q
    have hq : (q.val : ZMod 12) = q := ZMod.natCast_zmod_val q
    calc
      (((z180K18M12NormalizedPhaseCount p shift c q : Int) : ℂ) *
          z180K18M12Root ^ q.val) =
          ((z180K18M12NormalizedPhaseFiber p shift c q).card : ℂ) *
            z180K18M12PhaseChar q := by
        rw [z180K18M12PhaseChar_apply]
        change
          ((((z180K18M12NormalizedPhaseFiber p shift c
            (q.val : ZMod 12)).card : Int) : ℂ) *
              z180K18M12Root ^ q.val) =
            ((z180K18M12NormalizedPhaseFiber p shift c q).card : ℂ) *
              z180K18M12Root ^ q.val
        rw [hq]
        norm_num
      _ = ∑ r ∈ z180K18M12NormalizedPhaseFiber p shift c q,
          z180K18M12PhaseChar q := by
        simp
      _ = ∑ r ∈ z180K18M12NormalizedPhaseFiber p shift c q,
          z180K18M12PhaseChar
            (z180K18M12NormalizedPairPhase p shift r) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hphase := (Finset.mem_filter.mp hr).2
        rw [hphase]
  calc
    Polynomial.aeval z180K18M12Root
        (z180K18M12NormalizedPhasePolynomial p shift c) =
        ∑ q : ZMod 12,
          (((z180K18M12NormalizedPhaseCount p shift c q : Int) : ℂ) *
            z180K18M12Root ^ q.val) := by
      simp [z180K18M12NormalizedPhasePolynomial,
        Polynomial.aeval_monomial]
      apply Finset.sum_congr rfl
      intro q hq
      rfl
    _ = ∑ q : ZMod 12,
        ∑ r ∈ z180K18M12NormalizedPhaseFiber p shift c q,
          z180K18M12PhaseChar
            (z180K18M12NormalizedPairPhase p shift r) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hterm q
    _ = z180K18M12NormalizedPhaseSum p shift c := by
      have hfiber := Finset.sum_fiberwise_eq_sum_filter
        (z180K18M12PairLevelFiber p c)
        (Finset.univ : Finset (ZMod 12))
        (z180K18M12NormalizedPairPhase p shift)
        (fun r => z180K18M12PhaseChar
          (z180K18M12NormalizedPairPhase p shift r))
      simpa [z180K18M12NormalizedPhaseFiber,
        z180K18M12NormalizedPhaseSum] using hfiber

#print axioms z180K18M12_fiveLevelFourierSum_eq_pairWeights
#print axioms z180K18M12_fiveLevelFourierSum_factor
#print axioms z180K18M12_aeval_normalizedPhasePolynomial

end Fuglede
