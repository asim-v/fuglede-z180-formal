import Fuglede.Z180K18M12PairFibres
import Mathlib.Tactic

/-!
# Oriented order-four pairs for the `k = 18`, `m = 12` branch

Every pair supplied by `Z180K18M12PairFibres` has projected difference of
exact order four.  In `ZMod 12` its two phases therefore differ by three.
This module chooses the orientation in which the second phase is the first
phase plus three and records the two finite-coordinate facts needed later:

* the oriented phase still has the pair's residue modulo three;
* subtracting one common phase only rotates those three residue classes.

No Fourier or cyclotomic assertion occurs here.
-/

namespace Fuglede

open scoped BigOperators

/-- The order-twelve phase of one point. -/
def z180K18M12PointPhase (x : ZMod 180) : ZMod 12 :=
  ZMod.cast x

private theorem z180K18Projection36_cast_twelve (x : ZMod 180) :
    (ZMod.cast (z180K18Projection36 x) : ZMod 12) =
      z180K18M12PointPhase x := by
  rw [z180K18Projection36_apply]
  apply ZMod.val_injective
  change (x.val % 36) % 12 = x.val % 12
  rw [Nat.mod_mod_of_dvd x.val (by norm_num : 12 ∣ 36)]

/-- An exact-order-four difference in `ZMod 36` is `+3` in one of the two
orientations after passing to `ZMod 12`. -/
theorem z36_order_four_phase_offset :
    ∀ x y : ZMod 36,
      frequencyOrder 36 (x - y) = 4 →
        (ZMod.cast y : ZMod 12) = ZMod.cast x + 3 ∨
          (ZMod.cast x : ZMod 12) = ZMod.cast y + 3 := by
  exact (by decide)

/-- Point-level form of `z36_order_four_phase_offset`. -/
theorem z180_k18_m12_pair_phase_offset
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    z180K18M12PointPhase (p.second r) =
        z180K18M12PointPhase (p.first r) + 3 ∨
      z180K18M12PointPhase (p.first r) =
        z180K18M12PointPhase (p.second r) + 3 := by
  have h := z36_order_four_phase_offset
    (z180K18Projection36 (p.first r))
    (z180K18Projection36 (p.second r))
    (p.projected_pair_order r)
  simpa only [z180K18Projection36_cast_twelve] using h

/-- First point after orienting the order-four pair by a `+3` phase step. -/
def z180K18M12OrientedFirst
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    ZMod 180 :=
  if z180K18M12PointPhase (p.second r) =
      z180K18M12PointPhase (p.first r) + 3 then
    p.first r
  else
    p.second r

/-- Second point after orienting the order-four pair by a `+3` phase step. -/
def z180K18M12OrientedSecond
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    ZMod 180 :=
  if z180K18M12PointPhase (p.second r) =
      z180K18M12PointPhase (p.first r) + 3 then
    p.second r
  else
    p.first r

/-- The normalized root computation uses the phase of the oriented first
point as the phase attached to the pair. -/
def z180K18M12PairPhase
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    ZMod 12 :=
  z180K18M12PointPhase (z180K18M12OrientedFirst p r)

theorem z180K18M12OrientedSecond_phase
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    z180K18M12PointPhase (z180K18M12OrientedSecond p r) =
      z180K18M12PairPhase p r + 3 := by
  rw [z180K18M12PairPhase]
  unfold z180K18M12OrientedFirst z180K18M12OrientedSecond
  split_ifs with h
  · exact h
  · rcases z180_k18_m12_pair_phase_offset p r with hbad | hgood
    · exact False.elim (h hbad)
    · exact hgood

theorem z180K18M12OrientedFirst_mem
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    z180K18M12OrientedFirst p r ∈ A := by
  unfold z180K18M12OrientedFirst
  split_ifs
  · exact p.first_mem r
  · exact p.second_mem r

theorem z180K18M12OrientedSecond_mem
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    z180K18M12OrientedSecond p r ∈ A := by
  unfold z180K18M12OrientedSecond
  split_ifs
  · exact p.second_mem r
  · exact p.first_mem r

theorem z180K18M12OrientedFirst_level
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    (ZMod.cast (z180K18M12OrientedFirst p r) : ZMod 5) = p.level r := by
  unfold z180K18M12OrientedFirst
  split_ifs
  · exact p.first_level r
  · exact p.second_level r

theorem z180K18M12OrientedSecond_level
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    (ZMod.cast (z180K18M12OrientedSecond p r) : ZMod 5) = p.level r := by
  unfold z180K18M12OrientedSecond
  split_ifs
  · exact p.second_level r
  · exact p.first_level r

private theorem z180_cast_three_through_nine (x : ZMod 180) :
    (ZMod.cast x : ZMod 3) = ZMod.cast (ZMod.cast x : ZMod 9) := by
  apply ZMod.val_injective
  change x.val % 3 = (x.val % 9) % 3
  rw [Nat.mod_mod_of_dvd x.val (by norm_num : 3 ∣ 9)]

private theorem z180_pointPhase_cast_three (x : ZMod 180) :
    (ZMod.cast (z180K18M12PointPhase x) : ZMod 3) = ZMod.cast x := by
  apply ZMod.val_injective
  change (x.val % 12) % 3 = x.val % 3
  rw [Nat.mod_mod_of_dvd x.val (by norm_num : 3 ∣ 12)]

theorem z180K18M12OrientedFirst_cast_nine
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    (ZMod.cast (z180K18M12OrientedFirst p r) : ZMod 9) = r := by
  unfold z180K18M12OrientedFirst
  split_ifs
  · exact p.first_cast_nine r
  · exact p.second_cast_nine r

/-- The chosen phase remembers exactly the residue of the pair modulo three. -/
theorem z180K18M12PairPhase_cast_three
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (r : ZMod 9) :
    (ZMod.cast (z180K18M12PairPhase p r) : ZMod 3) = ZMod.cast r := by
  rw [z180K18M12PairPhase, z180_pointPhase_cast_three,
    z180_cast_three_through_nine, z180K18M12OrientedFirst_cast_nine]

/-- Phase after subtracting the common singleton phase. -/
def z180K18M12NormalizedPairPhase
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (r : ZMod 9) : ZMod 12 :=
  z180K18M12PairPhase p r - shift

theorem z180K18M12NormalizedPairPhase_cast_three
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (r : ZMod 9) :
    (ZMod.cast (z180K18M12NormalizedPairPhase p shift r) : ZMod 3) =
      ZMod.cast r - ZMod.cast shift := by
  rw [z180K18M12NormalizedPairPhase,
    ZMod.cast_sub (by norm_num : 3 ∣ 12),
    z180K18M12PairPhase_cast_three]

/-- The eight phase classes used by the root-parity obstruction. -/
def z180K18M12SelectedPhases : Finset (ZMod 12) :=
  {0, 1, 3, 4, 6, 7, 9, 10}

@[simp]
theorem mem_z180K18M12SelectedPhases_iff (q : ZMod 12) :
    q ∈ z180K18M12SelectedPhases ↔ (ZMod.cast q : ZMod 3) ≠ 2 := by
  fin_cases q <;> decide

/-- Indices of pairs lying in one fifth-coordinate level. -/
def z180K18M12PairLevelFiber
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A) (c : ZMod 5) :
    Finset (ZMod 9) :=
  Finset.univ.filter fun r => p.level r = c

/-- Pairs in one level and one normalized order-twelve phase. -/
def z180K18M12NormalizedPhaseFiber
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (c : ZMod 5) (q : ZMod 12) : Finset (ZMod 9) :=
  (z180K18M12PairLevelFiber p c).filter fun r =>
    z180K18M12NormalizedPairPhase p shift r = q

/-- Integral phase multiplicity in one fifth-coordinate level. -/
def z180K18M12NormalizedPhaseCount
    {A : Finset (ZMod 180)} (p : Z180K18M12PairFibres A)
    (shift : ZMod 12) (c : ZMod 5) (j : Fin 12) : Int :=
  ((z180K18M12NormalizedPhaseFiber p shift c (j.val : ZMod 12)).card : Nat)

#print axioms z36_order_four_phase_offset
#print axioms z180_k18_m12_pair_phase_offset
#print axioms z180K18M12PairPhase_cast_three
#print axioms z180K18M12NormalizedPairPhase_cast_three

end Fuglede
