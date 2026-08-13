import Fuglede.Z180K18M12PairFibresHighOrder
import Fuglede.Z36Card18PrimePowerFiberCore
import Mathlib.Tactic

/-!
# Finite-set adapters for the `k = 18`, `m = 12` high-order geometry

This module is purely combinatorial.  It identifies the four projection
coordinates above a residue modulo nine, rewrites the signed projection
profile as a signed sum over the corresponding set fibre, and extracts
same fifth level plus order-four difference from a two-point fibre.
-/

namespace Fuglede

open scoped BigOperators

set_option maxHeartbeats 0

/-- The four coordinates in `Fin 36` above one residue modulo nine. -/
def z180K18M12NineFiberIndices (r : ZMod 9) : Finset (Fin 36) :=
  match r.val with
  | 0 => {0, 9, 18, 27}
  | 1 => {1, 10, 19, 28}
  | 2 => {2, 11, 20, 29}
  | 3 => {3, 12, 21, 30}
  | 4 => {4, 13, 22, 31}
  | 5 => {5, 14, 23, 32}
  | 6 => {6, 15, 24, 33}
  | 7 => {7, 16, 25, 34}
  | _ => {8, 17, 26, 35}

@[simp]
theorem mem_z180K18M12NineFiberIndices_iff
    (r : ZMod 9) (i : Fin 36) :
    i ∈ z180K18M12NineFiberIndices r ↔ (i.val : ZMod 9) = r := by
  exact (by decide : ∀ r : ZMod 9, ∀ i : Fin 36,
    i ∈ z180K18M12NineFiberIndices r ↔ (i.val : ZMod 9) = r) r i

theorem sum_z180K18M12NineFiberIndices
    (b : Fin 36 → Int) (r : ZMod 9) :
    (∑ i ∈ z180K18M12NineFiberIndices r, b i) =
      z180K18M12NineFiberMass b r := by
  unfold z180K18M12NineFiberIndices z180K18M12NineFiberMass
  split <;> simp_all <;> ring

private theorem z180Projection36Coordinate_cast_nine (x : ZMod 180) :
    ((z180Projection36Coordinate x).val : ZMod 9) =
      (ZMod.cast x : ZMod 9) := by
  apply ZMod.val_injective
  change (z180Projection36Coordinate x).val % 9 = x.val % 9
  rw [z180Projection36Coordinate_val,
    Nat.mod_mod_of_dvd x.val (by norm_num : 9 ∣ 36)]

@[simp]
theorem z180Projection36Coordinate_mem_nineFiberIndices_iff
    (x : ZMod 180) (r : ZMod 9) :
    z180Projection36Coordinate x ∈ z180K18M12NineFiberIndices r ↔
      (ZMod.cast x : ZMod 9) = r := by
  rw [mem_z180K18M12NineFiberIndices_iff,
    z180Projection36Coordinate_cast_nine]

/-- The four projected occupancies sum to the cardinality of the original
modulo-nine fibre. -/
theorem z180K18M12NineFiberMass_occupancy_eq_filter_card
    (A : Finset (ZMod 180)) (r : ZMod 9) :
    z180K18M12NineFiberMass
        (fun i : Fin 36 => (z180Projection36Occupancy A i : Int)) r =
      ((z180K18M12NineFiber A r).card : Int) := by
  classical
  have hpartition := Finset.sum_card_fiberwise_eq_card_filter A
    (z180K18M12NineFiberIndices r) z180Projection36Coordinate
  have hfilter :
      A.filter (fun x =>
        z180Projection36Coordinate x ∈ z180K18M12NineFiberIndices r) =
        z180K18M12NineFiber A r := by
    apply Finset.filter_congr
    intro x hx
    simpa [z180K18M12NineFiber] using
      z180Projection36Coordinate_mem_nineFiberIndices_iff x r
  rw [hfilter] at hpartition
  have hpartition' :
      (∑ i ∈ z180K18M12NineFiberIndices r,
          z180Projection36Occupancy A i) =
        (z180K18M12NineFiber A r).card := by
    simpa only [z180Projection36Occupancy] using hpartition
  have hcast := congrArg (fun n : Nat => (n : Int)) hpartition'
  push_cast at hcast
  rw [sum_z180K18M12NineFiberIndices] at hcast
  exact hcast

theorem z180_k18_m12_projection_mass_two_of_card_two
    (A : Finset (ZMod 180))
    (htwo : Z180K18M12NineFibresHaveCardTwo A) :
    Z180K18M12ProjectionNineFibresHaveMassTwo A := by
  intro r
  change z180K18M12NineFiberMass
      (fun i : Fin 36 => (z180Projection36Occupancy A i : Int)) r = 2
  rw [z180K18M12NineFiberMass_occupancy_eq_filter_card]
  exact_mod_cast htwo r

/-- Parity sign of one projected coordinate. -/
def z180K18M12ProjectionParitySign (i : Fin 36) : Int :=
  if (i.val : ZMod 2) = 0 then 1 else -1

/-- Parity sign of one original point. -/
def z180K18M12PointParitySign (x : ZMod 180) : Int :=
  if (ZMod.cast x : ZMod 2) = 0 then 1 else -1

private theorem z180Projection36Coordinate_cast_two (x : ZMod 180) :
    ((z180Projection36Coordinate x).val : ZMod 2) =
      (ZMod.cast x : ZMod 2) := by
  apply ZMod.val_injective
  change (z180Projection36Coordinate x).val % 2 = x.val % 2
  rw [z180Projection36Coordinate_val,
    Nat.mod_mod_of_dvd x.val (by norm_num : 2 ∣ 36)]

theorem sum_z180K18M12NineFiberIndices_signed
    (b : Fin 36 → Int) (r : ZMod 9) :
    (∑ i ∈ z180K18M12NineFiberIndices r,
      z180K18M12ProjectionParitySign i * b i) =
        z180K18M12SignedNineFiber b r := by
  unfold z180K18M12NineFiberIndices z180K18M12ProjectionParitySign
  unfold z180K18M12SignedNineFiber
  split <;> simp_all +decide <;> ring

/-- Direct signed count of one fifth-level/modulo-nine fibre. -/
noncomputable def z180K18M12DirectSignedLevelFiber
    (A : Finset (ZMod 180)) (c : ZMod 5) (r : ZMod 9) : Int :=
  ∑ x ∈ A.filter (fun x =>
      (ZMod.cast x : ZMod 5) = c ∧ (ZMod.cast x : ZMod 9) = r),
    z180K18M12PointParitySign x

private theorem sum_projection36_signed_fibre
    (S : Finset (ZMod 180)) (r : ZMod 9) :
    (∑ i ∈ z180K18M12NineFiberIndices r,
      z180K18M12ProjectionParitySign i *
        (z180Projection36Occupancy S i : Int)) =
      ∑ x ∈ S.filter (fun x => (ZMod.cast x : ZMod 9) = r),
        z180K18M12PointParitySign x := by
  classical
  let w : ZMod 180 → Int := z180K18M12PointParitySign
  have hfiber := Finset.sum_fiberwise_eq_sum_filter
    S (z180K18M12NineFiberIndices r) z180Projection36Coordinate w
  have hinner : ∀ i : Fin 36,
      (∑ x ∈ S.filter (fun x => z180Projection36Coordinate x = i), w x) =
        z180K18M12ProjectionParitySign i *
          (z180Projection36Occupancy S i : Int) := by
    intro i
    rw [z180Projection36Occupancy, Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hcoord := (Finset.mem_filter.mp hx).2
    have hsign : w x = z180K18M12ProjectionParitySign i := by
      dsimp only [w, z180K18M12PointParitySign,
        z180K18M12ProjectionParitySign]
      rw [← z180Projection36Coordinate_cast_two x, hcoord]
    rw [hsign]
    ring
  have hleft :
      (∑ i ∈ z180K18M12NineFiberIndices r,
        ∑ x ∈ S.filter (fun x => z180Projection36Coordinate x = i), w x) =
      (∑ i ∈ z180K18M12NineFiberIndices r,
        z180K18M12ProjectionParitySign i *
          (z180Projection36Occupancy S i : Int)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hinner i
  have hfilter :
      S.filter (fun x =>
        z180Projection36Coordinate x ∈ z180K18M12NineFiberIndices r) =
        S.filter (fun x => (ZMod.cast x : ZMod 9) = r) := by
    apply Finset.filter_congr
    intro x hx
    exact z180Projection36Coordinate_mem_nineFiberIndices_iff x r
  rw [hfilter] at hfiber
  rw [← hleft]
  simpa [w] using hfiber

/-- The explicit signed projection profile is the direct signed count of
the corresponding set fibre. -/
theorem z180K18M12SignedNineFiber_levelIndicator_eq_direct
    (A : Finset (ZMod 180)) (c : ZMod 5) (r : ZMod 9) :
    z180K18M12SignedNineFiber (z180K18M12LevelIndicator A c) r =
      z180K18M12DirectSignedLevelFiber A c r := by
  change z180K18M12SignedNineFiber
      (fun i : Fin 36 =>
        (z180Projection36Occupancy (z180K18M12FifthLevel A c) i : Int)) r = _
  rw [← sum_z180K18M12NineFiberIndices_signed]
  rw [sum_projection36_signed_fibre]
  rw [z180K18M12DirectSignedLevelFiber]
  apply Finset.sum_congr
  · ext x
    simp only [z180K18M12FifthLevel, Finset.mem_filter]
    tauto
  · intro x hx
    rfl

/-- An order-two difference in `ZMod 36` is invisible modulo two. -/
theorem z36_cast_two_eq_of_frequencyOrder_two
    {x y : ZMod 36} (horder : frequencyOrder 36 (x - y) = 2) :
    (ZMod.cast x : ZMod 2) = ZMod.cast y := by
  have hkernel : ∀ d : ZMod 36,
      frequencyOrder 36 d = 2 → (ZMod.cast d : ZMod 2) = 0 := by
    decide
  have hzero := hkernel (x - y) horder
  rw [ZMod.cast_sub (by norm_num : 2 ∣ 36), sub_eq_zero] at hzero
  exact hzero

private theorem z180K18Projection36_cast_nine (x : ZMod 180) :
    (ZMod.cast (z180K18Projection36 x) : ZMod 9) =
      (ZMod.cast x : ZMod 9) := by
  rw [z180K18Projection36_apply]
  apply ZMod.val_injective
  change (x.val % 36) % 9 = x.val % 9
  rw [Nat.mod_mod_of_dvd x.val (by norm_num : 9 ∣ 36)]

private theorem z180K18Projection36_cast_two (x : ZMod 180) :
    (ZMod.cast (z180K18Projection36 x) : ZMod 2) =
      (ZMod.cast x : ZMod 2) := by
  rw [z180K18Projection36_apply]
  apply ZMod.val_injective
  change (x.val % 36) % 2 = x.val % 2
  rw [Nat.mod_mod_of_dvd x.val (by norm_num : 2 ∣ 36)]

/-- Zero signed profiles on two-point fibres give the required same-level,
order-four geometry. -/
theorem z180_k18_m12_pairGeometry_of_signed_profiles_zero
    (A : Finset (ZMod 180))
    (hinj : Set.InjOn z180K18Projection36 (A : Set (ZMod 180)))
    (htwo : Z180K18M12NineFibresHaveCardTwo A)
    (hzero : Z180K18M12LevelSignedProfilesZero A) :
    Z180K18M12PairGeometry A := by
  classical
  intro r x hx y hy hxy
  have hpairSubset : ({x, y} : Finset (ZMod 180)) ⊆
      z180K18M12NineFiber A r := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hpairCard : ({x, y} : Finset (ZMod 180)).card = 2 := by
    simp [hxy]
  have hfiber : ({x, y} : Finset (ZMod 180)) =
      z180K18M12NineFiber A r :=
    Finset.eq_of_subset_of_card_le hpairSubset (by rw [htwo r, hpairCard])
  let c : ZMod 5 := ZMod.cast x
  have hdirect : z180K18M12DirectSignedLevelFiber A c r = 0 := by
    rw [← z180K18M12SignedNineFiber_levelIndicator_eq_direct]
    exact hzero c r
  have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
  have hyA : y ∈ A := (Finset.mem_filter.mp hy).1
  have hx9 : (ZMod.cast x : ZMod 9) = r := (Finset.mem_filter.mp hx).2
  have hy9 : (ZMod.cast y : ZMod 9) = r := (Finset.mem_filter.mp hy).2
  have hx5 : (ZMod.cast x : ZMod 5) = c := rfl
  by_cases hy5 : (ZMod.cast y : ZMod 5) = c
  · have hweights :
        z180K18M12PointParitySign x +
          z180K18M12PointParitySign y = 0 := by
      rw [z180K18M12DirectSignedLevelFiber] at hdirect
      have hfilter :
          A.filter (fun z =>
            (ZMod.cast z : ZMod 5) = c ∧ (ZMod.cast z : ZMod 9) = r) =
            {x, y} := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hzA, hz5, hz9⟩
          have hzf : z ∈ z180K18M12NineFiber A r :=
            Finset.mem_filter.mpr ⟨hzA, hz9⟩
          rw [← hfiber] at hzf
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hzf
        · intro hz
          rcases hz with rfl | rfl
          · exact ⟨hxA, hx5, hx9⟩
          · exact ⟨hyA, hy5, hy9⟩
      rw [hfilter] at hdirect
      simpa [hxy] using hdirect
    have hparity : (ZMod.cast x : ZMod 2) ≠ ZMod.cast y := by
      intro heq
      dsimp only [z180K18M12PointParitySign] at hweights
      rw [heq] at hweights
      split at hweights <;> omega
    have hprojNe : z180K18Projection36 x ≠ z180K18Projection36 y := by
      intro h
      exact hxy (hinj hxA hyA h)
    have hproj9 :
        (ZMod.cast (z180K18Projection36 x) : ZMod 9) =
          ZMod.cast (z180K18Projection36 y) := by
      rw [z180K18Projection36_cast_nine,
        z180K18Projection36_cast_nine]
      exact hx9.trans hy9.symm
    have horder := z36_frequencyOrder_two_or_four_of_cast9_eq
      (z180K18Projection36 x) (z180K18Projection36 y) hprojNe hproj9
    refine ⟨hy5.symm, ?_⟩
    rcases horder with htwoOrder | hfourOrder
    · exfalso
      apply hparity
      have hcast := z36_cast_two_eq_of_frequencyOrder_two htwoOrder
      rw [z180K18Projection36_cast_two,
        z180K18Projection36_cast_two] at hcast
      exact hcast
    · exact hfourOrder
  · exfalso
    rw [z180K18M12DirectSignedLevelFiber] at hdirect
    have hfilter :
        A.filter (fun z =>
          (ZMod.cast z : ZMod 5) = c ∧ (ZMod.cast z : ZMod 9) = r) =
          {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hzA, hz5, hz9⟩
        have hzf : z ∈ z180K18M12NineFiber A r :=
          Finset.mem_filter.mpr ⟨hzA, hz9⟩
        rw [← hfiber] at hzf
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzf
        rcases hzf with rfl | rfl
        · rfl
        · exact False.elim (hy5 hz5)
      · rintro rfl
        exact ⟨hxA, hx5, hx9⟩
    rw [hfilter] at hdirect
    simp only [Finset.sum_singleton] at hdirect
    dsimp only [z180K18M12PointParitySign] at hdirect
    split at hdirect <;> omega

/-- Canonical inhabitant of the reduced combinatorial interface. -/
def z180K18M12PairGeometryCombinatorial :
    Z180K18M12PairGeometryCombinatorialInterface where
  projection_mass_two := z180_k18_m12_projection_mass_two_of_card_two
  geometry_of_signed_profiles_zero :=
    z180_k18_m12_pairGeometry_of_signed_profiles_zero

/-- The previously isolated high-order extraction field, now table-free. -/
theorem z180_k18_m12_pairGeometry_of_high_order
    (A : Finset (ZMod 180))
    (hinj : Set.InjOn z180K18Projection36 (A : Set (ZMod 180)))
    (h10 : Polynomial.cyclotomic 10 Int ∣ maskPolynomial 180 A)
    (h30 : Polynomial.cyclotomic 30 Int ∣ maskPolynomial 180 A)
    (h90 : Polynomial.cyclotomic 90 Int ∣ maskPolynomial 180 A)
    (htwo : Z180K18M12NineFibresHaveCardTwo A) :
    Z180K18M12PairGeometry A :=
  z180_k18_m12_pairGeometry_of_high_order_of_combinatorial_interface
    z180K18M12PairGeometryCombinatorial A hinj h10 h30 h90 htwo

#print axioms z180_k18_m12_projection_mass_two_of_card_two
#print axioms z180_k18_m12_pairGeometry_of_signed_profiles_zero
#print axioms z180_k18_m12_pairGeometry_of_high_order

end Fuglede
