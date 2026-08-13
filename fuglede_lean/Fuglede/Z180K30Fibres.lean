import Fuglede.Z180K10Structural
import Fuglede.Z180Phi5K30TypedAdapter
import Fuglede.Z180FiveLevelFourier
import Mathlib.Tactic

/-!
# The five six-point fibres at cardinality thirty

The order-five certificate balances a cardinality-thirty set evenly over
its five residue classes.  Reducing one fixed residue class modulo `36` is
injective by the Chinese remainder theorem, so each resulting fibre is a
six-point subset of `ZMod 36`.
-/

namespace Fuglede

open scoped BigOperators

/-- Chinese remainder coordinates adapted to the factorisation
`180 = 5 * 36`. -/
noncomputable def z180K30CRT : ZMod 180 ≃+* ZMod 5 × ZMod 36 :=
  ZMod.chineseRemainder (by decide : Nat.Coprime 5 36)

@[simp]
theorem z180K30CRT_apply (x : ZMod 180) :
    z180K30CRT x = ((ZMod.cast x : ZMod 5), (ZMod.cast x : ZMod 36)) := by
  rfl

/-- The reduction modulo `36` is injective after fixing the residue modulo
five. -/
theorem z180_k30_cast36_injective_on_fifth_fibre
    {c : ZMod 5} :
    Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 36))
      {x | (ZMod.cast x : ZMod 5) = c} := by
  intro x hx y hy h36
  apply z180K30CRT.injective
  rw [z180K30CRT_apply, z180K30CRT_apply]
  exact Prod.ext (hx.trans hy.symm) h36

/-- The `c`-th fifth-coordinate fibre, written in its natural `ZMod 36`
coordinate. -/
noncomputable def z180K30Fibre
    (X : Finset (ZMod 180)) (c : ZMod 5) : Finset (ZMod 36) :=
  (X.filter fun x => (ZMod.cast x : ZMod 5) = c).image
    (fun x => (ZMod.cast x : ZMod 36))

/-- The K10 occupancy notation is ordinary reduction modulo five. -/
theorem z180K10FifthCoordinate_eq_cast_five (x : ZMod 180) :
    z180K10FifthCoordinate x = (ZMod.cast x : ZMod 5) := by
  simpa only [z180K10FifthCoordinate, crt180FifthCoord,
    Z180K10FifthCoordinateSpace, crt180Modulus_two] using
    crt180FifthCoord_toCRT180 x

/-- The cardinality-thirty analogue of the already sealed K10/K15 balanced
occupancy lemmas. -/
theorem z180K30FifthOccupancy_eq_six_of_transform_zero
    {X : Finset (ZMod 180)}
    (hcard : X.card = 30)
    (hzero : z180ExactOrderTransform X 5 = 0) :
    ∀ c : Z180K10FifthCoordinateSpace,
      z180K10FifthOccupancy X c = 6 := by
  have hsum := sum_z180K10FifthOccupancy X
  have hmoment := z180ExactOrderTransform_five_eq_fiber_second_moment X
  rw [hcard] at hsum hmoment
  rw [hzero] at hmoment
  norm_num at hmoment
  have hsumInt :
      (∑ c : Z180K10FifthCoordinateSpace,
        (z180K10FifthOccupancy X c : Int)) = 30 := by
    exact_mod_cast hsum
  have hmomentInt :
      (∑ c : Z180K10FifthCoordinateSpace,
        (z180K10FifthOccupancy X c : Int) ^ 2) = 180 := by
    nlinarith
  have hsquare (n : Int) : (n - 6) ^ 2 = n ^ 2 - 12 * n + 36 := by
    ring
  have hdeviation :
      (∑ c : Z180K10FifthCoordinateSpace,
        ((z180K10FifthOccupancy X c : Int) - 6) ^ 2) = 0 := by
    calc
      _ = (∑ c : Z180K10FifthCoordinateSpace,
            (z180K10FifthOccupancy X c : Int) ^ 2) -
          12 * (∑ c : Z180K10FifthCoordinateSpace,
            (z180K10FifthOccupancy X c : Int)) + 180 := by
        simp_rw [hsquare]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp [Finset.mul_sum, Z180K10FifthCoordinateSpace,
          crt180Modulus]
      _ = 0 := by rw [hmomentInt, hsumInt]; norm_num
  intro c
  have hallSquares :
      (fun c : Z180K10FifthCoordinateSpace =>
        ((z180K10FifthOccupancy X c : Int) - 6) ^ 2) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun c : Z180K10FifthCoordinateSpace => sq_nonneg
        ((z180K10FifthOccupancy X c : Int) - 6))).mp hdeviation
  have hcsquare :
      ((z180K10FifthOccupancy X c : Int) - 6) ^ 2 = 0 := by
    simpa using congrFun hallSquares c
  have hcInt : (z180K10FifthOccupancy X c : Int) = 6 := by
    nlinarith
  exact_mod_cast hcInt

/-- Every fifth-coordinate fibre of a cardinality-thirty spectral set has
six elements after reduction modulo `36`. -/
theorem z180_k30_fibre_card_six
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30) :
    ∀ c : ZMod 5, (z180K30Fibre A c).card = 6 := by
  obtain ⟨hzeroA, _hzeroL⟩ := z180_phi5_k30_both_transform_zero hSpec hcard
  have hbalanced := z180K30FifthOccupancy_eq_six_of_transform_zero
    hcard hzeroA
  intro c
  rw [z180K30Fibre, Finset.card_image_iff.mpr]
  · simpa only [z180K10FifthOccupancy, z180K10FifthCoordinate_eq_cast_five,
      Z180K10FifthCoordinateSpace, crt180Modulus_two]
      using hbalanced c
  · intro x hx y hy hxy
    apply z180_k30_cast36_injective_on_fifth_fibre
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hy).2
    · exact hxy

#print axioms z180_k30_cast36_injective_on_fifth_fibre
#print axioms z180K30FifthOccupancy_eq_six_of_transform_zero
#print axioms z180_k30_fibre_card_six

end Fuglede
