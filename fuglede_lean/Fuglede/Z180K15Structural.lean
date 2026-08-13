import Fuglede.Z180K10Structural
import Fuglede.Z180Phi5K15TypedAdapter
import Mathlib.Tactic

/-!
# The structural beginning of the `|S| = 3 * 5` case in `ZMod 180`

This module formalizes the unconditional gateway of the `qr || |S|` case
from FKMS, Section 3.3, after interchanging the paper's primes `p` and `q`.
For `180 = 2^2 * 3^2 * 5`, the relevant projection is
`ZMod 180 -> ZMod (3^2 * 5) = ZMod 45`.

The sealed order-five certificate makes every residue modulo five occur
exactly three times.  Since two does not divide fifteen, spectral duality
makes the projection modulo forty-five injective on both sides of the
spectral pair.

The remaining FKMS argument uses cyclotomic reduction over `F_2` and an
induction step for sets or spectra contained in a proper subgroup.  Those
ingredients are not assumed here.  Instead, the final theorems expose the
two exact tiling interfaces needed after that descent: tiling of the
projected image lifts to `ZMod 180`, and injectivity modulo fifteen gives the
explicit projection-kernel complement.
-/

namespace Fuglede

open scoped BigOperators

/-- Fixed reduction homomorphism from `ZMod 180` to `ZMod 45`. -/
def z180K15Projection45 : ZMod 180 →+ ZMod 45 :=
  (ZMod.castHom (by norm_num : 45 ∣ 180) (ZMod 45)).toAddMonoidHom

/-- The fifth-coordinate space, renamed for the cardinality-fifteen case. -/
abbrev Z180K15FifthCoordinateSpace := Z180K10FifthCoordinateSpace

/-- Occupancy of a residue class modulo five. -/
noncomputable abbrev z180K15FifthOccupancy
    (X : Finset (ZMod 180)) (c : Z180K15FifthCoordinateSpace) : Nat :=
  z180K10FifthOccupancy X c

/-- A zero order-five transform at cardinality fifteen forces exactly three
points in every residue class modulo five. -/
theorem z180K15FifthOccupancy_eq_three_of_transform_zero
    {X : Finset (ZMod 180)}
    (hcard : X.card = 15)
    (hzero : z180ExactOrderTransform X 5 = 0) :
    ∀ c : Z180K15FifthCoordinateSpace,
      z180K15FifthOccupancy X c = 3 := by
  have hsum := sum_z180K10FifthOccupancy X
  have hmoment := z180ExactOrderTransform_five_eq_fiber_second_moment X
  rw [hcard] at hsum hmoment
  rw [hzero] at hmoment
  norm_num at hmoment
  have hsumInt :
      (∑ c : Z180K10FifthCoordinateSpace,
        (z180K10FifthOccupancy X c : Int)) = 15 := by
    exact_mod_cast hsum
  have hmomentInt :
      (∑ c : Z180K10FifthCoordinateSpace,
        (z180K10FifthOccupancy X c : Int) ^ 2) = 45 := by
    nlinarith
  have hsquare (n : Int) : (n - 3) ^ 2 = n ^ 2 - 6 * n + 9 := by
    ring
  have hdeviation :
      (∑ c : Z180K10FifthCoordinateSpace,
        ((z180K10FifthOccupancy X c : Int) - 3) ^ 2) = 0 := by
    calc
      _ = (∑ c : Z180K10FifthCoordinateSpace,
            (z180K10FifthOccupancy X c : Int) ^ 2) -
          6 * (∑ c : Z180K10FifthCoordinateSpace,
            (z180K10FifthOccupancy X c : Int)) + 45 := by
        simp_rw [hsquare]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp [Finset.mul_sum, Z180K10FifthCoordinateSpace,
          crt180Modulus]
      _ = 0 := by rw [hmomentInt, hsumInt]; norm_num
  intro c
  have hallSquares :
      (fun c : Z180K10FifthCoordinateSpace =>
        ((z180K10FifthOccupancy X c : Int) - 3) ^ 2) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun c : Z180K10FifthCoordinateSpace => sq_nonneg
        ((z180K10FifthOccupancy X c : Int) - 3))).mp hdeviation
  have hcsquare :
      ((z180K10FifthOccupancy X c : Int) - 3) ^ 2 = 0 := by
    simpa using congrFun hallSquares c
  have hcInt : (z180K10FifthOccupancy X c : Int) = 3 := by
    nlinarith
  exact_mod_cast hcInt

/-- Direct cyclotomic form of the balanced-fibre conclusion used by FKMS. -/
theorem z180K15FifthOccupancy_eq_three_of_cyclotomicZero36
    {X : Finset (ZMod 180)}
    (hcard : X.card = 15)
    (hzero : CyclotomicZero 180 X 36) :
    ∀ c : Z180K15FifthCoordinateSpace,
      z180K15FifthOccupancy X c = 3 := by
  exact z180K15FifthOccupancy_eq_three_of_transform_zero hcard
    (z180ExactOrderTransform_five_eq_zero_of_cyclotomicZero36 hzero)

/-- Reduction modulo forty-five is injective on a cardinality-fifteen
spectral set.  A collision would have order two or four, forcing two to
divide the cardinality of the dual set. -/
theorem z180_k15_projection45_injOn_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15) :
    Set.InjOn z180K15Projection45 (A : Set (ZMod 180)) := by
  intro x hx y hy hcast
  by_contra hxy
  have hzero : CyclotomicZero 180 L (x - y) :=
    (cyclotomicSpectrum_dual hSpec).2.2 x hx y hy hxy
  have hcast' : (ZMod.cast x : ZMod 45) = ZMod.cast y := by
    exact hcast
  have hdivL : 2 ∣ L.card := by
    rcases z180_frequencyOrder_two_or_four_of_cast45_eq x y hxy hcast'
      with htwo | hfour
    · exact prime_dvd_card_of_cyclotomicZero
        (by norm_num) L (x - y) htwo hzero
    · apply prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask
        (p := 2) (N := 180) (by norm_num) 1 L
      simpa [CyclotomicZero, hfour] using hzero
  have hdivA : 2 ∣ A.card := by simpa [hSpec.2.1] using hdivL
  omega

/-- Both members of the spectral pair satisfy the unconditional FKMS `qr`
gateway: injectivity modulo forty-five and three points in every residue
class modulo five. -/
theorem z180_k15_fkms_qr_gateway
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15) :
    Set.InjOn z180K15Projection45 (A : Set (ZMod 180)) ∧
      Set.InjOn z180K15Projection45 (L : Set (ZMod 180)) ∧
      (∀ c : Z180K15FifthCoordinateSpace,
        z180K15FifthOccupancy A c = 3) ∧
      (∀ c : Z180K15FifthCoordinateSpace,
        z180K15FifthOccupancy L c = 3) := by
  have hcardL : L.card = 15 := hSpec.2.1.symm.trans hcard
  obtain ⟨hzeroA, hzeroL⟩ :=
    z180_phi5_k15_both_cyclotomic_zero hSpec hcard
  exact ⟨z180_k15_projection45_injOn_of_spectral hSpec hcard,
    z180_k15_projection45_injOn_of_spectral
      (cyclotomicSpectrum_dual hSpec) hcardL,
    z180K15FifthOccupancy_eq_three_of_cyclotomicZero36 hcard hzeroA,
    z180K15FifthOccupancy_eq_three_of_cyclotomicZero36 hcardL hzeroL⟩

/-- Conditional interface for the unresolved finite-field and subgroup
descent.  Once the injective image of `A` tiles `ZMod 45`, its tiling lifts
through the surjective projection to `ZMod 180`. -/
theorem z180_k15_exists_tiling_of_projection45_image_tile
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (himage : ∃ C : Finset (ZMod 45),
      Tiles (A.image z180K15Projection45) C) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  have hsurj : Function.Surjective z180K15Projection45 := by
    simpa [z180K15Projection45] using
      ZMod.castHom_surjective (by norm_num : 45 ∣ 180)
  have hinj := z180_k15_projection45_injOn_of_spectral hSpec hcard
  obtain ⟨C, hC⟩ := himage
  exact ⟨preimageFinset z180K15Projection45 C,
    lift_tiles_of_surjective z180K15Projection45 hsurj A C hinj hC⟩

/-- The transversal endpoint of the FKMS `qr` split: injectivity modulo
fifteen gives the projection kernel as an explicit tiling complement. -/
theorem z180_k15_tiles_projection15_kernel
    {A : Finset (ZMod 180)} (hcard : A.card = 15)
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 15))
      (A : Set (ZMod 180))) :
    Tiles A (kernelFinset
      (ZMod.castHom (by norm_num : 15 ∣ 180) (ZMod 15)).toAddMonoidHom) := by
  let phi : ZMod 180 →+ ZMod 15 :=
    (ZMod.castHom (by norm_num : 15 ∣ 180) (ZMod 15)).toAddMonoidHom
  apply transversal_tiles_kernel phi A
  · apply (kernel_difference_free_iff_injOn phi A).2
    intro x hx y hy hmap
    apply hinj hx hy
    simpa [phi, ZMod.castHom_apply] using hmap
  · simpa [ZMod.card] using hcard

/-- Existential form of the first unconditional tiling endpoint after the
FKMS local descent. -/
theorem z180_k15_exists_tiling_of_projection15_injOn
    {A : Finset (ZMod 180)} (hcard : A.card = 15)
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 15))
      (A : Set (ZMod 180))) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  exact ⟨kernelFinset
      (ZMod.castHom (by norm_num : 15 ∣ 180) (ZMod 15)).toAddMonoidHom,
    z180_k15_tiles_projection15_kernel hcard hinj⟩

#print axioms z180_k15_fkms_qr_gateway
#print axioms z180_k15_exists_tiling_of_projection45_image_tile
#print axioms z180_k15_exists_tiling_of_projection15_injOn

end Fuglede
