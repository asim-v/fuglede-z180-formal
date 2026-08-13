import Fuglede.Z180Phi5K10TypedAdapter
import Fuglede.Z180ProjectionTiles
import Fuglede.Z180SmallCardinality
import Mathlib.Tactic

/-!
# The structural beginning of the `|S| = 2 * 5` case in `ZMod 180`

This module formalizes the unconditional part of the `pr || |S|` argument
from FKMS, Section 3.3, specialized to `(p,q,r) = (2,3,5)`.

The order-five gateway is supplied by `Z180Phi5K10TypedAdapter`.  Since
three does not divide ten, spectral duality makes reduction modulo twenty
injective on both sides of the spectral pair.  The vanishing order-five
Ramanujan transform then says that every residue modulo five occurs exactly
twice.

The final theorem records the first tiling endpoint in the FKMS case split:
if the resulting set is a transversal modulo ten, it tiles by the kernel of
that projection.  No finite-field cyclotomic reduction is assumed here.
-/

namespace Fuglede

open scoped BigOperators

/-- Fixed reduction homomorphism from `ZMod 180` to `ZMod 20`. -/
def z180K10Projection20 : ZMod 180 →+ ZMod 20 :=
  (ZMod.castHom (by norm_num : 20 ∣ 180) (ZMod 20)).toAddMonoidHom

/-- The fifth CRT coordinate space; its modulus is definitionally the third
entry `5` of `crt180Modulus`. -/
abbrev Z180K10FifthCoordinateSpace := ZMod (crt180Modulus 2)

/-- The fifth CRT coordinate, i.e. ordinary reduction modulo five. -/
noncomputable def z180K10FifthCoordinate
    (x : ZMod 180) : Z180K10FifthCoordinateSpace :=
  toCRT180 x 2

@[simp]
theorem z180K10FifthCoordinate_sub (x y : ZMod 180) :
    z180K10FifthCoordinate (x - y) =
      z180K10FifthCoordinate x - z180K10FifthCoordinate y := by
  exact congrFun (toCRT180_sub x y) 2

/-- Occupancy of a residue class modulo five. -/
noncomputable def z180K10FifthOccupancy
    (X : Finset (ZMod 180)) (c : Z180K10FifthCoordinateSpace) : Nat :=
  (X.filter fun x => z180K10FifthCoordinate x = c).card

/-- The five occupancies sum to the cardinality of the set. -/
theorem sum_z180K10FifthOccupancy (X : Finset (ZMod 180)) :
    (∑ c : Z180K10FifthCoordinateSpace,
      z180K10FifthOccupancy X c) = X.card := by
  classical
  simpa [z180K10FifthOccupancy] using
    (Finset.sum_card_fiberwise_eq_card_filter X
      (Finset.univ : Finset Z180K10FifthCoordinateSpace)
      z180K10FifthCoordinate)

private theorem zmod5_frequencyOrder_eq_one_or_five
    (z : Z180K10FifthCoordinateSpace) :
    frequencyOrder (crt180Modulus 2) z = if z = 0 then 1 else 5 := by
  revert z
  decide

/-- Two residues have the same fifth coordinate exactly when the order-five
Ramanujan coefficient of their difference is `4` (and otherwise it is
`-1`). -/
theorem z180RamanujanCoeff_five_difference (x y : ZMod 180) :
    z180RamanujanCoeff 5 (frequencyOrder 180 (x - y)) =
      if z180K10FifthCoordinate x = z180K10FifthCoordinate y then 4 else -1 := by
  let d : CRT180 := toCRT180 (x - y)
  let r : Nat := frequencyOrder 180 (x - y)
  let z : Z180K10FifthCoordinateSpace := d 2
  have hr : r ∈ (180).divisors :=
    Nat.mem_divisors.mpr
      ⟨frequencyOrder_dvd_modulus (x - y), by norm_num⟩
  have hglobal : frequencyOrder 180 (fromCRT180 d) = r := by
    change frequencyOrder 180 (fromCRT180 (toCRT180 (x - y))) =
      frequencyOrder 180 (x - y)
    rw [fromCRT180_toCRT180]
  have hlocal :=
    (frequencyOrder_fromCRT180_eq_iff_local (d := d) hr).mp hglobal
  have hfive := hlocal 2
  have hgcd : Nat.gcd r (crt180Modulus 2) =
      frequencyOrder (crt180Modulus 2) z := by
    simpa only [z, crt180OrderPart] using hfive.symm
  by_cases hxy : z180K10FifthCoordinate x = z180K10FifthCoordinate y
  · rw [if_pos hxy]
    have hdiff : z = 0 := by
      change z180K10FifthCoordinate (x - y) = 0
      rw [z180K10FifthCoordinate_sub, hxy, sub_self]
    have hlocalOrder :
        frequencyOrder (crt180Modulus 2) z = 1 := by
      rw [zmod5_frequencyOrder_eq_one_or_five, if_pos hdiff]
    have hgcdOneLocal : Nat.gcd r (crt180Modulus 2) = 1 :=
      hgcd.trans hlocalOrder
    have hgcdOne : Nat.gcd r 5 = 1 := by
      simpa only [crt180Modulus_two] using hgcdOneLocal
    norm_num [z180RamanujanCoeff, z180RamanujanFour,
      z180RamanujanNine, z180RamanujanFive, r, hgcdOne]
  · rw [if_neg hxy]
    have hdiff : z ≠ 0 := by
      intro hd
      apply hxy
      have hd' : z180K10FifthCoordinate (x - y) = 0 := by
        simpa only [z, d, z180K10FifthCoordinate] using hd
      apply sub_eq_zero.mp
      rw [← z180K10FifthCoordinate_sub]
      exact hd'
    have hlocalOrder :
        frequencyOrder (crt180Modulus 2) z = 5 := by
      rw [zmod5_frequencyOrder_eq_one_or_five, if_neg hdiff]
    have hgcdFiveLocal : Nat.gcd r (crt180Modulus 2) = 5 :=
      hgcd.trans hlocalOrder
    have hgcdFive : Nat.gcd r 5 = 5 := by
      simpa only [crt180Modulus_two] using hgcdFiveLocal
    norm_num [z180RamanujanCoeff, z180RamanujanFour,
      z180RamanujanNine, z180RamanujanFive, r, hgcdFive]

/-- The second moment of the five occupancies counts ordered pairs with the
same residue modulo five. -/
theorem sum_z180K10FifthOccupancy_sq (X : Finset (ZMod 180)) :
    (∑ c : Z180K10FifthCoordinateSpace,
      z180K10FifthOccupancy X c ^ 2) =
      ((X ×ˢ X).filter fun p =>
        z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2).card := by
  classical
  let P := (X ×ˢ X).filter fun p =>
    z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := P)
    (t := (Finset.univ : Finset Z180K10FifthCoordinateSpace))
    (f := fun p => z180K10FifthCoordinate p.1)
    (by simp [P])
  rw [show ((X ×ˢ X).filter fun p =>
      z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2) = P from rfl]
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro c _
  rw [z180K10FifthOccupancy, pow_two]
  have hfilter :
      P.filter (fun p => z180K10FifthCoordinate p.1 = c) =
        (X.filter fun x => z180K10FifthCoordinate x = c) ×ˢ
          (X.filter fun x => z180K10FifthCoordinate x = c) := by
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_product]
    aesop
  rw [hfilter, Finset.card_product]

/-- At order five, the exact transform is five times the same-fibre pair
count minus the total number of ordered pairs. -/
theorem z180ExactOrderTransform_five_eq_fiber_second_moment
    (X : Finset (ZMod 180)) :
    z180ExactOrderTransform X 5 =
      5 * (∑ c : Z180K10FifthCoordinateSpace,
        (z180K10FifthOccupancy X c : Int) ^ 2) -
        (X.card : Int) ^ 2 := by
  classical
  rw [z180ExactOrderTransform_eq_pairKernelSum X (by norm_num)]
  rw [z180PairKernelSum]
  simp_rw [z180RamanujanCoeff_five_difference]
  let P := (X ×ˢ X).filter fun p =>
    z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2
  let Q := (X ×ˢ X).filter fun p =>
    ¬z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2
  have hpartition : P ∪ Q = X ×ˢ X := by
    ext p
    simp only [P, Q, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product]
    tauto
  have hdisjoint : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hp).2
  have hsumSplit :
      (∑ p ∈ X ×ˢ X,
          if z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2
          then (4 : Int) else -1) =
        4 * P.card - Q.card := by
    calc
      (∑ p ∈ X ×ˢ X,
          if z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2
          then (4 : Int) else -1) =
          (∑ p ∈ P,
            if z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2
            then (4 : Int) else -1) +
          (∑ p ∈ Q,
            if z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2
            then (4 : Int) else -1) := by
        rw [← hpartition, Finset.sum_union hdisjoint]
      _ = 4 * P.card - Q.card := by
        have hPtrue : ∀ p ∈ P,
            z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2 := by
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        have hQfalse : ∀ p ∈ Q,
            ¬z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2 := by
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        have hsumP :
            (∑ p ∈ P,
              if z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2
              then (4 : Int) else -1) = 4 * P.card := by
          calc
            _ = ∑ _p ∈ P, (4 : Int) := by
              apply Finset.sum_congr rfl
              intro p hp
              simp [hPtrue p hp]
            _ = 4 * P.card := by simp [mul_comm]
        have hsumQ :
            (∑ p ∈ Q,
              if z180K10FifthCoordinate p.1 = z180K10FifthCoordinate p.2
              then (4 : Int) else -1) = -(Q.card : Int) := by
          calc
            _ = ∑ _p ∈ Q, (-1 : Int) := by
              apply Finset.sum_congr rfl
              intro p hp
              simp [hQfalse p hp]
            _ = -(Q.card : Int) := by simp
        rw [hsumP, hsumQ]
        ring
  rw [hsumSplit]
  have hcardSplit : P.card + Q.card = (X ×ˢ X).card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hpartition]
  have hP : P.card =
      ∑ c : Z180K10FifthCoordinateSpace,
        z180K10FifthOccupancy X c ^ 2 := by
    simpa [P] using (sum_z180K10FifthOccupancy_sq X).symm
  have hprod : (X ×ˢ X).card = X.card ^ 2 := by
    simp [pow_two]
  rw [hP] at hcardSplit
  rw [hprod] at hcardSplit
  nlinarith

/-- The order-five cyclotomic gateway at the representative frequency `36`
forces the entire order-five Fourier orbit, and hence the exact transform,
to vanish. -/
theorem z180ExactOrderTransform_five_eq_zero_of_cyclotomicZero36
    {X : Finset (ZMod 180)}
    (hzero : CyclotomicZero 180 X 36) :
    z180ExactOrderTransform X 5 = 0 := by
  have horder36 : frequencyOrder 180 (36 : ZMod 180) = 5 := by
    decide
  have horbit : ∀ d : ZMod 180,
      frequencyOrder 180 d = 5 → CyclotomicZero 180 X d := by
    intro d hd
    simpa [CyclotomicZero, hd, horder36] using hzero
  have henergy : exactOrderFourierEnergy X 5 = 0 :=
    (exactOrderFourierEnergy_eq_zero_iff_cyclotomicZero X 5).2 horbit
  exact z180ExactOrderTransform_eq_zero_of_fourierEnergy_eq_zero
    (z180RamanujanIdentity_all X) (by norm_num) henergy

/-- A zero order-five transform at cardinality ten forces exactly two points
in every residue class modulo five. -/
theorem z180K10FifthOccupancy_eq_two_of_transform_zero
    {X : Finset (ZMod 180)}
    (hcard : X.card = 10)
    (hzero : z180ExactOrderTransform X 5 = 0) :
    ∀ c : Z180K10FifthCoordinateSpace,
      z180K10FifthOccupancy X c = 2 := by
  have hsum := sum_z180K10FifthOccupancy X
  have hmoment := z180ExactOrderTransform_five_eq_fiber_second_moment X
  rw [hcard] at hsum hmoment
  rw [hzero] at hmoment
  norm_num at hmoment
  have hsumInt :
      (∑ c : Z180K10FifthCoordinateSpace,
        (z180K10FifthOccupancy X c : Int)) = 10 := by
    exact_mod_cast hsum
  have hmomentInt :
      (∑ c : Z180K10FifthCoordinateSpace,
        (z180K10FifthOccupancy X c : Int) ^ 2) = 20 := by
    nlinarith
  have hsquare (n : Int) : (n - 2) ^ 2 = n ^ 2 - 4 * n + 4 := by
    ring
  have hdeviation :
      (∑ c : Z180K10FifthCoordinateSpace,
        ((z180K10FifthOccupancy X c : Int) - 2) ^ 2) = 0 := by
    calc
      _ = (∑ c : Z180K10FifthCoordinateSpace,
            (z180K10FifthOccupancy X c : Int) ^ 2) -
          4 * (∑ c : Z180K10FifthCoordinateSpace,
            (z180K10FifthOccupancy X c : Int)) + 20 := by
        simp_rw [hsquare]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp [Finset.mul_sum, Z180K10FifthCoordinateSpace,
          crt180Modulus]
      _ = 0 := by rw [hmomentInt, hsumInt]; norm_num
  intro c
  have hallSquares :
      (fun c : Z180K10FifthCoordinateSpace =>
        ((z180K10FifthOccupancy X c : Int) - 2) ^ 2) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun c : Z180K10FifthCoordinateSpace => sq_nonneg
        ((z180K10FifthOccupancy X c : Int) - 2))).mp hdeviation
  have hcsquare :
      ((z180K10FifthOccupancy X c : Int) - 2) ^ 2 = 0 := by
    simpa using congrFun hallSquares c
  have hcInt : (z180K10FifthOccupancy X c : Int) = 2 := by
    nlinarith
  exact_mod_cast hcInt

/-- Direct cyclotomic form of the balanced-fibre conclusion used by FKMS. -/
theorem z180K10FifthOccupancy_eq_two_of_cyclotomicZero36
    {X : Finset (ZMod 180)}
    (hcard : X.card = 10)
    (hzero : CyclotomicZero 180 X 36) :
    ∀ c : Z180K10FifthCoordinateSpace,
      z180K10FifthOccupancy X c = 2 := by
  exact z180K10FifthOccupancy_eq_two_of_transform_zero hcard
    (z180ExactOrderTransform_five_eq_zero_of_cyclotomicZero36 hzero)

/-- A nonzero collision in reduction modulo twenty has frequency order three
or nine. -/
theorem z180K10_frequencyOrder_three_or_nine_of_cast20_eq
    (x y : ZMod 180) (hxy : x ≠ y)
    (hcast : z180K10Projection20 x = z180K10Projection20 y) :
    frequencyOrder 180 (x - y) = 3 ∨
      frequencyOrder 180 (x - y) = 9 := by
  have hcastZero : z180K10Projection20 (x - y) = 0 := by
    rw [map_sub, hcast, sub_self]
  have hnatCastZero : ((x - y).val : ZMod 20) = 0 := by
    change ((x - y).val : ZMod 20) = 0 at hcastZero
    exact hcastZero
  have hdvd : 20 ∣ (x - y).val :=
    (ZMod.natCast_eq_zero_iff (x - y).val 20).1 hnatCastZero
  obtain ⟨k, hk⟩ := hdvd
  have hvalne : (x - y).val ≠ 0 := by
    intro hzero
    have hdiff : x - y = 0 := (ZMod.val_eq_zero (x - y)).1 hzero
    exact hxy (sub_eq_zero.mp hdiff)
  have hkpos : 0 < k := by omega
  have hklt : k < 9 := by
    have hvalLt := (x - y).val_lt
    omega
  unfold frequencyOrder
  rw [hk]
  interval_cases k <;> norm_num at hkpos ⊢

/-- Reduction modulo twenty is injective on a cardinality-ten spectral set.
This is the projection step at the start of the FKMS `pr` case. -/
theorem z180_k10_projection20_injOn_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 10) :
    Set.InjOn z180K10Projection20
      (A : Set (ZMod 180)) := by
  intro x hx y hy hcast
  by_contra hxy
  have hzero : CyclotomicZero 180 L (x - y) :=
    (cyclotomicSpectrum_dual hSpec).2.2 x hx y hy hxy
  have hdivL : 3 ∣ L.card := by
    rcases z180K10_frequencyOrder_three_or_nine_of_cast20_eq x y hxy hcast
      with hthree | hnine
    · exact prime_dvd_card_of_cyclotomicZero
        (by norm_num) L (x - y) hthree hzero
    · apply prime_dvd_card_of_prime_pow_cyclotomic_dvd_mask
        (p := 3) (N := 180) (by norm_num) 1 L
      simpa [CyclotomicZero, hnine] using hzero
  have hdivA : 3 ∣ A.card := by simpa [hSpec.2.1] using hdivL
  omega

/-- Both members of the spectral pair satisfy the unconditional FKMS
gateway: injectivity modulo twenty and two points in every fifth-coordinate
fibre. -/
theorem z180_k10_fkms_pr_gateway
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 10) :
    Set.InjOn z180K10Projection20
        (A : Set (ZMod 180)) ∧
      Set.InjOn z180K10Projection20
        (L : Set (ZMod 180)) ∧
      (∀ c : Z180K10FifthCoordinateSpace,
        z180K10FifthOccupancy A c = 2) ∧
      (∀ c : Z180K10FifthCoordinateSpace,
        z180K10FifthOccupancy L c = 2) := by
  have hcardL : L.card = 10 := hSpec.2.1.symm.trans hcard
  obtain ⟨hzeroA, hzeroL⟩ :=
    z180_phi5_k10_both_cyclotomic_zero hSpec hcard
  exact ⟨z180_k10_projection20_injOn_of_spectral hSpec hcard,
    z180_k10_projection20_injOn_of_spectral
      (cyclotomicSpectrum_dual hSpec) hcardL,
    z180K10FifthOccupancy_eq_two_of_cyclotomicZero36 hcard hzeroA,
    z180K10FifthOccupancy_eq_two_of_cyclotomicZero36 hcardL hzeroL⟩

/-- Narrow conditional bridge for the unresolved finite-field part of the
FKMS argument.  Once the injective projection of `A` to `ZMod 20` is shown
to tile there, that tiling lifts through reduction modulo twenty. -/
theorem z180_k10_exists_tiling_of_projection20_image_tile
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 10)
    (himage : ∃ C : Finset (ZMod 20),
      Tiles (A.image z180K10Projection20) C) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  have hsurj : Function.Surjective z180K10Projection20 := by
    simpa [z180K10Projection20] using
      ZMod.castHom_surjective (by norm_num : 20 ∣ 180)
  have hinj := z180_k10_projection20_injOn_of_spectral hSpec hcard
  obtain ⟨C, hC⟩ := himage
  exact ⟨preimageFinset z180K10Projection20 C,
    lift_tiles_of_surjective z180K10Projection20 hsurj A C hinj hC⟩

/-- The transversal endpoint of the FKMS `pr` split: injectivity modulo ten
immediately gives an explicit tiling complement, namely the projection
kernel. -/
theorem z180_k10_tiles_projection10_kernel
    {A : Finset (ZMod 180)} (hcard : A.card = 10)
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 10))
      (A : Set (ZMod 180))) :
    Tiles A (kernelFinset
      (ZMod.castHom (by norm_num : 10 ∣ 180) (ZMod 10)).toAddMonoidHom) := by
  let phi : ZMod 180 →+ ZMod 10 :=
    (ZMod.castHom (by norm_num : 10 ∣ 180) (ZMod 10)).toAddMonoidHom
  apply transversal_tiles_kernel phi A
  · apply (kernel_difference_free_iff_injOn phi A).2
    intro x hx y hy hmap
    apply hinj hx hy
    simpa [phi, ZMod.castHom_apply] using hmap
  · simpa [ZMod.card] using hcard

/-- Existential form of the first (transversal) endpoint in the FKMS local
case split. -/
theorem z180_k10_exists_tiling_of_projection10_injOn
    {A : Finset (ZMod 180)} (hcard : A.card = 10)
    (hinj : Set.InjOn (fun x : ZMod 180 => (ZMod.cast x : ZMod 10))
      (A : Set (ZMod 180))) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  exact ⟨kernelFinset
      (ZMod.castHom (by norm_num : 10 ∣ 180) (ZMod 10)).toAddMonoidHom,
    z180_k10_tiles_projection10_kernel hcard hinj⟩

#print axioms z180_k10_fkms_pr_gateway
#print axioms z180_k10_exists_tiling_of_projection20_image_tile
#print axioms z180_k10_exists_tiling_of_projection10_injOn

end Fuglede
