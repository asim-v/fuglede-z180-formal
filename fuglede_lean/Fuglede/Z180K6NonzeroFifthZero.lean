import Fuglede.Z180K6Bridge
import Fuglede.Z180K6SetNormalForm
import Mathlib.Tactic

/-!
# The nonzero fifth-coordinate zero branch at cardinality six

In the `Phi_30`/not-`Phi_6` normal form, a cyclotomic zero whose fifth CRT
coordinate is nonzero has exact order `30`.  The proof separates the order
as `5 * m`.  Fourier inversion on the fifth coordinate makes the five base
level sums equal.  The four singleton levels then occupy one residue class
modulo `m`, while the double-level phase equation forces `6 | m`.  Injectivity
of projection to `ZMod 36` and the four-point fibre-capacity lemma force
`m = 6`.
-/

namespace Fuglede

open scoped BigOperators

/-! ## Generic level and phase helpers -/

/-- A singleton fifth fibre contributes its one CRT character at every base
frequency, not only at the distinguished order-six frequency. -/
theorem z180FiveLevelFourierSum_eq_pairing_of_singleton
    (X : Finset (ZMod 180)) (u : CRT180) (c : ZMod 5) (r : ZMod 180)
    (hfiber : z180FifthFiber X c = {r}) :
    z180FiveLevelFourierSum X u c =
      z180StandardCRTCharacterPairing (toCRT180 r) u := by
  have hfiber' :
      X.filter (fun x ↦ crt180FifthCoord (toCRT180 x) = c) = {r} := by
    simpa [z180FifthFiber] using hfiber
  rw [z180FiveLevelFourierSum, hfiber']
  simp

/-- A double fifth fibre contributes the sum of its two CRT characters at
every base frequency. -/
theorem z180FiveLevelFourierSum_eq_pairing_sum_of_pair
    (X : Finset (ZMod 180)) (u : CRT180) (c : ZMod 5)
    (a b : ZMod 180) (hab : a ≠ b)
    (hfiber : z180FifthFiber X c = {a, b}) :
    z180FiveLevelFourierSum X u c =
      z180StandardCRTCharacterPairing (toCRT180 a) u +
        z180StandardCRTCharacterPairing (toCRT180 b) u := by
  have hfiber' :
      X.filter (fun x ↦ crt180FifthCoord (toCRT180 x) = c) = {a, b} := by
    simpa [z180FifthFiber] using hfiber
  rw [z180FiveLevelFourierSum, hfiber']
  simp [hab]

/-- Removing the fifth coordinate leaves a frequency whose order divides
`36`. -/
theorem frequencyOrder_fromCRT180_dvd_thirtySix_of_fifthCoord_eq_zero
    (u : CRT180) (hu : crt180FifthCoord u = 0) :
    frequencyOrder 180 (fromCRT180 u) ∣ 36 := by
  rw [frequencyOrder_fromCRT180_eq_prod]
  simp [Fin.prod_univ_succ]
  have h2 : frequencyOrder 5 (u 2) = 1 := by
    rw [show u 2 = 0 from hu]
    exact (frequencyOrder_eq_one_iff (by norm_num) 0).2 rfl
  rw [h2, mul_one]
  exact Nat.mul_dvd_mul
    (frequencyOrder_dvd_modulus (u 0))
    (frequencyOrder_dvd_modulus (u 1))

/-- Equal base characters imply equality after reduction modulo the exact
order of the base frequency. -/
theorem z180_cast_eq_of_base_pairing_eq
    (u : CRT180) {m : Nat}
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (hm180 : m ∣ 180) {r s : ZMod 180}
    (heq : z180StandardCRTCharacterPairing (toCRT180 r) u =
      z180StandardCRTCharacterPairing (toCRT180 s) u) :
    (ZMod.cast r : ZMod m) = ZMod.cast s := by
  have hmpos : 0 < m := by
    rw [← horder, frequencyOrder_eq_addOrderOf (by norm_num)]
    exact addOrderOf_pos _
  letI : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hchar :
      ZMod.stdAddChar (r * fromCRT180 u) =
        ZMod.stdAddChar (s * fromCRT180 u) := by
    simpa [z180StandardCRTCharacterPairing, fromCRT180_mul, mul_comm]
      using heq
  have hmul : r * fromCRT180 u = s * fromCRT180 u :=
    ZMod.injective_stdAddChar hchar
  have hzero : (r - s) * fromCRT180 u = 0 := by
    rw [sub_mul, hmul, sub_self]
  have hnsmul : (r - s).val • fromCRT180 u = 0 := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact hzero
  have hdvd : m ∣ (r - s).val := by
    have h := (addOrderOf_dvd_iff_nsmul_eq_zero).2 hnsmul
    rw [← frequencyOrder_eq_addOrderOf (by norm_num), horder] at h
    exact h
  have hcastVal : (((r - s).val : Nat) : ZMod m) = 0 := by
    rw [← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hdvd
  have hcastSub : (ZMod.cast (r - s) : ZMod m) = 0 := by
    rw [ZMod.cast_eq_val]
    exact hcastVal
  rw [ZMod.cast_sub hm180] at hcastSub
  exact sub_eq_zero.mp hcastSub

/-- Reduction through `ZMod 36` commutes with reduction to every divisor of
`36`. -/
theorem cast_projection36_eq_cast
    {m : Nat} (hm36 : m ∣ 36) (x : ZMod 180) :
    (ZMod.cast (ZMod.cast x : ZMod 36) : ZMod m) = ZMod.cast x := by
  have hcomp := ZMod.castHom_comp hm36 (by norm_num : 36 ∣ 180)
  exact DFunLike.congr_fun hcomp x

/-- Membership in different fifth fibres separates the underlying points. -/
theorem ne_of_mem_z180FifthFiber_of_ne
    {X : Finset (ZMod 180)} {c c' : ZMod 5} {x y : ZMod 180}
    (hcc' : c ≠ c') (hx : x ∈ z180FifthFiber X c)
    (hy : y ∈ z180FifthFiber X c') : x ≠ y := by
  intro hxy
  subst y
  have hxc := (Finset.mem_filter.mp hx).2
  have hxc' := (Finset.mem_filter.mp hy).2
  exact hcc' (hxc.symm.trans hxc')

/-! ## The exact-order reduction -/

/-- Injection-only core of the nonzero fifth-coordinate branch.  Spectrality
is used by the public wrapper solely to provide `hinj36`. -/
theorem z180_k6_frequencyOrder_eq_thirty_of_phi30_defect_of_injOn
    {X : Finset (ZMod 180)} (hcard : X.card = 6)
    (hinj36 : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (X : Set (ZMod 180)))
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    (h6 : ¬ Polynomial.cyclotomic 6 ℤ ∣ maskPolynomial 180 X)
    {d : ZMod 180} (hzero : CyclotomicZero 180 X d)
    (hd5 : crt180FifthCoord (toCRT180 d) ≠ 0) :
    frequencyOrder 180 d = 30 := by
  classical
  let q : ZMod 5 := crt180FifthCoord (toCRT180 d)
  let u : CRT180 := toCRT180 d - crt180FifthSingle q
  let m : Nat := frequencyOrder 180 (fromCRT180 u)
  have hq : q ≠ 0 := hd5
  have hu : crt180FifthCoord u = 0 := by
    change crt180FifthCoord
      (toCRT180 d - crt180FifthSingle
        (crt180FifthCoord (toCRT180 d))) = 0
    change crt180FifthCoord (toCRT180 d) -
      crt180FifthCoord (crt180FifthSingle
        (crt180FifthCoord (toCRT180 d))) = 0
    simp
  have hrecover : u + crt180FifthSingle q = toCRT180 d := by
    dsimp [u]
    abel
  have hdrepr : d = fromCRT180 (u + crt180FifthSingle q) := by
    rw [hrecover, fromCRT180_toCRT180]
  have hordD : frequencyOrder 180 d = m * 5 := by
    rw [hdrepr]
    exact frequencyOrder_fromCRT180_add_fifth u hu hq
  have hhigh :
      Polynomial.cyclotomic (m * 5) ℤ ∣ maskPolynomial 180 X := by
    unfold CyclotomicZero at hzero
    rwa [hordD] at hzero
  have hlevels : ∀ c c' : ZMod 5,
      z180FiveLevelFourierSum X u c =
        z180FiveLevelFourierSum X u c' := by
    exact z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
      X u m hu rfl hhigh
  have hmpos : 0 < m := by
    dsimp [m]
    rw [frequencyOrder_eq_addOrderOf (by norm_num)]
    exact addOrderOf_pos _
  have hm36 : m ∣ 36 := by
    dsimp [m]
    exact frequencyOrder_fromCRT180_dvd_thirtySix_of_fifthCoord_eq_zero u hu
  have hm180 : m ∣ 180 := hm36.trans (by norm_num)
  obtain ⟨c, a, b, r1, r2, r3, r4, hab, hX, h0, h1, h2, h3, h4,
      hr12base, hr13base, hr14base, hpairBase⟩ :=
    z180_card_six_phi30_defect_set_normal_form_with_support X hcard h30 h6
  have hr1F : r1 ∈ z180FifthFiber X (c + 1) := by rw [h1]; simp
  have hr2F : r2 ∈ z180FifthFiber X (c + 2) := by rw [h2]; simp
  have hr3F : r3 ∈ z180FifthFiber X (c + 3) := by rw [h3]; simp
  have hr4F : r4 ∈ z180FifthFiber X (c + 4) := by rw [h4]; simp
  have hc12 : c + 1 ≠ c + 2 := by fin_cases c <;> decide
  have hc13 : c + 1 ≠ c + 3 := by fin_cases c <;> decide
  have hc14 : c + 1 ≠ c + 4 := by fin_cases c <;> decide
  have hc23 : c + 2 ≠ c + 3 := by fin_cases c <;> decide
  have hc24 : c + 2 ≠ c + 4 := by fin_cases c <;> decide
  have hc34 : c + 3 ≠ c + 4 := by fin_cases c <;> decide
  have hr12 : r1 ≠ r2 := ne_of_mem_z180FifthFiber_of_ne hc12 hr1F hr2F
  have hr13 : r1 ≠ r3 := ne_of_mem_z180FifthFiber_of_ne hc13 hr1F hr3F
  have hr14 : r1 ≠ r4 := ne_of_mem_z180FifthFiber_of_ne hc14 hr1F hr4F
  have hr23 : r2 ≠ r3 := ne_of_mem_z180FifthFiber_of_ne hc23 hr2F hr3F
  have hr24 : r2 ≠ r4 := ne_of_mem_z180FifthFiber_of_ne hc24 hr2F hr4F
  have hr34 : r3 ≠ r4 := ne_of_mem_z180FifthFiber_of_ne hc34 hr3F hr4F
  let T : Finset (ZMod 180) := {r1, r2, r3, r4}
  have hcardT : T.card = 4 := by
    simp [T, hr12, hr13, hr14, hr23, hr24, hr34]
  have hTX : T ⊆ X := by
    intro x hx
    rw [hX]
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  have heq12 :
      z180StandardCRTCharacterPairing (toCRT180 r1) u =
        z180StandardCRTCharacterPairing (toCRT180 r2) u := by
    have h := hlevels (c + 1) (c + 2)
    rwa [z180FiveLevelFourierSum_eq_pairing_of_singleton X u (c + 1) r1 h1,
      z180FiveLevelFourierSum_eq_pairing_of_singleton X u (c + 2) r2 h2] at h
  have heq13 :
      z180StandardCRTCharacterPairing (toCRT180 r1) u =
        z180StandardCRTCharacterPairing (toCRT180 r3) u := by
    have h := hlevels (c + 1) (c + 3)
    rwa [z180FiveLevelFourierSum_eq_pairing_of_singleton X u (c + 1) r1 h1,
      z180FiveLevelFourierSum_eq_pairing_of_singleton X u (c + 3) r3 h3] at h
  have heq14 :
      z180StandardCRTCharacterPairing (toCRT180 r1) u =
        z180StandardCRTCharacterPairing (toCRT180 r4) u := by
    have h := hlevels (c + 1) (c + 4)
    rwa [z180FiveLevelFourierSum_eq_pairing_of_singleton X u (c + 1) r1 h1,
      z180FiveLevelFourierSum_eq_pairing_of_singleton X u (c + 4) r4 h4] at h
  have hcast12 : (ZMod.cast r1 : ZMod m) = ZMod.cast r2 :=
    z180_cast_eq_of_base_pairing_eq u rfl hm180 heq12
  have hcast13 : (ZMod.cast r1 : ZMod m) = ZMod.cast r3 :=
    z180_cast_eq_of_base_pairing_eq u rfl hm180 heq13
  have hcast14 : (ZMod.cast r1 : ZMod m) = ZMod.cast r4 :=
    z180_cast_eq_of_base_pairing_eq u rfl hm180 heq14
  have hdouble :
      z180StandardCRTCharacterPairing (toCRT180 a) u +
          z180StandardCRTCharacterPairing (toCRT180 b) u =
        z180StandardCRTCharacterPairing (toCRT180 r1) u := by
    have h := hlevels c (c + 1)
    rwa [z180FiveLevelFourierSum_eq_pairing_sum_of_pair X u c a b hab h0,
      z180FiveLevelFourierSum_eq_pairing_of_singleton X u (c + 1) r1 h1] at h
  let pa : ℂ := z180StandardCRTCharacterPairing (toCRT180 a) u
  let pb : ℂ := z180StandardCRTCharacterPairing (toCRT180 b) u
  let pr : ℂ := z180StandardCRTCharacterPairing (toCRT180 r1) u
  have hpa : pa * star pa = 1 := by
    simpa [pa, z180StandardCRTCharacterPairing] using
      z180_char_unit (fromCRT180 (u * toCRT180 a))
  have hpb : pb * star pb = 1 := by
    simpa [pb, z180StandardCRTCharacterPairing] using
      z180_char_unit (fromCRT180 (u * toCRT180 b))
  have hpr : pr * star pr = 1 := by
    simpa [pr, z180StandardCRTCharacterPairing] using
      z180_char_unit (fromCRT180 (u * toCRT180 r1))
  have hgeom := unit_pair_sum_unit_ratios_primitive_six hpa hpb hpr
    (by simpa [pa, pb, pr] using hdouble)
  have hratio : pa * star pr =
      z180StandardCRTCharacterPairing (toCRT180 (a - r1)) u := by
    simpa [pa, pr, toCRT180_sub] using
      z180StandardCRTCharacterPairing_mul_star
        (toCRT180 a) (toCRT180 r1) u
  have hprimitive : IsPrimitiveRoot
      (ZMod.stdAddChar ((a - r1) * fromCRT180 u)) 6 := by
    have hpPair : IsPrimitiveRoot
        (z180StandardCRTCharacterPairing (toCRT180 (a - r1)) u) 6 := by
      rw [← hratio]
      exact hgeom.1
    have hfrom :
        fromCRT180 (toCRT180 a - toCRT180 r1) = a - r1 := by
      rw [← toCRT180_sub, fromCRT180_toCRT180]
    simpa [z180StandardCRTCharacterPairing, fromCRT180_mul, hfrom, mul_comm]
      using hpPair
  have hprodOrder :
      frequencyOrder 180 ((a - r1) * fromCRT180 u) = 6 := by
    exact (isPrimitiveRoot_stdAddChar ((a - r1) * fromCRT180 u)).eq_orderOf.trans
      hprimitive.eq_orderOf.symm
  have h6m : 6 ∣ m := by
    have hnsmul : (a - r1).val • fromCRT180 u =
        (a - r1) * fromCRT180 u := by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    have hquot : m / Nat.gcd m (a - r1).val = 6 := by
      have hcalc := addOrderOf_nsmul
        (n := (a - r1).val) (fromCRT180 u)
      have haddProd :
          addOrderOf ((a - r1) * fromCRT180 u) = 6 := by
        rw [← frequencyOrder_eq_addOrderOf (by norm_num)]
        exact hprodOrder
      have haddBase : addOrderOf (fromCRT180 u) = m := by
        rw [← frequencyOrder_eq_addOrderOf (by norm_num)]
      rw [hnsmul, haddProd, haddBase] at hcalc
      exact hcalc.symm
    have hdvd : m / Nat.gcd m (a - r1).val ∣ m :=
      Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m (a - r1).val)
    rwa [hquot] at hdvd
  have hm : m = 6 := by
    let base : ZMod 180 → ZMod 36 := fun x ↦ ZMod.cast x
    let S : Finset (ZMod 36) := T.image base
    have hinjT : Set.InjOn base (T : Set (ZMod 180)) := by
      intro x hx y hy hxy
      exact hinj36 (hTX hx) (hTX hy) hxy
    have hcardS : S.card = 4 := by
      calc
        S.card = T.card := Finset.card_image_of_injOn hinjT
        _ = 4 := hcardT
    apply z180_k6_defect_order_eq_six hmpos hm36 h6m S hcardS
      (ZMod.cast r1)
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx
    · subst x
      exact cast_projection36_eq_cast hm36 r1
    · calc
        (ZMod.cast (base x) : ZMod m) = ZMod.cast x := by
          exact cast_projection36_eq_cast hm36 x
        _ = ZMod.cast r2 := by rw [hx]
        _ = ZMod.cast r1 := hcast12.symm
    · calc
        (ZMod.cast (base x) : ZMod m) = ZMod.cast x := by
          exact cast_projection36_eq_cast hm36 x
        _ = ZMod.cast r3 := by rw [hx]
        _ = ZMod.cast r1 := hcast13.symm
    · calc
        (ZMod.cast (base x) : ZMod m) = ZMod.cast x := by
          exact cast_projection36_eq_cast hm36 x
        _ = ZMod.cast r4 := by rw [hx]
        _ = ZMod.cast r1 := hcast14.symm
  rw [hordD, hm]

/-- Spectral wrapper: projection injectivity is automatic at cardinality
six, so every nonzero-fifth cyclotomic zero in the defect branch has order
exactly `30`. -/
theorem z180_k6_frequencyOrder_eq_thirty_of_phi30_defect
    {X L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 X L) (hcard : X.card = 6)
    (h30 : Polynomial.cyclotomic 30 ℤ ∣ maskPolynomial 180 X)
    (h6 : ¬ Polynomial.cyclotomic 6 ℤ ∣ maskPolynomial 180 X)
    {d : ZMod 180} (hzero : CyclotomicZero 180 X d)
    (hd5 : crt180FifthCoord (toCRT180 d) ≠ 0) :
    frequencyOrder 180 d = 30 := by
  exact z180_k6_frequencyOrder_eq_thirty_of_phi30_defect_of_injOn hcard
    (z180_k6_projection36_injOn_of_spectral hSpec hcard)
    h30 h6 hzero hd5

#print axioms z180_k6_frequencyOrder_eq_thirty_of_phi30_defect_of_injOn
#print axioms z180_k6_frequencyOrder_eq_thirty_of_phi30_defect

end Fuglede
