import Fuglede.Z180K6DescentDefect
import Fuglede.Z180K6NonzeroFifthZero

/-!
# Every five-factor defect at cardinality six has base order six

This is the coordinate-free version of the geometric block used in the
`Phi_30` branch.  A generic `Phi_(5m)`/not-`Phi_m` defect makes all five
fifth-coordinate fibres nonempty.  At cardinality six their profile is
`(2,1,1,1,1)`.  Equality of the five level sums forces the four singleton
base phases to agree, while the double phase produces a primitive sixth
root.  Hence `6 | m`; projection capacity then forces `m = 6`.
-/

namespace Fuglede

open scoped BigOperators
open Polynomial

set_option maxHeartbeats 0

private theorem zmod5_add_one_ne_self_k6_descent (c : ZMod 5) :
    c + 1 ≠ c := by
  fin_cases c <;> decide

private theorem zmod5_add_two_ne_self_k6_descent (c : ZMod 5) :
    c + 2 ≠ c := by
  fin_cases c <;> decide

private theorem zmod5_add_three_ne_self_k6_descent (c : ZMod 5) :
    c + 3 ≠ c := by
  fin_cases c <;> decide

private theorem zmod5_add_four_ne_self_k6_descent (c : ZMod 5) :
    c + 4 ≠ c := by
  fin_cases c <;> decide

/-- Injection-only geometric core: every generic five-factor defect on a
six-point set has base order exactly six. -/
theorem z180_k6_defect_base_order_eq_six_of_injOn
    {X : Finset (ZMod 180)} (hcard : X.card = 6)
    (hinj36 : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (X : Set (ZMod 180)))
    (u : CRT180) (m : Nat)
    (hu : crt180FifthCoord u = 0)
    (horder : frequencyOrder 180 (fromCRT180 u) = m)
    (hhigh : cyclotomic (m * 5) Int ∣ maskPolynomial 180 X)
    (hlow : ¬ cyclotomic m Int ∣ maskPolynomial 180 X) :
    m = 6 := by
  classical
  have hlevels : ∀ c c' : ZMod 5,
      z180FiveLevelFourierSum X u c =
        z180FiveLevelFourierSum X u c' :=
    z180FiveLevelFourierSum_eq_of_cyclotomic_five_mul_order
      X u m hu horder hhigh
  have hnonemptyCRT := z180FiveLevelsNonempty_of_cyclotomic_defect
    X u m hu horder hhigh hlow
  have hnonempty : ∀ c : ZMod 5,
      ∃ x ∈ X, (ZMod.cast x : ZMod 5) = c := by
    intro c
    obtain ⟨x, hx, hxc⟩ := hnonemptyCRT c
    refine ⟨x, hx, ?_⟩
    exact (crt180FifthCoord_toCRT180 x).symm.trans hxc
  obtain ⟨c, hdouble, hsingle⟩ :=
    z180_card_six_fifthFiber_unique_double X hcard hnonempty
  obtain ⟨a, b, hab, h0⟩ :=
    z180FifthFiber_exists_pair_of_card_two X c hdouble
  obtain ⟨r1, h1⟩ := z180FifthFiber_exists_singleton_of_card_one X
    (c + 1) (hsingle _ (zmod5_add_one_ne_self_k6_descent c))
  obtain ⟨r2, h2⟩ := z180FifthFiber_exists_singleton_of_card_one X
    (c + 2) (hsingle _ (zmod5_add_two_ne_self_k6_descent c))
  obtain ⟨r3, h3⟩ := z180FifthFiber_exists_singleton_of_card_one X
    (c + 3) (hsingle _ (zmod5_add_three_ne_self_k6_descent c))
  obtain ⟨r4, h4⟩ := z180FifthFiber_exists_singleton_of_card_one X
    (c + 4) (hsingle _ (zmod5_add_four_ne_self_k6_descent c))
  have hX : X = {a, b, r1, r2, r3, r4} :=
    z180_eq_six_points_of_fifthFibers X c a b r1 r2 r3 r4
      h0 h1 h2 h3 h4
  have hmpos : 0 < m := by
    rw [← horder, frequencyOrder_eq_addOrderOf (by norm_num)]
    exact addOrderOf_pos _
  have hm36 : m ∣ 36 := by
    rw [← horder]
    exact frequencyOrder_fromCRT180_dvd_thirtySix_of_fifthCoord_eq_zero u hu
  have hm180 : m ∣ 180 := hm36.trans (by norm_num)
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
    z180_cast_eq_of_base_pairing_eq u horder hm180 heq12
  have hcast13 : (ZMod.cast r1 : ZMod m) = ZMod.cast r3 :=
    z180_cast_eq_of_base_pairing_eq u horder hm180 heq13
  have hcast14 : (ZMod.cast r1 : ZMod m) = ZMod.cast r4 :=
    z180_cast_eq_of_base_pairing_eq u horder hm180 heq14
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
      have haddProd : addOrderOf ((a - r1) * fromCRT180 u) = 6 := by
        rw [← frequencyOrder_eq_addOrderOf (by norm_num)]
        exact hprodOrder
      have haddBase : addOrderOf (fromCRT180 u) = m := by
        rw [← frequencyOrder_eq_addOrderOf (by norm_num)]
        exact horder
      rw [hnsmul, haddProd, haddBase] at hcalc
      exact hcalc.symm
    have hdvd : m / Nat.gcd m (a - r1).val ∣ m :=
      Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m (a - r1).val)
    rwa [hquot] at hdvd
  let T : Finset (ZMod 180) := {r1, r2, r3, r4}
  have hcardT : T.card = 4 := by
    simp [T, hr12, hr13, hr14, hr23, hr24, hr34]
  have hTX : T ⊆ X := by
    intro x hx
    rw [hX]
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp
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
      (ZMod.cast (base x) : ZMod m) = ZMod.cast x :=
        cast_projection36_eq_cast hm36 x
      _ = ZMod.cast r2 := by rw [hx]
      _ = ZMod.cast r1 := hcast12.symm
  · calc
      (ZMod.cast (base x) : ZMod m) = ZMod.cast x :=
        cast_projection36_eq_cast hm36 x
      _ = ZMod.cast r3 := by rw [hx]
      _ = ZMod.cast r1 := hcast13.symm
  · calc
      (ZMod.cast (base x) : ZMod m) = ZMod.cast x :=
        cast_projection36_eq_cast hm36 x
      _ = ZMod.cast r4 := by rw [hx]
      _ = ZMod.cast r1 := hcast14.symm

/-- Every failed projected zero is therefore the concrete
`Phi_30`/not-`Phi_6` defect. -/
theorem z180_k6_phi30_defect_of_fiveFactorDefect
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hdefect : Z180K6Projection36FiveFactorDefect A L) :
    cyclotomic 30 Int ∣ maskPolynomial 180 A ∧
      ¬ cyclotomic 6 Int ∣ maskPolynomial 180 A := by
  obtain ⟨l1, hl1, l2, hl2, hne, hm36, hmgt, horderHigh,
    hhigh, hlow⟩ := hdefect
  let d : ZMod 180 := l1 - l2
  let q : ZMod 5 := crt180FifthCoord (toCRT180 d)
  let u : CRT180 := toCRT180 d - crt180FifthSingle q
  let m : Nat := frequencyOrder 36
    (z180K6Projection36 l1 - z180K6Projection36 l2)
  have hu : crt180FifthCoord u = 0 := by
    change crt180FifthCoord
      (toCRT180 d - crt180FifthSingle
        (crt180FifthCoord (toCRT180 d))) = 0
    change crt180FifthCoord (toCRT180 d) -
      crt180FifthCoord (crt180FifthSingle
        (crt180FifthCoord (toCRT180 d))) = 0
    simp
  have hq : q ≠ 0 := by
    intro hq0
    have huEq : u = toCRT180 d := by
      dsimp only [u]
      rw [hq0]
      simp
    have hordDvd :=
      frequencyOrder_fromCRT180_dvd_thirtySix_of_fifthCoord_eq_zero u hu
    rw [huEq, fromCRT180_toCRT180] at hordDvd
    rw [show frequencyOrder 180 d = 5 * m by
      simpa only [d, m] using horderHigh] at hordDvd
    have hfive : 5 ∣ 36 := by
      exact (dvd_mul_right 5 m).trans hordDvd
    norm_num at hfive
  have hrecover : u + crt180FifthSingle q = toCRT180 d := by
    dsimp [u]
    abel
  have hdrepr : d = fromCRT180 (u + crt180FifthSingle q) := by
    rw [hrecover, fromCRT180_toCRT180]
  have hordD : frequencyOrder 180 d =
      frequencyOrder 180 (fromCRT180 u) * 5 := by
    rw [hdrepr]
    exact frequencyOrder_fromCRT180_add_fifth u hu hq
  have hbaseOrder : frequencyOrder 180 (fromCRT180 u) = m := by
    dsimp only [d, m] at hordD horderHigh ⊢
    omega
  have hhighM : cyclotomic (5 * m) Int ∣ maskPolynomial 180 A := by
    simpa only [m] using hhigh
  have hlowM : ¬ cyclotomic m Int ∣ maskPolynomial 180 A := by
    simpa only [m] using hlow
  have hm : m = 6 :=
    z180_k6_defect_base_order_eq_six_of_injOn hcard
      (z180_k6_projection36_injOn_of_spectral hSpec hcard)
      u m hu hbaseOrder (by simpa [Nat.mul_comm] using hhighM) hlowM
  rw [hm] at hhighM hlowM
  constructor
  · convert hhighM using 1 <;> norm_num
  · exact hlowM

/-- End-to-end descent reduction.  The only remaining premise is the exact
size-six spectral-to-tile theorem in `ZMod 36`. -/
theorem z180_k6_phi30_defect_of_non_tiler
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hInduction : Z36SpectralCard6ImpliesTile)
    (hnot : ¬ ∃ B : Finset (ZMod 180), Tiles A B) :
    cyclotomic 30 Int ∣ maskPolynomial 180 A ∧
      ¬ cyclotomic 6 Int ∣ maskPolynomial 180 A := by
  exact z180_k6_phi30_defect_of_fiveFactorDefect hSpec hcard
    (z180_k6_fiveFactorDefect_of_non_tiler
      hSpec hcard hInduction hnot)

#print axioms z180_k6_defect_base_order_eq_six_of_injOn
#print axioms z180_k6_phi30_defect_of_fiveFactorDefect
#print axioms z180_k6_phi30_defect_of_non_tiler

end Fuglede
