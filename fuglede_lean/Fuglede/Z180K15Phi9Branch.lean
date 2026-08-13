import Fuglede.Z180K15SubgroupInduction
import Mathlib.Tactic

/-!
# The missing-`Phi_9` branch at cardinality fifteen

If the projected spectrum mask is not divisible by `Phi_9` over `F_2`, then
two points of the spectral set with the same residue modulo five must have
the same residue modulo fifteen.  Together with the balanced fifth fibres,
this makes the image modulo forty-five a union of five full three-point
fibres modulo fifteen.  The fixed set `{0,5,10}` is then a tiling complement.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- A difference divisible by five but not by fifteen has order `9`, `18`,
or `36` in `ZMod 180`. -/
theorem z180_frequencyOrder_nine_eighteen_or_thirtysix_of_cast5_eq_of_cast15_ne
    (x y : ZMod 180)
    (hcast5 : (ZMod.cast x : ZMod 5) = ZMod.cast y)
    (hcast15 : (ZMod.cast x : ZMod 15) ≠ ZMod.cast y) :
    frequencyOrder 180 (x - y) = 9 ∨
      frequencyOrder 180 (x - y) = 18 ∨
      frequencyOrder 180 (x - y) = 36 := by
  have hcast5Zero : (ZMod.cast (x - y) : ZMod 5) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 5 ∣ 180), hcast5, sub_self]
  have hnatCast5Zero : ((x - y).val : ZMod 5) = 0 := by
    simpa only [ZMod.cast_eq_val] using hcast5Zero
  have hdvd : 5 ∣ (x - y).val :=
    (ZMod.natCast_eq_zero_iff (x - y).val 5).1 hnatCast5Zero
  obtain ⟨k, hk⟩ := hdvd
  have hcast15Diff : (ZMod.cast (x - y) : ZMod 15) ≠ 0 := by
    intro hzero
    apply hcast15
    rw [← sub_eq_zero]
    simpa [ZMod.cast_sub (by norm_num : 15 ∣ 180)] using hzero
  have hnatCast15Diff : ((x - y).val : ZMod 15) ≠ 0 := by
    simpa only [ZMod.cast_eq_val] using hcast15Diff
  have hvalne : (x - y).val ≠ 0 := by
    intro hzero
    apply hnatCast15Diff
    rw [hzero]
    norm_num
  have hkpos : 0 < k := by omega
  have hklt : k < 36 := by
    have hvalLt := (x - y).val_lt
    omega
  have hnotdvd15 : ¬ 15 ∣ 5 * k := by
    intro hdiv15
    apply hnatCast15Diff
    rw [hk]
    exact (ZMod.natCast_eq_zero_iff (5 * k) 15).2 hdiv15
  unfold frequencyOrder
  rw [hk]
  interval_cases k <;> norm_num at hkpos hnotdvd15
  all_goals norm_num

/-- Orders `9`, `18`, and `36` all reduce to the projected `Phi_9` factor
over `F_2`. -/
theorem cyclotomic_nine_dvd_projection45MaskModTwo_of_order_nine_eighteen_or_thirtysix
    {S : Finset (ZMod 180)} {d : ZMod 180}
    (horder : frequencyOrder 180 d = 9 ∨
      frequencyOrder 180 d = 18 ∨ frequencyOrder 180 d = 36)
    (hzero : CyclotomicZero 180 S d) :
    cyclotomic 9 (ZMod 2) ∣ z180Projection45MaskModTwo S := by
  rcases horder with hnine | heighteen | hthirtysix
  · apply cyclotomic_dvd_projection45MaskModTwo_of_dvd_mask (by norm_num)
    simpa [CyclotomicZero, hnine] using hzero
  · apply cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
      (m := 9) (by norm_num) (by norm_num)
    simpa [CyclotomicZero, heighteen] using hzero
  · apply cyclotomic_dvd_projection45MaskModTwo_of_four_times_index_dvd_mask
      (m := 9) (by norm_num) (by norm_num)
    simpa [CyclotomicZero, hthirtysix] using hzero

/-- In the missing-`Phi_9` branch, equality modulo five inside `A` forces
equality modulo fifteen. -/
theorem z180_k15_cast15_eq_of_cast5_eq_of_not_phi9_dvd_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hnot9 : ¬ cyclotomic 9 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∀ x ∈ A, ∀ y ∈ A,
      (ZMod.cast x : ZMod 5) = ZMod.cast y →
      (ZMod.cast x : ZMod 15) = ZMod.cast y := by
  intro x hx y hy hcast5
  by_contra hcast15
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hcast15 rfl
  have hzero : CyclotomicZero 180 L (x - y) :=
    (cyclotomicSpectrum_dual hSpec).2.2 x hx y hy hxy
  apply hnot9
  exact
    cyclotomic_nine_dvd_projection45MaskModTwo_of_order_nine_eighteen_or_thirtysix
      (z180_frequencyOrder_nine_eighteen_or_thirtysix_of_cast5_eq_of_cast15_ne
        x y hcast5 hcast15) hzero

/-- The fixed three-point complement in `ZMod 45`. -/
def z45K15Phi9Complement : Finset (ZMod 45) := {0, 5, 10}

@[simp]
theorem card_z45K15Phi9Complement : z45K15Phi9Complement.card = 3 := by
  decide

theorem cast5_eq_zero_of_mem_z45K15Phi9Complement
    {b : ZMod 45} (hb : b ∈ z45K15Phi9Complement) :
    (ZMod.cast b : ZMod 5) = 0 := by
  simp only [z45K15Phi9Complement, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;> decide

theorem cast15_injOn_z45K15Phi9Complement :
    Set.InjOn (fun b : ZMod 45 => (ZMod.cast b : ZMod 15))
      (z45K15Phi9Complement : Set (ZMod 45)) := by
  decide

/-- Reduction through `ZMod 45` commutes with reduction from `ZMod 180` to
each divisor of forty-five used below. -/
theorem cast_projection45_eq_cast
    {m : Nat} (hm45 : m ∣ 45) (x : ZMod 180) :
    (ZMod.cast (z180K15Projection45 x) : ZMod m) = ZMod.cast x := by
  change (ZMod.cast (ZMod.cast x : ZMod 45) : ZMod m) = ZMod.cast x
  have hcomp := ZMod.castHom_comp hm45 (by norm_num : 45 ∣ 180)
  exact DFunLike.congr_fun hcomp x

/-- Projected form of the rigidity lemma: inside the image of `A`, equality
modulo five forces equality modulo fifteen. -/
theorem z180_k15_projection45_image_cast15_eq_of_cast5_eq_of_not_phi9
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hnot9 : ¬ cyclotomic 9 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∀ a ∈ A.image z180K15Projection45,
      ∀ a' ∈ A.image z180K15Projection45,
      (ZMod.cast a : ZMod 5) = ZMod.cast a' →
      (ZMod.cast a : ZMod 15) = ZMod.cast a' := by
  intro a ha a' ha' hcast5
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha'
  apply (cast_projection45_eq_cast (by norm_num : 15 ∣ 45) x).trans
  have hxy5 : (ZMod.cast x : ZMod 5) = ZMod.cast y := by
    rw [← cast_projection45_eq_cast (by norm_num : 5 ∣ 45) x,
      ← cast_projection45_eq_cast (by norm_num : 5 ∣ 45) y]
    exact hcast5
  rw [z180_k15_cast15_eq_of_cast5_eq_of_not_phi9_dvd_spectrum_mask
    hSpec hnot9 x hx y hy hxy5]
  exact (cast_projection45_eq_cast (by norm_num : 15 ∣ 45) y).symm

/-- The projected image tiles `ZMod 45` in the missing-`Phi_9` branch, with
the explicit complement `{0,5,10}`. -/
theorem z180_k15_projection45_image_tiles_of_not_phi9_dvd_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot9 : ¬ cyclotomic 9 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    Tiles (A.image z180K15Projection45) z45K15Phi9Complement := by
  have hinj45 := (z180_k15_fkms_qr_gateway hSpec hcard).1
  have himageCard : (A.image z180K15Projection45).card = 15 := by
    rw [Finset.card_image_of_injOn hinj45, hcard]
  apply (Fintype.bijective_iff_injective_and_card
    (sumMap (A.image z180K15Projection45) z45K15Phi9Complement)).2
  constructor
  · intro p q hpq
    rcases p with ⟨⟨a, b⟩, hp⟩
    rcases q with ⟨⟨a', b'⟩, hq⟩
    have ha : a ∈ A.image z180K15Projection45 :=
      (Finset.mem_product.mp hp).1
    have hb : b ∈ z45K15Phi9Complement :=
      (Finset.mem_product.mp hp).2
    have ha' : a' ∈ A.image z180K15Projection45 :=
      (Finset.mem_product.mp hq).1
    have hb' : b' ∈ z45K15Phi9Complement :=
      (Finset.mem_product.mp hq).2
    change a + b = a' + b' at hpq
    have ha5 : (ZMod.cast a : ZMod 5) = ZMod.cast a' := by
      have h := congrArg (fun z : ZMod 45 => (ZMod.cast z : ZMod 5)) hpq
      rw [ZMod.cast_add (by norm_num : 5 ∣ 45),
        ZMod.cast_add (by norm_num : 5 ∣ 45),
        cast5_eq_zero_of_mem_z45K15Phi9Complement hb,
        cast5_eq_zero_of_mem_z45K15Phi9Complement hb',
        add_zero, add_zero] at h
      exact h
    have ha15 : (ZMod.cast a : ZMod 15) = ZMod.cast a' :=
      z180_k15_projection45_image_cast15_eq_of_cast5_eq_of_not_phi9
        hSpec hnot9 a ha a' ha' ha5
    have hb15 : (ZMod.cast b : ZMod 15) = ZMod.cast b' := by
      have h := congrArg (fun z : ZMod 45 => (ZMod.cast z : ZMod 15)) hpq
      rw [ZMod.cast_add (by norm_num : 15 ∣ 45),
        ZMod.cast_add (by norm_num : 15 ∣ 45), ha15] at h
      exact add_left_cancel h
    have hbb : b = b' :=
      cast15_injOn_z45K15Phi9Complement hb hb' hb15
    subst b'
    have haa : a = a' := add_right_cancel hpq
    subst a'
    rfl
  · rw [Fintype.card_coe, Finset.card_product, himageCard,
      card_z45K15Phi9Complement, ZMod.card]

/-- Lifted tiling conclusion for the missing-`Phi_9` branch. -/
theorem z180_k15_exists_tiling_of_not_phi9_dvd_projection45_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot9 : ¬ cyclotomic 9 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  apply z180_k15_exists_tiling_of_projection45_image_tile hSpec hcard
  exact ⟨z45K15Phi9Complement,
    z180_k15_projection45_image_tiles_of_not_phi9_dvd_spectrum_mask
      hSpec hcard hnot9⟩

#print axioms z180_frequencyOrder_nine_eighteen_or_thirtysix_of_cast5_eq_of_cast15_ne
#print axioms z180_k15_cast15_eq_of_cast5_eq_of_not_phi9_dvd_spectrum_mask
#print axioms z180_k15_projection45_image_tiles_of_not_phi9_dvd_spectrum_mask
#print axioms z180_k15_exists_tiling_of_not_phi9_dvd_projection45_spectrum_mask

end Fuglede
