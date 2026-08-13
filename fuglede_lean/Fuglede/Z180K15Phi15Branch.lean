import Fuglede.Z180K15TwoBranchReduction
import Mathlib.Tactic

/-!
# The missing-`Phi_15` branch at cardinality fifteen

Inside a fixed modulo-three fibre, a difference has projected order fifteen
exactly when its modulo-nine and modulo-five coordinates are both different.
Thus absence of `Phi_15` makes every such fibre a clique in the `3 x 5` rook
graph.  A clique has at most five points.  Since the projected set has fifteen
points and there are three modulo-three fibres, each fibre has exactly five
points and is a full modulo-nine row.  The fixed set `{0,15,30}` is then an
exact tiling complement in `ZMod 45`.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

/-- A difference which is zero modulo three, nonzero modulo nine, and
nonzero modulo five has order `15`, `30`, or `60` in `ZMod 180`. -/
theorem z180_frequencyOrder_fifteen_thirty_or_sixty_of_cast3_eq_cast9_ne_cast5_ne
    (x y : ZMod 180)
    (hcast3 : (ZMod.cast x : ZMod 3) = ZMod.cast y)
    (hcast9 : (ZMod.cast x : ZMod 9) ≠ ZMod.cast y)
    (hcast5 : (ZMod.cast x : ZMod 5) ≠ ZMod.cast y) :
    frequencyOrder 180 (x - y) = 15 ∨
      frequencyOrder 180 (x - y) = 30 ∨
      frequencyOrder 180 (x - y) = 60 := by
  have hcast3Zero : (ZMod.cast (x - y) : ZMod 3) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 3 ∣ 180), hcast3, sub_self]
  have hcast9Diff : (ZMod.cast (x - y) : ZMod 9) ≠ 0 := by
    intro hzero
    apply hcast9
    rw [← sub_eq_zero]
    simpa [ZMod.cast_sub (by norm_num : 9 ∣ 180)] using hzero
  have hcast5Diff : (ZMod.cast (x - y) : ZMod 5) ≠ 0 := by
    intro hzero
    apply hcast5
    rw [← sub_eq_zero]
    simpa [ZMod.cast_sub (by norm_num : 5 ∣ 180)] using hzero
  have hdvd3 : 3 ∣ (x - y).val := by
    have hz : ((x - y).val : ZMod 3) = 0 := by
      simpa only [ZMod.cast_eq_val] using hcast3Zero
    exact (ZMod.natCast_eq_zero_iff (x - y).val 3).1 hz
  have hnotdvd9 : ¬ 9 ∣ (x - y).val := by
    intro hdiv
    apply hcast9Diff
    change ((x - y).val : ZMod 9) = 0
    exact (ZMod.natCast_eq_zero_iff (x - y).val 9).2 hdiv
  have hnotdvd5 : ¬ 5 ∣ (x - y).val := by
    intro hdiv
    apply hcast5Diff
    change ((x - y).val : ZMod 5) = 0
    exact (ZMod.natCast_eq_zero_iff (x - y).val 5).2 hdiv
  obtain ⟨k, hk⟩ := hdvd3
  have hnotdvd3k : ¬ 3 ∣ k := by
    intro hdiv
    apply hnotdvd9
    have hmul := Nat.mul_dvd_mul_left 3 hdiv
    simpa [hk, mul_assoc] using hmul
  have hnotdvd5k : ¬ 5 ∣ k := by
    intro hdiv
    apply hnotdvd5
    rw [hk]
    exact dvd_mul_of_dvd_right hdiv 3
  have hc3 : Nat.Coprime 3 k :=
    Nat.prime_three.coprime_iff_not_dvd.mpr hnotdvd3k
  have hc5 : Nat.Coprime 5 k :=
    (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hnotdvd5k
  have hc15 : Nat.Coprime 15 k := by
    simpa using hc3.mul_left hc5
  let g := Nat.gcd 60 k
  have hgdvdk : g ∣ k := Nat.gcd_dvd_right 60 k
  have hgcoprime15 : Nat.Coprime g 15 :=
    hc15.symm.of_dvd_left hgdvdk
  have hgdvd60 : g ∣ 60 := Nat.gcd_dvd_left 60 k
  have hgdvd4 : g ∣ 4 := by
    apply (hgcoprime15.dvd_mul_right).mp
    simpa using hgdvd60
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left k (by norm_num)
  have hgcases : g = 1 ∨ g = 2 ∨ g = 4 := by
    have hgle : g ≤ 4 := Nat.le_of_dvd (by norm_num) hgdvd4
    interval_cases g <;> norm_num at *
  unfold frequencyOrder
  rw [hk]
  rw [show 180 = 3 * 60 by norm_num, Nat.gcd_mul_left]
  rw [Nat.mul_div_mul_left 60 g (by norm_num : 0 < 3)]
  change 60 / g = 15 ∨ 60 / g = 30 ∨ 60 / g = 60
  rcases hgcases with hg | hg | hg <;> rw [hg] <;> norm_num

/-- Orders `15`, `30`, and `60` all reduce to the projected `Phi_15`
factor over `F_2`. -/
theorem cyclotomic_fifteen_dvd_projection45MaskModTwo_of_order_fifteen_thirty_or_sixty
    {S : Finset (ZMod 180)} {d : ZMod 180}
    (horder : frequencyOrder 180 d = 15 ∨
      frequencyOrder 180 d = 30 ∨ frequencyOrder 180 d = 60)
    (hzero : CyclotomicZero 180 S d) :
    cyclotomic 15 (ZMod 2) ∣ z180Projection45MaskModTwo S := by
  rcases horder with h15 | h30 | h60
  · apply cyclotomic_dvd_projection45MaskModTwo_of_dvd_mask (by norm_num)
    simpa [CyclotomicZero, h15] using hzero
  · apply cyclotomic_dvd_projection45MaskModTwo_of_twice_index_dvd_mask
      (m := 15) (by norm_num) (by norm_num)
    simpa [CyclotomicZero, h30] using hzero
  · apply cyclotomic_dvd_projection45MaskModTwo_of_four_times_index_dvd_mask
      (m := 15) (by norm_num) (by norm_num)
    simpa [CyclotomicZero, h60] using hzero

/-- Missing `Phi_15` gives the rook relation on `A`: within one modulo-three
fibre, every pair agrees modulo nine or modulo five. -/
theorem z180_k15_cast9_eq_or_cast5_eq_of_cast3_eq_of_not_phi15
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hnot15 : ¬ cyclotomic 15 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∀ x ∈ A, ∀ y ∈ A,
      (ZMod.cast x : ZMod 3) = ZMod.cast y →
      (ZMod.cast x : ZMod 9) = ZMod.cast y ∨
        (ZMod.cast x : ZMod 5) = ZMod.cast y := by
  intro x hx y hy h3
  by_cases h9 : (ZMod.cast x : ZMod 9) = ZMod.cast y
  · exact Or.inl h9
  by_cases h5 : (ZMod.cast x : ZMod 5) = ZMod.cast y
  · exact Or.inr h5
  exfalso
  have hxy : x ≠ y := by
    intro h
    subst y
    exact h9 rfl
  have hzero : CyclotomicZero 180 L (x - y) :=
    (cyclotomicSpectrum_dual hSpec).2.2 x hx y hy hxy
  apply hnot15
  exact cyclotomic_fifteen_dvd_projection45MaskModTwo_of_order_fifteen_thirty_or_sixty
    (z180_frequencyOrder_fifteen_thirty_or_sixty_of_cast3_eq_cast9_ne_cast5_ne
      x y h3 h9 h5) hzero

/-- Projected form of the rook relation. -/
theorem z180_k15_projection45_image_rook_relation_of_not_phi15
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hnot15 : ¬ cyclotomic 15 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∀ a ∈ A.image z180K15Projection45,
      ∀ a' ∈ A.image z180K15Projection45,
      (ZMod.cast a : ZMod 3) = ZMod.cast a' →
      (ZMod.cast a : ZMod 9) = ZMod.cast a' ∨
        (ZMod.cast a : ZMod 5) = ZMod.cast a' := by
  intro a ha a' ha' h3
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha'
  have h3xy : (ZMod.cast x : ZMod 3) = ZMod.cast y := by
    rw [← cast_projection45_eq_cast (by norm_num : 3 ∣ 45) x,
      ← cast_projection45_eq_cast (by norm_num : 3 ∣ 45) y]
    exact h3
  rcases z180_k15_cast9_eq_or_cast5_eq_of_cast3_eq_of_not_phi15
      hSpec hnot15 x hx y hy h3xy with h9 | h5
  · left
    rw [cast_projection45_eq_cast (by norm_num : 9 ∣ 45) x,
      cast_projection45_eq_cast (by norm_num : 9 ∣ 45) y]
    exact h9
  · right
    rw [cast_projection45_eq_cast (by norm_num : 5 ∣ 45) x,
      cast_projection45_eq_cast (by norm_num : 5 ∣ 45) y]
    exact h5

/-- Ambient joint fibres of reduction modulo three and five have exactly
three points in `ZMod 45`. -/
theorem card_z45_cast3_cast5_fiber :
    ∀ r : ZMod 3, ∀ c : ZMod 5,
      ((Finset.univ : Finset (ZMod 45)).filter fun z =>
        (ZMod.cast z : ZMod 3) = r ∧
          (ZMod.cast z : ZMod 5) = c).card = 3 := by
  decide

/-- Ambient modulo-nine fibres have exactly five points in `ZMod 45`. -/
theorem card_z45_cast9_fiber :
    ∀ q : ZMod 9,
      ((Finset.univ : Finset (ZMod 45)).filter fun z =>
        (ZMod.cast z : ZMod 9) = q).card = 5 := by
  decide

/-- A rook clique inside one modulo-three fibre has at most five points. -/
theorem card_z45_cast3_fiber_le_five_of_rook_relation
    (S : Finset (ZMod 45))
    (hrook : ∀ a ∈ S, ∀ a' ∈ S,
      (ZMod.cast a : ZMod 3) = ZMod.cast a' →
      (ZMod.cast a : ZMod 9) = ZMod.cast a' ∨
        (ZMod.cast a : ZMod 5) = ZMod.cast a') :
    ∀ r : ZMod 3,
      (S.filter fun z => (ZMod.cast z : ZMod 3) = r).card ≤ 5 := by
  classical
  intro r
  let F := S.filter fun z => (ZMod.cast z : ZMod 3) = r
  change F.card ≤ 5
  by_cases hF : F = ∅
  · simp [F, hF]
  have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
  obtain ⟨x, hxF⟩ := hFne
  have hxS : x ∈ S := (Finset.mem_filter.mp hxF).1
  have hx3 : (ZMod.cast x : ZMod 3) = r :=
    (Finset.mem_filter.mp hxF).2
  by_cases hall5 : ∀ z ∈ F,
      (ZMod.cast z : ZMod 5) = ZMod.cast x
  · have hsubset : F ⊆
        (Finset.univ : Finset (ZMod 45)).filter (fun z =>
          (ZMod.cast z : ZMod 3) = r ∧
            (ZMod.cast z : ZMod 5) = ZMod.cast x) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
        (Finset.mem_filter.mp hz).2, hall5 z hz⟩
    have hcard := Finset.card_le_card hsubset
    rw [card_z45_cast3_cast5_fiber r (ZMod.cast x)] at hcard
    omega
  · push Not at hall5
    obtain ⟨y, hyF, hy5⟩ := hall5
    have hyS : y ∈ S := (Finset.mem_filter.mp hyF).1
    have hy3 : (ZMod.cast y : ZMod 3) = r :=
      (Finset.mem_filter.mp hyF).2
    have hxy9 : (ZMod.cast x : ZMod 9) = ZMod.cast y := by
      rcases hrook x hxS y hyS (hx3.trans hy3.symm) with h9 | h5
      · exact h9
      · exact False.elim (hy5 h5.symm)
    have hall9 : ∀ z ∈ F,
        (ZMod.cast z : ZMod 9) = ZMod.cast x := by
      intro z hzF
      have hzS : z ∈ S := (Finset.mem_filter.mp hzF).1
      have hz3 : (ZMod.cast z : ZMod 3) = r :=
        (Finset.mem_filter.mp hzF).2
      by_cases hz5 : (ZMod.cast z : ZMod 5) = ZMod.cast x
      · rcases hrook y hyS z hzS (hy3.trans hz3.symm) with h9 | h5
        · exact h9.symm.trans hxy9.symm
        · exfalso
          apply hy5
          exact h5.trans hz5
      · rcases hrook x hxS z hzS (hx3.trans hz3.symm) with h9 | h5
        · exact h9.symm
        · exact False.elim (hz5 h5.symm)
    have hsubset : F ⊆
        (Finset.univ : Finset (ZMod 45)).filter (fun z =>
          (ZMod.cast z : ZMod 9) = ZMod.cast x) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hall9 z hz⟩
    have hcard := Finset.card_le_card hsubset
    rw [card_z45_cast9_fiber (ZMod.cast x)] at hcard
    exact hcard

/-- At total cardinality fifteen, all three modulo-three fibres of a rook
set have exactly five points. -/
theorem card_z45_cast3_fiber_eq_five_of_card_fifteen_of_rook_relation
    (S : Finset (ZMod 45)) (hcard : S.card = 15)
    (hrook : ∀ a ∈ S, ∀ a' ∈ S,
      (ZMod.cast a : ZMod 3) = ZMod.cast a' →
      (ZMod.cast a : ZMod 9) = ZMod.cast a' ∨
        (ZMod.cast a : ZMod 5) = ZMod.cast a') :
    ∀ r : ZMod 3,
      (S.filter fun z => (ZMod.cast z : ZMod 3) = r).card = 5 := by
  classical
  let occ : ZMod 3 → Nat := fun r =>
    (S.filter fun z => (ZMod.cast z : ZMod 3) = r).card
  have hsum : (∑ r : ZMod 3, occ r) = 15 := by
    rw [show 15 = S.card from hcard.symm]
    simpa [occ] using
      (Finset.sum_card_fiberwise_eq_card_filter S
        (Finset.univ : Finset (ZMod 3))
        (fun z : ZMod 45 => (ZMod.cast z : ZMod 3)))
  have hle : ∀ r : ZMod 3, occ r ≤ 5 := by
    intro r
    exact card_z45_cast3_fiber_le_five_of_rook_relation S hrook r
  intro r
  change occ r = 5
  have hler : occ r ≤ 5 := hle r
  have hothers : (∑ s ∈ (Finset.univ : Finset (ZMod 3)).erase r,
      occ s) ≤ 10 := by
    calc
      _ ≤ ∑ _s ∈ (Finset.univ : Finset (ZMod 3)).erase r, 5 := by
        apply Finset.sum_le_sum
        intro s hs
        exact hle s
      _ = 10 := by simp
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (ZMod 3))
    occ (Finset.mem_univ r)
  omega

/-- Consequently, equality modulo three inside the projected image forces
equality modulo nine. -/
theorem z180_k15_projection45_image_cast9_eq_of_cast3_eq_of_not_phi15
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot15 : ¬ cyclotomic 15 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∀ a ∈ A.image z180K15Projection45,
      ∀ a' ∈ A.image z180K15Projection45,
      (ZMod.cast a : ZMod 3) = ZMod.cast a' →
      (ZMod.cast a : ZMod 9) = ZMod.cast a' := by
  let S := A.image z180K15Projection45
  have hrook := z180_k15_projection45_image_rook_relation_of_not_phi15
    hSpec hnot15
  have hinj45 := (z180_k15_fkms_qr_gateway hSpec hcard).1
  have hcardS : S.card = 15 := by
    dsimp [S]
    rw [Finset.card_image_of_injOn hinj45, hcard]
  have hfive :=
    card_z45_cast3_fiber_eq_five_of_card_fifteen_of_rook_relation
      S hcardS hrook
  intro a ha a' ha' h3
  let F := S.filter fun z => (ZMod.cast z : ZMod 3) = ZMod.cast a
  have haF : a ∈ F := Finset.mem_filter.mpr ⟨ha, rfl⟩
  have ha'F : a' ∈ F := Finset.mem_filter.mpr ⟨ha', h3.symm⟩
  by_cases hall5 : ∀ z ∈ F,
      (ZMod.cast z : ZMod 5) = ZMod.cast a
  · have hsubset : F ⊆
        (Finset.univ : Finset (ZMod 45)).filter (fun z =>
          (ZMod.cast z : ZMod 3) = ZMod.cast a ∧
            (ZMod.cast z : ZMod 5) = ZMod.cast a) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
        (Finset.mem_filter.mp hz).2, hall5 z hz⟩
    have hle := Finset.card_le_card hsubset
    have hcardF : F.card = 5 := by simpa [F, S] using hfive (ZMod.cast a)
    rw [hcardF, card_z45_cast3_cast5_fiber] at hle
    omega
  · push Not at hall5
    obtain ⟨y, hyF, hy5⟩ := hall5
    have hyS : y ∈ S := (Finset.mem_filter.mp hyF).1
    have hy3 : (ZMod.cast y : ZMod 3) = ZMod.cast a :=
      (Finset.mem_filter.mp hyF).2
    have hay9 : (ZMod.cast a : ZMod 9) = ZMod.cast y := by
      rcases hrook a ha y hyS hy3.symm with h9 | h5
      · exact h9
      · exact False.elim (hy5 h5.symm)
    by_cases ha'5 : (ZMod.cast a' : ZMod 5) = ZMod.cast a
    · rcases hrook y hyS a' ha' (hy3.trans h3) with h9 | h5
      · exact hay9.trans h9
      · exfalso
        apply hy5
        exact h5.trans ha'5
    · rcases hrook a ha a' ha' h3 with h9 | h5
      · exact h9
      · exact False.elim (ha'5 h5.symm)

/-- Fixed three-point complement for the missing-`Phi_15` branch. -/
def z45K15Phi15Complement : Finset (ZMod 45) := {0, 15, 30}

@[simp]
theorem card_z45K15Phi15Complement : z45K15Phi15Complement.card = 3 := by
  decide

theorem cast3_eq_zero_of_mem_z45K15Phi15Complement
    {b : ZMod 45} (hb : b ∈ z45K15Phi15Complement) :
    (ZMod.cast b : ZMod 3) = 0 := by
  simp only [z45K15Phi15Complement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;> decide

theorem cast9_injOn_z45K15Phi15Complement :
    Set.InjOn (fun b : ZMod 45 => (ZMod.cast b : ZMod 9))
      (z45K15Phi15Complement : Set (ZMod 45)) := by
  decide

/-- The projected image tiles with `{0,15,30}` in the missing-`Phi_15`
branch. -/
theorem z180_k15_projection45_image_tiles_of_not_phi15_dvd_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot15 : ¬ cyclotomic 15 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    Tiles (A.image z180K15Projection45) z45K15Phi15Complement := by
  have hinj45 := (z180_k15_fkms_qr_gateway hSpec hcard).1
  have himageCard : (A.image z180K15Projection45).card = 15 := by
    rw [Finset.card_image_of_injOn hinj45, hcard]
  have hrigid :=
    z180_k15_projection45_image_cast9_eq_of_cast3_eq_of_not_phi15
      hSpec hcard hnot15
  apply (Fintype.bijective_iff_injective_and_card
    (sumMap (A.image z180K15Projection45) z45K15Phi15Complement)).2
  constructor
  · intro p q hpq
    rcases p with ⟨⟨a, b⟩, hp⟩
    rcases q with ⟨⟨a', b'⟩, hq⟩
    have ha : a ∈ A.image z180K15Projection45 :=
      (Finset.mem_product.mp hp).1
    have hb : b ∈ z45K15Phi15Complement :=
      (Finset.mem_product.mp hp).2
    have ha' : a' ∈ A.image z180K15Projection45 :=
      (Finset.mem_product.mp hq).1
    have hb' : b' ∈ z45K15Phi15Complement :=
      (Finset.mem_product.mp hq).2
    change a + b = a' + b' at hpq
    have ha3 : (ZMod.cast a : ZMod 3) = ZMod.cast a' := by
      have h := congrArg (fun z : ZMod 45 => (ZMod.cast z : ZMod 3)) hpq
      rw [ZMod.cast_add (by norm_num : 3 ∣ 45),
        ZMod.cast_add (by norm_num : 3 ∣ 45),
        cast3_eq_zero_of_mem_z45K15Phi15Complement hb,
        cast3_eq_zero_of_mem_z45K15Phi15Complement hb',
        add_zero, add_zero] at h
      exact h
    have ha9 : (ZMod.cast a : ZMod 9) = ZMod.cast a' :=
      hrigid a ha a' ha' ha3
    have hb9 : (ZMod.cast b : ZMod 9) = ZMod.cast b' := by
      have h := congrArg (fun z : ZMod 45 => (ZMod.cast z : ZMod 9)) hpq
      rw [ZMod.cast_add (by norm_num : 9 ∣ 45),
        ZMod.cast_add (by norm_num : 9 ∣ 45), ha9] at h
      exact add_left_cancel h
    have hbb : b = b' := cast9_injOn_z45K15Phi15Complement hb hb' hb9
    subst b'
    have haa : a = a' := add_right_cancel hpq
    subst a'
    rfl
  · rw [Fintype.card_coe, Finset.card_product, himageCard,
      card_z45K15Phi15Complement, ZMod.card]

/-- Lifted tiling conclusion for the missing-`Phi_15` branch. -/
theorem z180_k15_exists_tiling_of_not_phi15_dvd_projection45_spectrum_mask
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 15)
    (hnot15 : ¬ cyclotomic 15 (ZMod 2) ∣
      z180Projection45MaskModTwo L) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  apply z180_k15_exists_tiling_of_projection45_image_tile hSpec hcard
  exact ⟨z45K15Phi15Complement,
    z180_k15_projection45_image_tiles_of_not_phi15_dvd_spectrum_mask
      hSpec hcard hnot15⟩

#print axioms z180_k15_projection45_image_cast9_eq_of_cast3_eq_of_not_phi15
#print axioms z180_k15_projection45_image_tiles_of_not_phi15_dvd_spectrum_mask
#print axioms z180_k15_exists_tiling_of_not_phi15_dvd_projection45_spectrum_mask

end Fuglede
