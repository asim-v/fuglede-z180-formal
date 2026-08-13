import Fuglede.Z180K12M6Order20FiveLevels
import Mathlib.Tactic

/-!
# Set-level exclusion of order twenty in the cardinality-twelve defect branch

This is the typed adapter around the small Presburger kernel.  It does not
assume the independent non-tiler-to-defect reduction: the genuine
`Phi_30`/not-`Phi_6` defect remains an explicit hypothesis.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0

private theorem order20_global_count12_profiles
    (b : Fin 36 → Int)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3) :
    z180K12Order20P0 (projection36Count12 b) = 3 ∧
    z180K12Order20P1 (projection36Count12 b) = 3 ∧
    z180K12Order20P2 (projection36Count12 b) = 3 ∧
    z180K12Order20P3 (projection36Count12 b) = 3 := by
  rcases hmod4 with ⟨h0, h1, h2, h3⟩
  constructor
  · change (b 0 + b 12 + b 24) + (b 4 + b 16 + b 28) +
      (b 8 + b 20 + b 32) = 3
    linear_combination h0
  constructor
  · change (b 1 + b 13 + b 25) + (b 5 + b 17 + b 29) +
      (b 9 + b 21 + b 33) = 3
    linear_combination h1
  constructor
  · change (b 2 + b 14 + b 26) + (b 6 + b 18 + b 30) +
      (b 10 + b 22 + b 34) = 3
    linear_combination h2
  · change (b 3 + b 15 + b 27) + (b 7 + b 19 + b 31) +
      (b 11 + b 23 + b 35) = 3
    linear_combination h3

/-- The order-twenty zero is incompatible with a cardinality-twelve
`m = 6` defect and the forced order-two/order-four transforms. -/
theorem z180_k12_m6_not_cyclotomic_twenty
    {A : Finset (ZMod 180)}
    (hcard : A.card = 12)
    (hinj : Set.InjOn (fun x : ZMod 180 ↦ (ZMod.cast x : ZMod 36))
      (A : Set (ZMod 180)))
    (htransform2 : z180ExactOrderTransform A 2 = 0)
    (htransform4 : z180ExactOrderTransform A 4 = 0)
    (hdefect : Z180K12M6Defect A) :
    ¬ cyclotomic 20 Int ∣ maskPolynomial 180 A := by
  intro h20
  obtain ⟨k0, k1, hlo, hhi, hmod4, h60, h61, hne⟩ :=
    z180_k12_m6_prepare hcard hinj htransform2 htransform4 hdefect
  have hmask4 : cyclotomic 4 Int ∣ maskPolynomial 180 A :=
    z180_cyclotomic_dvd_mask_of_transform_zero
      (A := A) (e := 4) (u := 45) (by norm_num) (by decide) htransform4
  let n : ZMod 5 → Fin 12 → Int :=
    fun c ↦ z180K12Order20LevelCount12 A c
  have hn (c : ZMod 5) : ∀ r : Fin 12, 0 ≤ n c r := by
    intro r
    exact z180K12Order20LevelCount12_nonneg A c r
  have hm (c : ZMod 5) :
      z180K12Order20Mass (n c) = (z180FifthFiberCard A c : Int) := by
    exact z180K12Order20LevelCount12_mass A c
  have hpos (c : ZMod 5) : 1 ≤ z180K12Order20Mass (n c) := by
    rw [hm]
    exact_mod_cast z180FifthFiberCard_pos_of_exists A c (hdefect.2.2 c)
  have hphi4 (c : ZMod 5) :
      z180K12Order20Phi4R0 (n c) = 0 ∧
      z180K12Order20Phi4R1 (n c) = 0 := by
    apply projection36_phi4_count12_remainders_order20
    exact z180_k12_order20_level_phi4_dvd A h20 hmask4 c
  have heven (c : ZMod 5) :
      ∃ t : Int, z180K12Order20Mass (n c) = 2 * t :=
    z180_k12_order20_mass_even_of_phi4 (n c) (hphi4 c).1 (hphi4 c).2
  have hphi6 (c c' : ZMod 5) :
      z180K12Order20Phi6R0 (n c) = z180K12Order20Phi6R0 (n c') ∧
      z180K12Order20Phi6R1 (n c) = z180K12Order20Phi6R1 (n c') := by
    apply projection36_phi6_count12_eq_of_sub_dvd_order20
    exact z180_k12_order20_level_phi6_sub_dvd A hdefect.1 c c'
  have hsumFibres := sum_z180FifthFiberCard A
  rw [sum_zmod_five_explicit_order20, hcard] at hsumFibres
  have hsum :
      z180K12Order20Mass (n 0) + z180K12Order20Mass (n 1) +
        z180K12Order20Mass (n 2) + z180K12Order20Mass (n 3) +
        z180K12Order20Mass (n 4) = 12 := by
    rw [hm 0, hm 1, hm 2, hm 3, hm 4]
    exact_mod_cast hsumFibres
  have hmassCases := z180_k12_order20_five_masses
    (z180K12Order20Mass (n 0)) (z180K12Order20Mass (n 1))
    (z180K12Order20Mass (n 2)) (z180K12Order20Mass (n 3))
    (z180K12Order20Mass (n 4))
    (hpos 0) (hpos 1) (hpos 2) (hpos 3) (hpos 4)
    (heven 0) (heven 1) (heven 2) (heven 3) (heven 4) hsum
  have hglobal := order20_global_count12_profiles
    (z180K12ProjectionIndicator A) hmod4
  have hprofileSums := sum_z180K12Order20LevelProfiles A
  obtain ⟨hp0, hp1, hp2, hp3⟩ := hprofileSums
  rw [sum_zmod_five_explicit_order20, hglobal.1] at hp0
  rw [sum_zmod_five_explicit_order20, hglobal.2.1] at hp1
  rw [sum_zmod_five_explicit_order20, hglobal.2.2.1] at hp2
  rw [sum_zmod_five_explicit_order20, hglobal.2.2.2] at hp3
  have hshape (c c' : ZMod 5)
      (hc : z180K12Order20Mass (n c) = 2)
      (hc' : z180K12Order20Mass (n c') = 4) :
      Z180K12Order20SmallLargeShape (n c) (n c') :=
    z180_k12_order20_small_large_shape (n c) (n c')
      (hn c) (hn c') hc hc'
      (hphi4 c).1 (hphi4 c).2 (hphi4 c').1 (hphi4 c').2
      (hphi6 c c').1 (hphi6 c c').2
  rcases hmassCases with h | h | h | h | h
  · apply z180_k12_order20_four_small_profiles_impossible
      (n 1) (n 2) (n 3) (n 4) (n 0)
      (hshape 1 0 h.2.1 h.1)
      (hshape 2 0 h.2.2.1 h.1)
      (hshape 3 0 h.2.2.2.1 h.1)
      (hshape 4 0 h.2.2.2.2 h.1)
    all_goals linarith only [hp0, hp1, hp2, hp3]
  · apply z180_k12_order20_four_small_profiles_impossible
      (n 0) (n 2) (n 3) (n 4) (n 1)
      (hshape 0 1 h.1 h.2.1)
      (hshape 2 1 h.2.2.1 h.2.1)
      (hshape 3 1 h.2.2.2.1 h.2.1)
      (hshape 4 1 h.2.2.2.2 h.2.1)
    all_goals linarith only [hp0, hp1, hp2, hp3]
  · apply z180_k12_order20_four_small_profiles_impossible
      (n 0) (n 1) (n 3) (n 4) (n 2)
      (hshape 0 2 h.1 h.2.2.1)
      (hshape 1 2 h.2.1 h.2.2.1)
      (hshape 3 2 h.2.2.2.1 h.2.2.1)
      (hshape 4 2 h.2.2.2.2 h.2.2.1)
    all_goals linarith only [hp0, hp1, hp2, hp3]
  · apply z180_k12_order20_four_small_profiles_impossible
      (n 0) (n 1) (n 2) (n 4) (n 3)
      (hshape 0 3 h.1 h.2.2.2.1)
      (hshape 1 3 h.2.1 h.2.2.2.1)
      (hshape 2 3 h.2.2.1 h.2.2.2.1)
      (hshape 4 3 h.2.2.2.2 h.2.2.2.1)
    all_goals linarith only [hp0, hp1, hp2, hp3]
  · apply z180_k12_order20_four_small_profiles_impossible
      (n 0) (n 1) (n 2) (n 3) (n 4)
      (hshape 0 4 h.1 h.2.2.2.2)
      (hshape 1 4 h.2.1 h.2.2.2.2)
      (hshape 2 4 h.2.2.1 h.2.2.2.2)
      (hshape 3 4 h.2.2.2.1 h.2.2.2.2)
    all_goals assumption

#print axioms z180_k12_m6_not_cyclotomic_twenty

end Fuglede
