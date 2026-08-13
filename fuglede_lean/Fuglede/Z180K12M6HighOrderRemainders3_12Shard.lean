import Fuglede.Z180K12M6HighOrderRemainderDefs
import Fuglede.Z180K12M6HighOrderRemoved
import Mathlib.Tactic

/-!
# Characteristic-five projected remainders for orders three and twelve

This shard contains exactly the interfaces consumed by the order-fifteen
and order-sixty arithmetic kernels.
-/

namespace Fuglede

namespace Z180K12HighOrder

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem remainderCoeff_three_high (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 3 b 0 = projection36Phi3R0 b ∧
    projection36CyclotomicRemainderCoeff 3 b 1 = projection36Phi3R1 b := by
  let r := projection36RemainderRemoved 3 b
  have hdiv : cyclotomic 3 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 3 b (by
      rw [show Nat.totient 3 = 2 by decide]
      norm_num)
  obtain ⟨h0, h1⟩ := projection36_phi3_count12_remainders r (by
    simpa [projection36IndicatorMask] using hdiv)
  have hz (j : Nat) (hj : 2 ≤ j) :
      projection36CyclotomicRemainderCoeff 3 b j = 0 := by
    apply projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
    rw [show Nat.totient 3 = 2 by decide]
    exact hj
  constructor
  · dsimp only [projection36Phi3R0, projection36Count12, r,
      projection36RemainderRemoved] at h0 ⊢
    norm_num [hz] at h0 ⊢
    linarith
  · dsimp only [projection36Phi3R1, projection36Count12, r,
      projection36RemainderRemoved] at h1 ⊢
    norm_num [hz] at h1 ⊢
    linarith

private theorem remainderCoeff_twelve_high (b : Fin 36 → Int) :
    projection36CyclotomicRemainderCoeff 12 b 0 = projection36Phi12R0 b ∧
    projection36CyclotomicRemainderCoeff 12 b 1 = projection36Phi12R1 b ∧
    projection36CyclotomicRemainderCoeff 12 b 2 = projection36Phi12R2 b ∧
    projection36CyclotomicRemainderCoeff 12 b 3 = projection36Phi12R3 b := by
  let r := projection36RemainderRemoved 12 b
  have hdiv : cyclotomic 12 Int ∣ projection36IndicatorMask r :=
    cyclotomic_dvd_projection36RemainderRemoved 12 b (by
      rw [show Nat.totient 12 = 4 by decide]
      norm_num)
  obtain ⟨h0, h1, h2, h3⟩ := projection36_phi12_count12_remainders r (by
    simpa [projection36IndicatorMask] using hdiv)
  have hz (j : Nat) (hj : 4 ≤ j) :
      projection36CyclotomicRemainderCoeff 12 b j = 0 := by
    apply projection36CyclotomicRemainderCoeff_eq_zero_of_totient_le
    rw [show Nat.totient 12 = 4 by decide]
    exact hj
  constructor
  · dsimp only [projection36Phi12R0, projection36Count12, r,
      projection36RemainderRemoved] at h0 ⊢
    norm_num [hz] at h0 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi12R1, projection36Count12, r,
      projection36RemainderRemoved] at h1 ⊢
    norm_num [hz] at h1 ⊢
    linarith
  constructor
  · dsimp only [projection36Phi12R2, projection36Count12, r,
      projection36RemainderRemoved] at h2 ⊢
    norm_num [hz] at h2 ⊢
    linarith
  · dsimp only [projection36Phi12R3, projection36Count12, r,
      projection36RemainderRemoved] at h3 ⊢
    norm_num [hz] at h3 ⊢
    linarith

theorem projection36_phi3_five_multipliers_high
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 3 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    ∃ k0 k1 : Int,
      projection36Phi3R0 b = 5 * k0 ∧
      projection36Phi3R1 b = 5 * k1 := by
  obtain ⟨k0, hk0⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 0
  obtain ⟨k1, hk1⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 1
  rcases remainderCoeff_three_high b with ⟨h0, h1⟩
  exact ⟨k0, k1, h0.symm.trans hk0, h1.symm.trans hk1⟩

theorem projection36_phi12_five_multipliers_high
    (b : Fin 36 → Int)
    (hdiv : cyclotomic 12 (ZMod 5) ∣
      (projection36IndicatorMask b).map (Int.castRingHom (ZMod 5))) :
    ∃ k0 k1 k2 k3 : Int,
      projection36Phi12R0 b = 5 * k0 ∧
      projection36Phi12R1 b = 5 * k1 ∧
      projection36Phi12R2 b = 5 * k2 ∧
      projection36Phi12R3 b = 5 * k3 := by
  obtain ⟨k0, hk0⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 0
  obtain ⟨k1, hk1⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 1
  obtain ⟨k2, hk2⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 2
  obtain ⟨k3, hk3⟩ :=
    projection36CyclotomicRemainderCoeff_eq_five_mul b hdiv 3
  rcases remainderCoeff_twelve_high b with ⟨h0, h1, h2, h3⟩
  exact ⟨k0, k1, k2, k3, h0.symm.trans hk0, h1.symm.trans hk1,
    h2.symm.trans hk2, h3.symm.trans hk3⟩

#print axioms projection36_phi3_five_multipliers_high
#print axioms projection36_phi12_five_multipliers_high

end Z180K12HighOrder

end Fuglede
