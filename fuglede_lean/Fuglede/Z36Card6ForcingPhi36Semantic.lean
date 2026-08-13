import Fuglede.Z36Card6TilingCovers
import Fuglede.Z36Card6ForcingIndicator
import Fuglede.Z36Card6ForcingPhi36BlockKernel
import Fuglede.Z36Card6ForcingPhi36MassKernel
import Fuglede.Z36Card6ForcingPhi36SumKernel
import Fuglede.Z36Card6ForcingPhi36BlockBridge
import Fuglede.Z36Card6ForcingPhi36Factor12
import Fuglede.Z36Card6ForcingPhi36Factor18
import Mathlib.Tactic

/-! Semantic assembly of the cardinality-six `Phi_36` dichotomy. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem z36_block_anti_of_ne_three
    (a0 a1 a2 a3 a4 a5 : Int)
    (hk : (a0 = a3 ∧ a1 = a4 ∧ a2 = a5) ∨
      ((a0 = a2 ∧ a2 = a4 ∧ a1 = a3 ∧ a3 = a5) ∧
        a0 + a1 + a2 + a3 + a4 + a5 = 3))
    (hne : a0 + a1 + a2 + a3 + a4 + a5 ≠ 3) :
    a0 = a3 ∧ a1 = a4 ∧ a2 = a5 := by
  rcases hk with hanti | hcycle
  · exact hanti
  · exact (hne hcycle.2).elim

private theorem z36_block_cycle_of_mass_zero_or_three
    (a0 a1 a2 a3 a4 a5 : Int)
    (h0l : 0 ≤ a0) (h0u : a0 ≤ 1)
    (h1l : 0 ≤ a1) (h1u : a1 ≤ 1)
    (h2l : 0 ≤ a2) (h2u : a2 ≤ 1)
    (h3l : 0 ≤ a3) (h3u : a3 ≤ 1)
    (h4l : 0 ≤ a4) (h4u : a4 ≤ 1)
    (h5l : 0 ≤ a5) (h5u : a5 ≤ 1)
    (hk : (a0 = a3 ∧ a1 = a4 ∧ a2 = a5) ∨
      ((a0 = a2 ∧ a2 = a4 ∧ a1 = a3 ∧ a3 = a5) ∧
        a0 + a1 + a2 + a3 + a4 + a5 = 3))
    (hmass : a0 + a1 + a2 + a3 + a4 + a5 = 0 ∨
      a0 + a1 + a2 + a3 + a4 + a5 = 3) :
    a0 = a2 ∧ a2 = a4 ∧ a1 = a3 ∧ a3 = a5 := by
  rcases hmass with hzero | hthree
  · omega
  · rcases hk with hanti | hcycle
    · omega
    · exact hcycle.1

theorem z36_phi36_indicator_period_dichotomy
    (b : Fin 36 → Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hsum : (∑ i : Fin 36, b i) = 6)
    (hdiv : cyclotomic 36 Int ∣ projection36IndicatorMask b) :
    Z36AntipodalIndicator b ∨ Z36ThreeCycleIndicator b := by
  rcases projection36_phi36_remainders b
      (by simpa [projection36IndicatorMask] using hdiv) with
    ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩
  have k0 := z36_phi36_block_classify (b 0) (b 6) (b 12) (b 18) (b 24) (b 30)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e0 e6
  have k1 := z36_phi36_block_classify (b 1) (b 7) (b 13) (b 19) (b 25) (b 31)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e1 e7
  have k2 := z36_phi36_block_classify (b 2) (b 8) (b 14) (b 20) (b 26) (b 32)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e2 e8
  have k3 := z36_phi36_block_classify (b 3) (b 9) (b 15) (b 21) (b 27) (b 33)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e3 e9
  have k4 := z36_phi36_block_classify (b 4) (b 10) (b 16) (b 22) (b 28) (b 34)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e4 e10
  have k5 := z36_phi36_block_classify (b 5) (b 11) (b 17) (b 23) (b 29) (b 35)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e5 e11
  let c0 := z36Mod6Block b 0
  let c1 := z36Mod6Block b 1
  let c2 := z36Mod6Block b 2
  let c3 := z36Mod6Block b 3
  let c4 := z36Mod6Block b 4
  let c5 := z36Mod6Block b 5
  have m0 : c0 = 0 ∨ c0 = 2 ∨ c0 = 3 ∨ c0 = 4 ∨ c0 = 6 := by
    simpa [c0, z36_mod6_block_0] using z36_phi36_block_mass_cases
      (b 0) (b 6) (b 12) (b 18) (b 24) (b 30)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e0 e6
  have m1 : c1 = 0 ∨ c1 = 2 ∨ c1 = 3 ∨ c1 = 4 ∨ c1 = 6 := by
    simpa [c1, z36_mod6_block_1] using z36_phi36_block_mass_cases
      (b 1) (b 7) (b 13) (b 19) (b 25) (b 31)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e1 e7
  have m2 : c2 = 0 ∨ c2 = 2 ∨ c2 = 3 ∨ c2 = 4 ∨ c2 = 6 := by
    simpa [c2, z36_mod6_block_2] using z36_phi36_block_mass_cases
      (b 2) (b 8) (b 14) (b 20) (b 26) (b 32)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e2 e8
  have m3 : c3 = 0 ∨ c3 = 2 ∨ c3 = 3 ∨ c3 = 4 ∨ c3 = 6 := by
    simpa [c3, z36_mod6_block_3] using z36_phi36_block_mass_cases
      (b 3) (b 9) (b 15) (b 21) (b 27) (b 33)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e3 e9
  have m4 : c4 = 0 ∨ c4 = 2 ∨ c4 = 3 ∨ c4 = 4 ∨ c4 = 6 := by
    simpa [c4, z36_mod6_block_4] using z36_phi36_block_mass_cases
      (b 4) (b 10) (b 16) (b 22) (b 28) (b 34)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e4 e10
  have m5 : c5 = 0 ∨ c5 = 2 ∨ c5 = 3 ∨ c5 = 4 ∨ c5 = 6 := by
    simpa [c5, z36_mod6_block_5] using z36_phi36_block_mass_cases
      (b 5) (b 11) (b 17) (b 23) (b 29) (b 35)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) e5 e11
  have hcsum : c0 + c1 + c2 + c3 + c4 + c5 = 6 := by
    have hvec :
        (∑ r : Fin 6, ![c0, c1, c2, c3, c4, c5] r) =
          ∑ r : Fin 6, z36Mod6Block b r := by
      apply Fintype.sum_congr
      intro r
      fin_cases r <;> dsimp only <;>
        apply congrArg (z36Mod6Block b) <;> apply Fin.ext <;> norm_num
    have hv := hvec.trans (z36_sum36_blocks_mod6 b hsum)
    norm_num [Fin.sum_univ_succ] at hv
    linarith only [hv]
  rcases z36_phi36_block_masses_dichotomy c0 c1 c2 c3 c4 c5
      m0 m1 m2 m3 m4 m5 hcsum with hne | h03
  · left
    rcases hne with ⟨n0, n1, n2, n3, n4, n5⟩
    have a0 := z36_block_anti_of_ne_three _ _ _ _ _ _ k0
      (by simpa [c0, z36_mod6_block_0] using n0)
    have a1 := z36_block_anti_of_ne_three _ _ _ _ _ _ k1
      (by simpa [c1, z36_mod6_block_1] using n1)
    have a2 := z36_block_anti_of_ne_three _ _ _ _ _ _ k2
      (by simpa [c2, z36_mod6_block_2] using n2)
    have a3 := z36_block_anti_of_ne_three _ _ _ _ _ _ k3
      (by simpa [c3, z36_mod6_block_3] using n3)
    have a4 := z36_block_anti_of_ne_three _ _ _ _ _ _ k4
      (by simpa [c4, z36_mod6_block_4] using n4)
    have a5 := z36_block_anti_of_ne_three _ _ _ _ _ _ k5
      (by simpa [c5, z36_mod6_block_5] using n5)
    rcases a0 with ⟨a00, a06, a012⟩
    rcases a1 with ⟨a01, a07, a013⟩
    rcases a2 with ⟨a02, a08, a014⟩
    rcases a3 with ⟨a03, a09, a015⟩
    rcases a4 with ⟨a04, a010, a016⟩
    rcases a5 with ⟨a05, a011, a017⟩
    exact ⟨a00, a01, a02, a03, a04, a05, a06, a07, a08,
      a09, a010, a011, a012, a013, a014, a015, a016, a017⟩
  · right
    rcases h03 with ⟨d0, d1, d2, d3, d4, d5⟩
    have a0 := z36_block_cycle_of_mass_zero_or_three
      (b 0) (b 6) (b 12) (b 18) (b 24) (b 30)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) k0
      (by simpa [c0, z36_mod6_block_0] using d0)
    have a1 := z36_block_cycle_of_mass_zero_or_three
      (b 1) (b 7) (b 13) (b 19) (b 25) (b 31)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) k1
      (by simpa [c1, z36_mod6_block_1] using d1)
    have a2 := z36_block_cycle_of_mass_zero_or_three
      (b 2) (b 8) (b 14) (b 20) (b 26) (b 32)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) k2
      (by simpa [c2, z36_mod6_block_2] using d2)
    have a3 := z36_block_cycle_of_mass_zero_or_three
      (b 3) (b 9) (b 15) (b 21) (b 27) (b 33)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) k3
      (by simpa [c3, z36_mod6_block_3] using d3)
    have a4 := z36_block_cycle_of_mass_zero_or_three
      (b 4) (b 10) (b 16) (b 22) (b 28) (b 34)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) k4
      (by simpa [c4, z36_mod6_block_4] using d4)
    have a5 := z36_block_cycle_of_mass_zero_or_three
      (b 5) (b 11) (b 17) (b 23) (b 29) (b 35)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
      (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _) k5
      (by simpa [c5, z36_mod6_block_5] using d5)
    rcases a0 with ⟨a00, a012, a06, a018⟩
    rcases a1 with ⟨a01, a013, a07, a019⟩
    rcases a2 with ⟨a02, a014, a08, a020⟩
    rcases a3 with ⟨a03, a015, a09, a021⟩
    rcases a4 with ⟨a04, a016, a010, a022⟩
    rcases a5 with ⟨a05, a017, a011, a023⟩
    exact ⟨a00, a012, a01, a013, a02, a014, a03, a015,
      a04, a016, a05, a017, a06, a018, a07, a019,
      a08, a020, a09, a021, a010, a022, a011, a023⟩

theorem z36_zero_36_forces_12_or_18
    (A : Finset (ZMod 36)) (hcard : A.card = 6)
    (h36 : Z36ZeroAtOrder A 36) :
    Z36ZeroAtOrder A 12 ∨ Z36ZeroAtOrder A 18 := by
  let b := z36MembershipIndicator A
  obtain ⟨hlo, hhi⟩ := z36MembershipIndicator_bounds A
  have hsum : (∑ i : Fin 36, b i) = 6 := by
    rw [z36MembershipIndicator_sum, hcard]
    norm_num
  have hdiv36 : cyclotomic 36 Int ∣ projection36IndicatorMask b := by
    rw [projection36IndicatorMask_z36MembershipIndicator]
    exact h36
  rcases z36_phi36_indicator_period_dichotomy b hlo hhi hsum hdiv36 with
    hanti | hcycle
  · left
    have hd := z36_cyclotomic_twelve_dvd_of_antipodal b hanti
    rw [projection36IndicatorMask_z36MembershipIndicator] at hd
    exact hd
  · right
    have hd := z36_cyclotomic_eighteen_dvd_of_three_cycle b hcycle
    rw [projection36IndicatorMask_z36MembershipIndicator] at hd
    exact hd

#print axioms z36_phi36_indicator_period_dichotomy
#print axioms z36_zero_36_forces_12_or_18

end Fuglede
