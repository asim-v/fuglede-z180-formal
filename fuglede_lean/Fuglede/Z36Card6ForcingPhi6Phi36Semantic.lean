import Fuglede.Z36Card6ForcingPhi36Semantic
import Fuglede.Z36Card6ForcingParityFactor
import Fuglede.Z180K12DescentOrder3Converse

/-!
# The remaining `Phi_6`--`Phi_36` forcing implication

For a six-point indicator, a `Phi_36` zero gives either antipodal pairs or
three-cycles.  Adding a `Phi_6` zero forces `Phi_3` in the antipodal branch
and `Phi_2` in the three-cycle branch.
-/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem nonnegative_phi6_mass_three_forces_alternation
    (d0 d1 d2 d3 d4 d5 : Int)
    (dn0 : 0 ≤ d0) (dn1 : 0 ≤ d1) (dn2 : 0 ≤ d2)
    (dn3 : 0 ≤ d3) (dn4 : 0 ≤ d4) (dn5 : 0 ≤ d5)
    (hs : d0 + d1 + d2 + d3 + d4 + d5 = 3)
    (h0 : d0 - d2 - d3 + d5 = 0)
    (h1 : d1 + d2 - d4 - d5 = 0) :
    d0 + d3 = d2 + d5 ∧ d1 + d4 = d2 + d5 := by
  have du0 : d0 ≤ 3 := by omega
  have du1 : d1 ≤ 3 := by omega
  have du2 : d2 ≤ 3 := by omega
  have du3 : d3 ≤ 3 := by omega
  have du4 : d4 ≤ 3 := by omega
  have du5 : d5 ≤ 3 := by omega
  interval_cases d0 <;> interval_cases d1 <;> interval_cases d2 <;>
    interval_cases d3 <;> interval_cases d4 <;> interval_cases d5 <;> omega

theorem z36_zero_6_36_forces_2_or_3
    (A : Finset (ZMod 36)) (hcard : A.card = 6)
    (h6 : Z36ZeroAtOrder A 6) (h36 : Z36ZeroAtOrder A 36) :
    Z36ZeroAtOrder A 2 ∨ Z36ZeroAtOrder A 3 := by
  let b := z36MembershipIndicator A
  obtain ⟨hlo, hhi⟩ := z36MembershipIndicator_bounds A
  have hsum : (∑ i : Fin 36, b i) = 6 := by
    rw [z36MembershipIndicator_sum, hcard]
    norm_num
  have hdiv6 : cyclotomic 6 Int ∣ projection36IndicatorMask b := by
    rw [projection36IndicatorMask_z36MembershipIndicator]
    exact h6
  have hdiv36 : cyclotomic 36 Int ∣ projection36IndicatorMask b := by
    rw [projection36IndicatorMask_z36MembershipIndicator]
    exact h36
  obtain ⟨f0, f1⟩ :=
    (projection36_phi6_dvd_iff_remainders_zero b).mp hdiv6
  rcases z36_phi36_indicator_period_dichotomy b hlo hhi hsum hdiv36 with
    hanti | hcycle
  · right
    rcases hanti with ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8,
      a9, a10, a11, a12, a13, a14, a15, a16, a17⟩
    let m0 := z36Mod6Block b 0
    let m1 := z36Mod6Block b 1
    let m2 := z36Mod6Block b 2
    let m3 := z36Mod6Block b 3
    let m4 := z36Mod6Block b 4
    let m5 := z36Mod6Block b 5
    let d0 := b 0 + b 6 + b 12
    let d1 := b 1 + b 7 + b 13
    let d2 := b 2 + b 8 + b 14
    let d3 := b 3 + b 9 + b 15
    let d4 := b 4 + b 10 + b 16
    let d5 := b 5 + b 11 + b 17
    have me0 : m0 = b 0 + b 6 + b 12 + b 18 + b 24 + b 30 := by
      simpa [m0] using z36_mod6_block_0 b
    have me1 : m1 = b 1 + b 7 + b 13 + b 19 + b 25 + b 31 := by
      simpa [m1] using z36_mod6_block_1 b
    have me2 : m2 = b 2 + b 8 + b 14 + b 20 + b 26 + b 32 := by
      simpa [m2] using z36_mod6_block_2 b
    have me3 : m3 = b 3 + b 9 + b 15 + b 21 + b 27 + b 33 := by
      simpa [m3] using z36_mod6_block_3 b
    have me4 : m4 = b 4 + b 10 + b 16 + b 22 + b 28 + b 34 := by
      simpa [m4] using z36_mod6_block_4 b
    have me5 : m5 = b 5 + b 11 + b 17 + b 23 + b 29 + b 35 := by
      simpa [m5] using z36_mod6_block_5 b
    have mt0 : m0 = 2 * d0 := by dsimp only [d0]; linarith only [me0, a0, a6, a12]
    have mt1 : m1 = 2 * d1 := by dsimp only [d1]; linarith only [me1, a1, a7, a13]
    have mt2 : m2 = 2 * d2 := by dsimp only [d2]; linarith only [me2, a2, a8, a14]
    have mt3 : m3 = 2 * d3 := by dsimp only [d3]; linarith only [me3, a3, a9, a15]
    have mt4 : m4 = 2 * d4 := by dsimp only [d4]; linarith only [me4, a4, a10, a16]
    have mt5 : m5 = 2 * d5 := by dsimp only [d5]; linarith only [me5, a5, a11, a17]
    have dn0 : 0 ≤ d0 := by dsimp only [d0]; exact add_nonneg (add_nonneg (hlo 0) (hlo 6)) (hlo 12)
    have dn1 : 0 ≤ d1 := by dsimp only [d1]; exact add_nonneg (add_nonneg (hlo 1) (hlo 7)) (hlo 13)
    have dn2 : 0 ≤ d2 := by dsimp only [d2]; exact add_nonneg (add_nonneg (hlo 2) (hlo 8)) (hlo 14)
    have dn3 : 0 ≤ d3 := by dsimp only [d3]; exact add_nonneg (add_nonneg (hlo 3) (hlo 9)) (hlo 15)
    have dn4 : 0 ≤ d4 := by dsimp only [d4]; exact add_nonneg (add_nonneg (hlo 4) (hlo 10)) (hlo 16)
    have dn5 : 0 ≤ d5 := by dsimp only [d5]; exact add_nonneg (add_nonneg (hlo 5) (hlo 11)) (hlo 17)
    have hmsum : m0 + m1 + m2 + m3 + m4 + m5 = 6 := by
      have hs := z36_sum36_blocks_mod6 b hsum
      norm_num [Fin.sum_univ_succ, m0, m1, m2, m3, m4, m5] at hs
      have hs' : z36Mod6Block b 0 + (z36Mod6Block b 1 +
          (z36Mod6Block b 2 + (z36Mod6Block b 3 +
            (z36Mod6Block b 4 + z36Mod6Block b 5)))) = 6 := by
        simpa only [
          show Fin.succ (2 : Fin 5) = (3 : Fin 6) by rfl,
          show Fin.succ (Fin.succ (2 : Fin 4)) = (4 : Fin 6) by rfl,
          show Fin.succ (Fin.succ (Fin.succ (2 : Fin 3))) = (5 : Fin 6) by rfl
        ] using hs
      dsimp only [m0, m1, m2, m3, m4, m5]
      linarith only [hs']
    have hmf0 : m0 - m2 - m3 + m5 = 0 := by
      dsimp only [projection36Phi6R0] at f0
      linarith only [f0, me0, me2, me3, me5]
    have hmf1 : m1 + m2 - m4 - m5 = 0 := by
      dsimp only [projection36Phi6R1] at f1
      linarith only [f1, me1, me2, me4, me5]
    have hdsum : d0 + d1 + d2 + d3 + d4 + d5 = 3 := by
      omega
    have hdf0 : d0 - d2 - d3 + d5 = 0 := by omega
    have hdf1 : d1 + d2 - d4 - d5 = 0 := by omega
    obtain ⟨hd03, hd14⟩ := nonnegative_phi6_mass_three_forces_alternation
      d0 d1 d2 d3 d4 d5 dn0 dn1 dn2 dn3 dn4 dn5 hdsum hdf0 hdf1
    have hm03 : m0 + m3 = m2 + m5 := by omega
    have hm14 : m1 + m4 = m2 + m5 := by omega
    have z0 : Z180K12HighOrder.projection36Phi3R0 b = 0 := by
      change
        (b 0 + b 12 + b 24) - (b 2 + b 14 + b 26) +
          (b 3 + b 15 + b 27) - (b 5 + b 17 + b 29) +
          (b 6 + b 18 + b 30) - (b 8 + b 20 + b 32) +
          (b 9 + b 21 + b 33) - (b 11 + b 23 + b 35) = 0
      linarith only [hm03, me0, me2, me3, me5]
    have z1 : Z180K12HighOrder.projection36Phi3R1 b = 0 := by
      change
        (b 1 + b 13 + b 25) - (b 2 + b 14 + b 26) +
          (b 4 + b 16 + b 28) - (b 5 + b 17 + b 29) +
          (b 7 + b 19 + b 31) - (b 8 + b 20 + b 32) +
          (b 10 + b 22 + b 34) - (b 11 + b 23 + b 35) = 0
      linarith only [hm14, me1, me2, me4, me5]
    have hd :=
      Z180K12HighOrder.cyclotomic_three_dvd_projection36Indicator_of_remainders_zero_direct
        b ⟨z0, z1⟩
    rw [projection36IndicatorMask_z36MembershipIndicator] at hd
    exact hd
  · left
    rcases hcycle with ⟨c0, c12, c1, c13, c2, c14, c3, c15,
      c4, c16, c5, c17, c6, c18, c7, c19, c8, c20,
      c9, c21, c10, c22, c11, c23⟩
    let m0 := z36Mod6Block b 0
    let m1 := z36Mod6Block b 1
    let m2 := z36Mod6Block b 2
    let m3 := z36Mod6Block b 3
    let m4 := z36Mod6Block b 4
    let m5 := z36Mod6Block b 5
    let d0 := b 0 + b 6
    let d1 := b 1 + b 7
    let d2 := b 2 + b 8
    let d3 := b 3 + b 9
    let d4 := b 4 + b 10
    let d5 := b 5 + b 11
    have me0 : m0 = b 0 + b 6 + b 12 + b 18 + b 24 + b 30 := by
      simpa [m0] using z36_mod6_block_0 b
    have me1 : m1 = b 1 + b 7 + b 13 + b 19 + b 25 + b 31 := by
      simpa [m1] using z36_mod6_block_1 b
    have me2 : m2 = b 2 + b 8 + b 14 + b 20 + b 26 + b 32 := by
      simpa [m2] using z36_mod6_block_2 b
    have me3 : m3 = b 3 + b 9 + b 15 + b 21 + b 27 + b 33 := by
      simpa [m3] using z36_mod6_block_3 b
    have me4 : m4 = b 4 + b 10 + b 16 + b 22 + b 28 + b 34 := by
      simpa [m4] using z36_mod6_block_4 b
    have me5 : m5 = b 5 + b 11 + b 17 + b 23 + b 29 + b 35 := by
      simpa [m5] using z36_mod6_block_5 b
    have mt0 : m0 = 3 * d0 := by dsimp only [d0]; linarith only [me0, c0, c12, c6, c18]
    have mt1 : m1 = 3 * d1 := by dsimp only [d1]; linarith only [me1, c1, c13, c7, c19]
    have mt2 : m2 = 3 * d2 := by dsimp only [d2]; linarith only [me2, c2, c14, c8, c20]
    have mt3 : m3 = 3 * d3 := by dsimp only [d3]; linarith only [me3, c3, c15, c9, c21]
    have mt4 : m4 = 3 * d4 := by dsimp only [d4]; linarith only [me4, c4, c16, c10, c22]
    have mt5 : m5 = 3 * d5 := by dsimp only [d5]; linarith only [me5, c5, c17, c11, c23]
    have dn0 : 0 ≤ d0 := by dsimp only [d0]; exact add_nonneg (hlo 0) (hlo 6)
    have dn1 : 0 ≤ d1 := by dsimp only [d1]; exact add_nonneg (hlo 1) (hlo 7)
    have dn2 : 0 ≤ d2 := by dsimp only [d2]; exact add_nonneg (hlo 2) (hlo 8)
    have dn3 : 0 ≤ d3 := by dsimp only [d3]; exact add_nonneg (hlo 3) (hlo 9)
    have dn4 : 0 ≤ d4 := by dsimp only [d4]; exact add_nonneg (hlo 4) (hlo 10)
    have dn5 : 0 ≤ d5 := by dsimp only [d5]; exact add_nonneg (hlo 5) (hlo 11)
    have hmsum : m0 + m1 + m2 + m3 + m4 + m5 = 6 := by
      have hs := z36_sum36_blocks_mod6 b hsum
      norm_num [Fin.sum_univ_succ, m0, m1, m2, m3, m4, m5] at hs
      have hs' : z36Mod6Block b 0 + (z36Mod6Block b 1 +
          (z36Mod6Block b 2 + (z36Mod6Block b 3 +
            (z36Mod6Block b 4 + z36Mod6Block b 5)))) = 6 := by
        simpa only [
          show Fin.succ (2 : Fin 5) = (3 : Fin 6) by rfl,
          show Fin.succ (Fin.succ (2 : Fin 4)) = (4 : Fin 6) by rfl,
          show Fin.succ (Fin.succ (Fin.succ (2 : Fin 3))) = (5 : Fin 6) by rfl
        ] using hs
      dsimp only [m0, m1, m2, m3, m4, m5]
      linarith only [hs']
    have hmf0 : m0 - m2 - m3 + m5 = 0 := by
      dsimp only [projection36Phi6R0] at f0
      linarith only [f0, me0, me2, me3, me5]
    have hmf1 : m1 + m2 - m4 - m5 = 0 := by
      dsimp only [projection36Phi6R1] at f1
      linarith only [f1, me1, me2, me4, me5]
    have hparity : m0 + m2 + m4 = m1 + m3 + m5 := by omega
    have hbalance :
        z36Mod6Block b 0 + z36Mod6Block b 2 + z36Mod6Block b 4 =
          z36Mod6Block b 1 + z36Mod6Block b 3 + z36Mod6Block b 5 := by
      exact hparity
    have hd := z36_parity_balance_forces_phi2 b hbalance
    rw [projection36IndicatorMask_z36MembershipIndicator] at hd
    exact hd

#print axioms z36_zero_6_36_forces_2_or_3

end Fuglede
