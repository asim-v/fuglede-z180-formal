import Fuglede.Z36Card6TilingCovers
import Fuglede.Z36Card6ForcingIndicator
import Fuglede.Z36Card6ForcingPhi3Phi18Count12Bridge
import Fuglede.Z36Card6ForcingPhi3Phi36Kernel
import Fuglede.Z36Card6ForcingPhi3Phi36Factor
import Fuglede.Z36Card6ForcingPhi36Semantic
import Mathlib.Tactic

/-! The final order `9,12,36` forcing branch; order nine is in fact redundant. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem z36_threecycle_phi12_indicator_antipodal
    (b : Fin 36 → Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hsum : (∑ i : Fin 36, b i) = 6)
    (hcycle : Z36ThreeCycleIndicator b)
    (htwelve : cyclotomic 12 Int ∣ projection36IndicatorMask b) :
    Z36AntipodalIndicator b := by
  obtain ⟨h0, h1, h2, h3⟩ := projection36_phi12_count12_remainders b
    (by simpa [projection36IndicatorMask] using htwelve)
  rcases hcycle with ⟨c0, c12, c1, c13, c2, c14, c3, c15,
    c4, c16, c5, c17, c6, c18, c7, c19, c8, c20,
    c9, c21, c10, c22, c11, c23⟩
  have hb0 := z36_mod6_block_0 b
  have hb1 := z36_mod6_block_1 b
  have hb2 := z36_mod6_block_2 b
  have hb3 := z36_mod6_block_3 b
  have hb4 := z36_mod6_block_4 b
  have hb5 := z36_mod6_block_5 b
  have hblocksum :
      z36Mod6Block b 0 + z36Mod6Block b 1 + z36Mod6Block b 2 +
        z36Mod6Block b 3 + z36Mod6Block b 4 + z36Mod6Block b 5 = 6 := by
    let d0 := z36Mod6Block b 0
    let d1 := z36Mod6Block b 1
    let d2 := z36Mod6Block b 2
    let d3 := z36Mod6Block b 3
    let d4 := z36Mod6Block b 4
    let d5 := z36Mod6Block b 5
    have hvec :
        (∑ r : Fin 6, ![d0, d1, d2, d3, d4, d5] r) =
          ∑ r : Fin 6, z36Mod6Block b r := by
      apply Fintype.sum_congr
      intro r
      fin_cases r <;> dsimp only <;>
        apply congrArg (z36Mod6Block b) <;> apply Fin.ext <;> norm_num
    have hv := hvec.trans (z36_sum36_blocks_mod6 b hsum)
    norm_num [Fin.sum_univ_succ] at hv
    dsimp only [d0, d1, d2, d3, d4, d5] at hv
    linarith only [hv]
  have hbase :
      b 0 + b 1 + b 2 + b 3 + b 4 + b 5 +
        b 6 + b 7 + b 8 + b 9 + b 10 + b 11 = 2 := by
    linarith only [hblocksum, hb0, hb1, hb2, hb3, hb4, hb5,
      c0, c12, c1, c13, c2, c14, c3, c15, c4, c16, c5, c17,
      c6, c18, c7, c19, c8, c20, c9, c21, c10, c22, c11, c23]
  rw [z36_count12_0, z36_count12_4, z36_count12_6,
    z36_count12_10] at h0
  rw [z36_count12_1, z36_count12_5, z36_count12_7,
    z36_count12_11] at h1
  rw [z36_count12_2, z36_count12_4, z36_count12_8,
    z36_count12_10] at h2
  rw [z36_count12_3, z36_count12_5, z36_count12_9,
    z36_count12_11] at h3
  have e0 : b 0 - b 4 - b 6 + b 10 = 0 := by
    linarith only [h0, c0, c12, c4, c16, c6, c18, c10, c22]
  have e1 : b 1 - b 5 - b 7 + b 11 = 0 := by
    linarith only [h1, c1, c13, c5, c17, c7, c19, c11, c23]
  have e2 : b 2 + b 4 - b 8 - b 10 = 0 := by
    linarith only [h2, c2, c14, c4, c16, c8, c20, c10, c22]
  have e3 : b 3 + b 5 - b 9 - b 11 = 0 := by
    linarith only [h3, c3, c15, c5, c17, c9, c21, c11, c23]
  have k := z36_phi3_phi36_fibre_kernel
    (b 0) (b 1) (b 2) (b 3) (b 4) (b 5)
    (b 6) (b 7) (b 8) (b 9) (b 10) (b 11)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    hbase e0 e1 e2 e3
  rcases k with ⟨p0, p1, p2, p3, p4, p5⟩
  have q0 : b 0 = b 18 := p0.trans c6
  have q1 : b 1 = b 19 := p1.trans c7
  have q2 : b 2 = b 20 := p2.trans c8
  have q3 : b 3 = b 21 := p3.trans c9
  have q4 : b 4 = b 22 := p4.trans c10
  have q5 : b 5 = b 23 := p5.trans c11
  have r0 : b 6 = b 24 := p0.symm.trans (c0.trans c12)
  have r1 : b 7 = b 25 := p1.symm.trans (c1.trans c13)
  have r2 : b 8 = b 26 := p2.symm.trans (c2.trans c14)
  have r3 : b 9 = b 27 := p3.symm.trans (c3.trans c15)
  have r4 : b 10 = b 28 := p4.symm.trans (c4.trans c16)
  have r5 : b 11 = b 29 := p5.symm.trans (c5.trans c17)
  have s0 : b 12 = b 30 := c0.symm.trans (p0.trans (c6.trans c18))
  have s1 : b 13 = b 31 := c1.symm.trans (p1.trans (c7.trans c19))
  have s2 : b 14 = b 32 := c2.symm.trans (p2.trans (c8.trans c20))
  have s3 : b 15 = b 33 := c3.symm.trans (p3.trans (c9.trans c21))
  have s4 : b 16 = b 34 := c4.symm.trans (p4.trans (c10.trans c22))
  have s5 : b 17 = b 35 := c5.symm.trans (p5.trans (c11.trans c23))
  exact ⟨q0, q1, q2, q3, q4, q5, r0, r1, r2,
    r3, r4, r5, s0, s1, s2, s3, s4, s5⟩

theorem z36_zero_12_36_forces_4
    (A : Finset (ZMod 36)) (hcard : A.card = 6)
    (htwelve : Z36ZeroAtOrder A 12)
    (hthirtysix : Z36ZeroAtOrder A 36) :
    Z36ZeroAtOrder A 4 := by
  let b := z36MembershipIndicator A
  obtain ⟨hlo, hhi⟩ := z36MembershipIndicator_bounds A
  have hsum : (∑ i : Fin 36, b i) = 6 := by
    simpa [b, hcard] using z36MembershipIndicator_sum A
  have hmask : projection36IndicatorMask b = maskPolynomial 36 A :=
    by simpa [b] using projection36IndicatorMask_z36MembershipIndicator A
  have hdiv12 : cyclotomic 12 Int ∣ projection36IndicatorMask b := by
    simpa [Z36ZeroAtOrder, hmask] using htwelve
  have hdiv36 : cyclotomic 36 Int ∣ projection36IndicatorMask b := by
    simpa [Z36ZeroAtOrder, hmask] using hthirtysix
  have hperiod := z36_phi36_indicator_period_dichotomy b hlo hhi hsum hdiv36
  have hanti : Z36AntipodalIndicator b := by
    rcases hperiod with hanti | hcycle
    · exact hanti
    · exact z36_threecycle_phi12_indicator_antipodal
        b hlo hhi hsum hcycle hdiv12
  have hdiv4 := (z36_antipodal_forces_phi4_phi12 b hanti).1
  simpa [Z36ZeroAtOrder, hmask] using hdiv4

theorem z36_zero_9_12_36_forces_4
    (A : Finset (ZMod 36)) (hcard : A.card = 6)
    (_hnine : Z36ZeroAtOrder A 9)
    (htwelve : Z36ZeroAtOrder A 12)
    (hthirtysix : Z36ZeroAtOrder A 36) :
    Z36ZeroAtOrder A 4 :=
  z36_zero_12_36_forces_4 A hcard htwelve hthirtysix

#print axioms z36_zero_12_36_forces_4
#print axioms z36_zero_9_12_36_forces_4

end Fuglede
