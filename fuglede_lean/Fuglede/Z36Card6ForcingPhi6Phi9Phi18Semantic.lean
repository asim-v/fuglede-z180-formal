import Fuglede.Z36Card6TilingCovers
import Fuglede.Z36Card6ForcingIndicator
import Fuglede.Z36Card6ForcingPhi6Phi9Phi18Kernel
import Fuglede.Z36Card6ForcingParityFactor
import Fuglede.Z36Card6ForcingPhi36BlockBridge
import Fuglede.Z36Card6ForcingPhi36SumKernel
import Fuglede.Z180K12Projection36Remainders18
import Mathlib.Tactic

/-! Semantic assembly of the last cardinality-six forcing branch. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z36_phi6_phi9_phi18_indicator_parity_balance
    (b : Fin 36 → Int)
    (hlo : ∀ i, 0 ≤ b i)
    (hsum : (∑ i : Fin 36, b i) = 6)
    (hsix : cyclotomic 6 Int ∣ projection36IndicatorMask b)
    (hnine : cyclotomic 9 Int ∣ projection36IndicatorMask b)
    (heighteen : cyclotomic 18 Int ∣ projection36IndicatorMask b) :
    z36Mod6Block b 0 + z36Mod6Block b 2 + z36Mod6Block b 4 =
      z36Mod6Block b 1 + z36Mod6Block b 3 + z36Mod6Block b 5 := by
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := projection36_phi9_remainders b
    (by simpa [projection36IndicatorMask] using hnine)
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := projection36_phi18_remainders b
    (by simpa [projection36IndicatorMask] using heighteen)
  obtain ⟨f0, f1⟩ :=
    (projection36_phi6_dvd_iff_remainders_zero b).mp hsix
  dsimp only [projection36Phi6R0] at f0
  dsimp only [projection36Phi6R1] at f1
  let n0 := b 0 + b 9 + b 18 + b 27
  let n1 := b 1 + b 10 + b 19 + b 28
  let n2 := b 2 + b 11 + b 20 + b 29
  let n3 := b 3 + b 12 + b 21 + b 30
  let n4 := b 4 + b 13 + b 22 + b 31
  let n5 := b 5 + b 14 + b 23 + b 32
  let n6 := b 6 + b 15 + b 24 + b 33
  let n7 := b 7 + b 16 + b 25 + b 34
  let n8 := b 8 + b 17 + b 26 + b 35
  let s0 := b 0 + b 18 - b 9 - b 27
  let s1 := b 10 + b 28 - b 1 - b 19
  let s2 := b 2 + b 20 - b 11 - b 29
  let s3 := b 12 + b 30 - b 3 - b 21
  let s4 := b 4 + b 22 - b 13 - b 31
  let s5 := b 14 + b 32 - b 5 - b 23
  let s6 := b 6 + b 24 - b 15 - b 33
  let s7 := b 16 + b 34 - b 7 - b 25
  let s8 := b 8 + b 26 - b 17 - b 35
  have hn06 : n0 = n6 := by
    dsimp only [n0, n6]
    linarith only [g0]
  have hn36 : n3 = n6 := by
    dsimp only [n3, n6]
    linarith only [g3]
  have hn17 : n1 = n7 := by
    dsimp only [n1, n7]
    linarith only [g1]
  have hn47 : n4 = n7 := by
    dsimp only [n4, n7]
    linarith only [g4]
  have hn28 : n2 = n8 := by
    dsimp only [n2, n8]
    linarith only [g2]
  have hn58 : n5 = n8 := by
    dsimp only [n5, n8]
    linarith only [g5]
  have hs06 : s0 = s6 := by
    dsimp only [s0, s6]
    linarith only [e0]
  have hs36 : s3 = s6 := by
    dsimp only [s3, s6]
    linarith only [e3]
  have hs17 : s1 = s7 := by
    dsimp only [s1, s7]
    linarith only [e1]
  have hs47 : s4 = s7 := by
    dsimp only [s4, s7]
    linarith only [e4]
  have hs28 : s2 = s8 := by
    dsimp only [s2, s8]
    linarith only [e2]
  have hs58 : s5 = s8 := by
    dsimp only [s5, s8]
    linarith only [e5]
  have hf0 : s0 - s2 + s3 - s5 + s6 - s8 = 0 := by
    dsimp only [s0, s2, s3, s5, s6, s8]
    linarith only [f0]
  have hf1 : -s1 + s2 - s4 + s5 - s7 + s8 = 0 := by
    dsimp only [s1, s2, s4, s5, s7, s8]
    linarith only [f1]
  have hs02 : s0 = s2 := by
    linarith only [hf0, hs06, hs36, hs28, hs58]
  have hs12 : s1 = s2 := by
    linarith only [hf1, hs17, hs47, hs28, hs58]
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
  have hnSum : n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 = 6 := by
    dsimp only [n0, n1, n2, n3, n4, n5, n6, n7, n8]
    linarith only [hblocksum, hb0, hb1, hb2, hb3, hb4, hb5]
  have hmass : 3 * (n0 + n1 + n2) = 6 := by
    linarith only [hnSum, hn06, hn36, hn17, hn47, hn28, hn58]
  have hn0 : 0 ≤ n0 := by
    dsimp only [n0]
    linarith only [hlo 0, hlo 9, hlo 18, hlo 27]
  have hn1 : 0 ≤ n1 := by
    dsimp only [n1]
    linarith only [hlo 1, hlo 10, hlo 19, hlo 28]
  have hn2 : 0 ≤ n2 := by
    dsimp only [n2]
    linarith only [hlo 2, hlo 11, hlo 20, hlo 29]
  have h0l : -n0 ≤ s0 := by
    dsimp only [n0, s0]
    linarith only [hlo 0, hlo 18]
  have h0u : s0 ≤ n0 := by
    dsimp only [n0, s0]
    linarith only [hlo 9, hlo 27]
  have h1l' : -n1 ≤ s1 := by
    dsimp only [n1, s1]
    linarith only [hlo 10, hlo 28]
  have h1u' : s1 ≤ n1 := by
    dsimp only [n1, s1]
    linarith only [hlo 1, hlo 19]
  have h2l' : -n2 ≤ s2 := by
    dsimp only [n2, s2]
    linarith only [hlo 2, hlo 20]
  have h2u' : s2 ≤ n2 := by
    dsimp only [n2, s2]
    linarith only [hlo 11, hlo 29]
  have h1l : -n1 ≤ s0 := by linarith only [h1l', hs12, hs02]
  have h1u : s0 ≤ n1 := by linarith only [h1u', hs12, hs02]
  have h2l : -n2 ≤ s0 := by linarith only [h2l', hs02]
  have h2u : s0 ≤ n2 := by linarith only [h2u', hs02]
  have hz := z36_phi6_phi9_phi18_signed_kernel
    n0 n1 n2 s0 hn0 hn1 hn2 hmass h0l h0u h1l h1u h2l h2u
  have z0 : s0 = 0 := hz
  have z1 : s1 = 0 := by linarith only [z0, hs12, hs02]
  have z2 : s2 = 0 := by linarith only [z0, hs02]
  have z3 : s3 = 0 := by linarith only [z0, hs06, hs36]
  have z4 : s4 = 0 := by linarith only [z1, hs17, hs47]
  have z5 : s5 = 0 := by linarith only [z2, hs28, hs58]
  have z6 : s6 = 0 := by linarith only [z0, hs06]
  have z7 : s7 = 0 := by linarith only [z1, hs17]
  have z8 : s8 = 0 := by linarith only [z2, hs28]
  rw [z36_mod6_block_0, z36_mod6_block_1, z36_mod6_block_2,
    z36_mod6_block_3, z36_mod6_block_4, z36_mod6_block_5]
  dsimp only [s0, s1, s2, s3, s4, s5, s6, s7, s8] at z0 z1 z2 z3 z4 z5 z6 z7 z8
  linarith only [z0, z1, z2, z3, z4, z5, z6, z7, z8]

theorem z36_zero_6_9_18_forces_2
    (A : Finset (ZMod 36)) (hcard : A.card = 6)
    (hsix : Z36ZeroAtOrder A 6)
    (hnine : Z36ZeroAtOrder A 9)
    (heighteen : Z36ZeroAtOrder A 18) :
    Z36ZeroAtOrder A 2 := by
  let b := z36MembershipIndicator A
  obtain ⟨hlo, _hhi⟩ := z36MembershipIndicator_bounds A
  have hsum : (∑ i : Fin 36, b i) = 6 := by
    simpa [b, hcard] using z36MembershipIndicator_sum A
  have hmask : projection36IndicatorMask b = maskPolynomial 36 A :=
    by simpa [b] using projection36IndicatorMask_z36MembershipIndicator A
  have hbalance := z36_phi6_phi9_phi18_indicator_parity_balance b hlo hsum
    (by simpa [Z36ZeroAtOrder, hmask] using hsix)
    (by simpa [Z36ZeroAtOrder, hmask] using hnine)
    (by simpa [Z36ZeroAtOrder, hmask] using heighteen)
  have hdiv := z36_parity_balance_forces_phi2 b hbalance
  simpa [Z36ZeroAtOrder, hmask] using hdiv

#print axioms z36_phi6_phi9_phi18_indicator_parity_balance
#print axioms z36_zero_6_9_18_forces_2

end Fuglede
