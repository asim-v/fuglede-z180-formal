import Fuglede.Z36Card6TilingCovers
import Fuglede.Z36Card6ForcingIndicator
import Fuglede.Z36Card6ForcingPhi3Phi18Count12Bridge
import Fuglede.Z36Card6ForcingPhi3Phi36Kernel
import Fuglede.Z36Card6ForcingPhi3Phi36Factor
import Fuglede.Z36Card6ForcingPhi36BlockBridge
import Fuglede.Z36Card6ForcingPhi36SumKernel
import Fuglede.Z180K12Projection36Remainders36
import Mathlib.Tactic

/-! Semantic assembly of the cardinality-six `Phi_3` plus `Phi_36` branch. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z36_phi3_phi36_indicator_antipodal
    (b : Fin 36 → Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hsum : (∑ i : Fin 36, b i) = 6)
    (hthree : cyclotomic 3 Int ∣ projection36IndicatorMask b)
    (hthirtysix : cyclotomic 36 Int ∣ projection36IndicatorMask b) :
    Z36AntipodalIndicator b := by
  obtain ⟨h30, h31⟩ := projection36_phi3_count12_remainders b
    (by simpa [projection36IndicatorMask] using hthree)
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ :=
    projection36_phi36_remainders b
      (by simpa [projection36IndicatorMask] using hthirtysix)
  have hb0 := z36_mod6_block_0 b
  have hb1 := z36_mod6_block_1 b
  have hb2 := z36_mod6_block_2 b
  have hb3 := z36_mod6_block_3 b
  have hb4 := z36_mod6_block_4 b
  have hb5 := z36_mod6_block_5 b
  have hmod30raw :
      (b 0 + b 6 + b 12 + b 18 + b 24 + b 30) +
        (b 3 + b 9 + b 15 + b 21 + b 27 + b 33) =
      (b 2 + b 8 + b 14 + b 20 + b 26 + b 32) +
        (b 5 + b 11 + b 17 + b 23 + b 29 + b 35) := by
    rw [z36_count12_0, z36_count12_2, z36_count12_3, z36_count12_5,
      z36_count12_6, z36_count12_8, z36_count12_9, z36_count12_11] at h30
    omega
  have hmod31raw :
      (b 1 + b 7 + b 13 + b 19 + b 25 + b 31) +
        (b 4 + b 10 + b 16 + b 22 + b 28 + b 34) =
      (b 2 + b 8 + b 14 + b 20 + b 26 + b 32) +
        (b 5 + b 11 + b 17 + b 23 + b 29 + b 35) := by
    rw [z36_count12_1, z36_count12_2, z36_count12_4, z36_count12_5,
      z36_count12_7, z36_count12_8, z36_count12_10, z36_count12_11] at h31
    omega
  have hmod30 : z36Mod6Block b 0 + z36Mod6Block b 3 =
      z36Mod6Block b 2 + z36Mod6Block b 5 := by omega
  have hmod31 : z36Mod6Block b 1 + z36Mod6Block b 4 =
      z36Mod6Block b 2 + z36Mod6Block b 5 := by omega
  have hblocksum :
      z36Mod6Block b 0 + z36Mod6Block b 1 + z36Mod6Block b 2 +
        z36Mod6Block b 3 + z36Mod6Block b 4 + z36Mod6Block b 5 = 6 := by
    let c0 := z36Mod6Block b 0
    let c1 := z36Mod6Block b 1
    let c2 := z36Mod6Block b 2
    let c3 := z36Mod6Block b 3
    let c4 := z36Mod6Block b 4
    let c5 := z36Mod6Block b 5
    have hvec :
        (∑ r : Fin 6, ![c0, c1, c2, c3, c4, c5] r) =
          ∑ r : Fin 6, z36Mod6Block b r := by
      apply Fintype.sum_congr
      intro r
      fin_cases r <;> dsimp only <;>
        apply congrArg (z36Mod6Block b) <;> apply Fin.ext <;> norm_num
    have hv := hvec.trans (z36_sum36_blocks_mod6 b hsum)
    norm_num [Fin.sum_univ_succ] at hv
    dsimp only [c0, c1, c2, c3, c4, c5] at hv
    linarith only [hv]
  have hm0 :
      b 0 + b 3 + b 6 + b 9 + b 12 + b 15 +
        b 18 + b 21 + b 24 + b 27 + b 30 + b 33 = 2 := by omega
  have hm1 :
      b 1 + b 4 + b 7 + b 10 + b 13 + b 16 +
        b 19 + b 22 + b 25 + b 28 + b 31 + b 34 = 2 := by omega
  have hm2 :
      b 2 + b 5 + b 8 + b 11 + b 14 + b 17 +
        b 20 + b 23 + b 26 + b 29 + b 32 + b 35 = 2 := by omega
  have k0 := z36_phi3_phi36_fibre_kernel
    (b 0) (b 3) (b 6) (b 9) (b 12) (b 15)
    (b 18) (b 21) (b 24) (b 27) (b 30) (b 33)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    hm0 e0 e3 e6 e9
  have k1 := z36_phi3_phi36_fibre_kernel
    (b 1) (b 4) (b 7) (b 10) (b 13) (b 16)
    (b 19) (b 22) (b 25) (b 28) (b 31) (b 34)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    hm1 e1 e4 e7 e10
  have k2 := z36_phi3_phi36_fibre_kernel
    (b 2) (b 5) (b 8) (b 11) (b 14) (b 17)
    (b 20) (b 23) (b 26) (b 29) (b 32) (b 35)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    (hlo _) (hhi _) (hlo _) (hhi _) (hlo _) (hhi _)
    hm2 e2 e5 e8 e11
  rcases k0 with ⟨a0, a3, a6, a9, a12, a15⟩
  rcases k1 with ⟨a1, a4, a7, a10, a13, a16⟩
  rcases k2 with ⟨a2, a5, a8, a11, a14, a17⟩
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8,
    a9, a10, a11, a12, a13, a14, a15, a16, a17⟩

theorem z36_zero_3_36_forces_4_12
    (A : Finset (ZMod 36)) (hcard : A.card = 6)
    (hthree : Z36ZeroAtOrder A 3)
    (hthirtysix : Z36ZeroAtOrder A 36) :
    Z36ZeroAtOrder A 4 ∧ Z36ZeroAtOrder A 12 := by
  let b := z36MembershipIndicator A
  obtain ⟨hlo, hhi⟩ := z36MembershipIndicator_bounds A
  have hsum : (∑ i : Fin 36, b i) = 6 := by
    simpa [b, hcard] using z36MembershipIndicator_sum A
  have hmask : projection36IndicatorMask b = maskPolynomial 36 A :=
    by simpa [b] using projection36IndicatorMask_z36MembershipIndicator A
  have hanti := z36_phi3_phi36_indicator_antipodal b hlo hhi hsum
    (by simpa [Z36ZeroAtOrder, hmask] using hthree)
    (by simpa [Z36ZeroAtOrder, hmask] using hthirtysix)
  have hdiv := z36_antipodal_forces_phi4_phi12 b hanti
  simpa [Z36ZeroAtOrder, hmask] using hdiv

#print axioms z36_phi3_phi36_indicator_antipodal
#print axioms z36_zero_3_36_forces_4_12

end Fuglede
