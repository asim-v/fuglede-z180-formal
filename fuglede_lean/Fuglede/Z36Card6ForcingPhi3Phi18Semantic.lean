import Fuglede.Z36Card6ForcingIndicator
import Fuglede.Z36Card6TilingCovers
import Fuglede.Z36Card6ForcingPhi3Phi18Kernel
import Fuglede.Z36Card6ForcingPhi3Phi18Factor
import Fuglede.Z36Card6ForcingPhi3Phi18Count12Bridge
import Fuglede.Z180K12Projection36Remainders3_12
import Fuglede.Z180K12Projection36Remainders18
import Mathlib.Tactic

/-! Semantic assembly of the cardinality-six `Phi_3` plus `Phi_18` branch. -/

namespace Fuglede

open Polynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem z36_phi3_phi18_indicator_mod6_profile
    (b : Fin 36 → Int)
    (hlo : ∀ i, 0 ≤ b i) (hhi : ∀ i, b i ≤ 1)
    (hsum : (∑ i : Fin 36, b i) = 6)
    (hthree : cyclotomic 3 Int ∣ projection36IndicatorMask b)
    (heighteen : cyclotomic 18 Int ∣ projection36IndicatorMask b) :
    z36Mod6Block b 0 = 1 ∧ z36Mod6Block b 1 = 1 ∧
      z36Mod6Block b 2 = 1 ∧ z36Mod6Block b 3 = 1 ∧
      z36Mod6Block b 4 = 1 ∧ z36Mod6Block b 5 = 1 := by
  obtain ⟨h30, h31⟩ := projection36_phi3_count12_remainders b
    (by simpa [projection36IndicatorMask] using hthree)
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := projection36_phi18_remainders b
    (by simpa [projection36IndicatorMask] using heighteen)
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
      (b 0 + b 18) + (b 3 + b 21) + (b 6 + b 24) +
        (b 9 + b 27) + (b 12 + b 30) + (b 15 + b 33) = 2 := by
    omega
  have hm1 :
      (b 1 + b 19) + (b 4 + b 22) + (b 7 + b 25) +
        (b 10 + b 28) + (b 13 + b 31) + (b 16 + b 34) = 2 := by
    omega
  have hm2 :
      (b 2 + b 20) + (b 5 + b 23) + (b 8 + b 26) +
        (b 11 + b 29) + (b 14 + b 32) + (b 17 + b 35) = 2 := by
    omega
  have pairlo (i j : Fin 36) : 0 ≤ b i + b j := by
    have hi := hlo i
    have hj := hlo j
    omega
  have pairhi (i j : Fin 36) : b i + b j ≤ 2 := by
    have hi := hhi i
    have hj := hhi j
    omega
  have k0 := z36_phi3_phi18_fibre_kernel
    (b 0 + b 18) (b 3 + b 21) (b 6 + b 24)
    (b 9 + b 27) (b 12 + b 30) (b 15 + b 33)
    (pairlo _ _) (pairhi _ _) (pairlo _ _) (pairhi _ _)
    (pairlo _ _) (pairhi _ _) (pairlo _ _) (pairhi _ _)
    (pairlo _ _) (pairhi _ _) (pairlo _ _) (pairhi _ _)
    hm0 (by omega) (by omega)
  have k1 := z36_phi3_phi18_fibre_kernel
    (b 1 + b 19) (b 4 + b 22) (b 7 + b 25)
    (b 10 + b 28) (b 13 + b 31) (b 16 + b 34)
    (pairlo _ _) (pairhi _ _) (pairlo _ _) (pairhi _ _)
    (pairlo _ _) (pairhi _ _) (pairlo _ _) (pairhi _ _)
    (pairlo _ _) (pairhi _ _) (pairlo _ _) (pairhi _ _)
    hm1 (by omega) (by omega)
  have k2 := z36_phi3_phi18_fibre_kernel
    (b 2 + b 20) (b 5 + b 23) (b 8 + b 26)
    (b 11 + b 29) (b 14 + b 32) (b 17 + b 35)
    (pairlo _ _) (pairhi _ _) (pairlo _ _) (pairhi _ _)
    (pairlo _ _) (pairhi _ _) (pairlo _ _) (pairhi _ _)
    (pairlo _ _) (pairhi _ _) (pairlo _ _) (pairhi _ _)
    hm2 (by omega) (by omega)
  have out0 : z36Mod6Block b 0 = 1 := by
    rw [z36_mod6_block_0]
    omega
  have out1 : z36Mod6Block b 1 = 1 := by
    rw [z36_mod6_block_1]
    omega
  have out2 : z36Mod6Block b 2 = 1 := by
    rw [z36_mod6_block_2]
    omega
  have out3 : z36Mod6Block b 3 = 1 := by
    rw [z36_mod6_block_3]
    omega
  have out4 : z36Mod6Block b 4 = 1 := by
    rw [z36_mod6_block_4]
    omega
  have out5 : z36Mod6Block b 5 = 1 := by
    rw [z36_mod6_block_5]
    omega
  exact ⟨out0, out1, out2, out3, out4, out5⟩

theorem z36_zero_3_18_forces_2_6
    (A : Finset (ZMod 36)) (hcard : A.card = 6)
    (hthree : Z36ZeroAtOrder A 3)
    (heighteen : Z36ZeroAtOrder A 18) :
    Z36ZeroAtOrder A 2 ∧ Z36ZeroAtOrder A 6 := by
  let b := z36MembershipIndicator A
  obtain ⟨hlo, hhi⟩ := z36MembershipIndicator_bounds A
  have hsum : (∑ i : Fin 36, b i) = 6 := by
    simpa [b, hcard] using z36MembershipIndicator_sum A
  have hmask : projection36IndicatorMask b = maskPolynomial 36 A :=
    by simpa [b] using projection36IndicatorMask_z36MembershipIndicator A
  obtain ⟨out0, out1, out2, out3, out4, out5⟩ :=
    z36_phi3_phi18_indicator_mod6_profile b hlo hhi hsum
    (by simpa [Z36ZeroAtOrder, hmask] using hthree)
    (by simpa [Z36ZeroAtOrder, hmask] using heighteen)
  have hdiv := z36_mod6_blocks_one_forces_phi2_phi6 b
    out0 out1 out2 out3 out4 out5
  simpa [Z36ZeroAtOrder, hmask] using hdiv

#print axioms z36_phi3_phi18_indicator_mod6_profile
#print axioms z36_zero_3_18_forces_2_6

end Fuglede
