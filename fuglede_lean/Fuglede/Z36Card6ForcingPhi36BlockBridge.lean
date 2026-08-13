import Fuglede.Z36Card6ForcingPhi36SumKernel
import Mathlib.Tactic

/-! Six small bridges from structural mod-6 blocks to the familiar coordinates. -/

namespace Fuglede

theorem z36_mod6_block_0 (b : Fin 36 → Int) :
    z36Mod6Block b 0 = b 0 + b 6 + b 12 + b 18 + b 24 + b 30 := by
  unfold z36Mod6Block
  calc
    (∑ q : Fin 6, b (finProdFinEquiv (q, (0 : Fin 6)))) =
        ∑ q : Fin 6, ![b 0, b 6, b 12, b 18, b 24, b 30] q := by
      apply Fintype.sum_congr
      intro q
      fin_cases q <;> apply congrArg b <;> apply Fin.ext <;>
        norm_num [finProdFinEquiv]
    _ = b 0 + b 6 + b 12 + b 18 + b 24 + b 30 := by
      simp [Fin.sum_univ_succ] <;> ring

theorem z36_mod6_block_1 (b : Fin 36 → Int) :
    z36Mod6Block b 1 = b 1 + b 7 + b 13 + b 19 + b 25 + b 31 := by
  unfold z36Mod6Block
  calc
    (∑ q : Fin 6, b (finProdFinEquiv (q, (1 : Fin 6)))) =
        ∑ q : Fin 6, ![b 1, b 7, b 13, b 19, b 25, b 31] q := by
      apply Fintype.sum_congr
      intro q
      fin_cases q <;> apply congrArg b <;> apply Fin.ext <;>
        norm_num [finProdFinEquiv]
    _ = b 1 + b 7 + b 13 + b 19 + b 25 + b 31 := by
      simp [Fin.sum_univ_succ] <;> ring

theorem z36_mod6_block_2 (b : Fin 36 → Int) :
    z36Mod6Block b 2 = b 2 + b 8 + b 14 + b 20 + b 26 + b 32 := by
  unfold z36Mod6Block
  calc
    (∑ q : Fin 6, b (finProdFinEquiv (q, (2 : Fin 6)))) =
        ∑ q : Fin 6, ![b 2, b 8, b 14, b 20, b 26, b 32] q := by
      apply Fintype.sum_congr
      intro q
      fin_cases q <;> apply congrArg b <;> apply Fin.ext <;>
        norm_num [finProdFinEquiv]
    _ = b 2 + b 8 + b 14 + b 20 + b 26 + b 32 := by
      simp [Fin.sum_univ_succ] <;> ring

theorem z36_mod6_block_3 (b : Fin 36 → Int) :
    z36Mod6Block b 3 = b 3 + b 9 + b 15 + b 21 + b 27 + b 33 := by
  unfold z36Mod6Block
  calc
    (∑ q : Fin 6, b (finProdFinEquiv (q, (3 : Fin 6)))) =
        ∑ q : Fin 6, ![b 3, b 9, b 15, b 21, b 27, b 33] q := by
      apply Fintype.sum_congr
      intro q
      fin_cases q <;> apply congrArg b <;> apply Fin.ext <;>
        norm_num [finProdFinEquiv]
    _ = b 3 + b 9 + b 15 + b 21 + b 27 + b 33 := by
      simp [Fin.sum_univ_succ] <;> ring

theorem z36_mod6_block_4 (b : Fin 36 → Int) :
    z36Mod6Block b 4 = b 4 + b 10 + b 16 + b 22 + b 28 + b 34 := by
  unfold z36Mod6Block
  calc
    (∑ q : Fin 6, b (finProdFinEquiv (q, (4 : Fin 6)))) =
        ∑ q : Fin 6, ![b 4, b 10, b 16, b 22, b 28, b 34] q := by
      apply Fintype.sum_congr
      intro q
      fin_cases q <;> apply congrArg b <;> apply Fin.ext <;>
        norm_num [finProdFinEquiv]
    _ = b 4 + b 10 + b 16 + b 22 + b 28 + b 34 := by
      simp [Fin.sum_univ_succ] <;> ring

theorem z36_mod6_block_5 (b : Fin 36 → Int) :
    z36Mod6Block b 5 = b 5 + b 11 + b 17 + b 23 + b 29 + b 35 := by
  unfold z36Mod6Block
  calc
    (∑ q : Fin 6, b (finProdFinEquiv (q, (5 : Fin 6)))) =
        ∑ q : Fin 6, ![b 5, b 11, b 17, b 23, b 29, b 35] q := by
      apply Fintype.sum_congr
      intro q
      fin_cases q <;> apply congrArg b <;> apply Fin.ext <;>
        norm_num [finProdFinEquiv]
    _ = b 5 + b 11 + b 17 + b 23 + b 29 + b 35 := by
      simp [Fin.sum_univ_succ] <;> ring

#print axioms z36_mod6_block_0
#print axioms z36_mod6_block_5

end Fuglede
