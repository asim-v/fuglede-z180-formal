import Fuglede.Z180K12M6HighOrderRemainders3_12Shard
import Mathlib.Tactic

/-! # Count-twelve adapter shared by the order-fifteen and order-sixty branches -/

namespace Fuglede

namespace Z180K12HighOrder

set_option maxHeartbeats 0

theorem count12_nonneg_high
    (b : Fin 36 → Int) (hlo : ∀ i, 0 ≤ b i) (r : Fin 12) :
    0 ≤ projection36Count12 b r := by
  rw [projection36Count12]
  linarith only [hlo ⟨r.val, by omega⟩,
    hlo ⟨r.val + 12, by omega⟩, hlo ⟨r.val + 24, by omega⟩]

theorem count12_le_three_high
    (b : Fin 36 → Int) (hhi : ∀ i, b i ≤ 1) (r : Fin 12) :
    projection36Count12 b r ≤ 3 := by
  rw [projection36Count12]
  linarith only [hhi ⟨r.val, by omega⟩,
    hhi ⟨r.val + 12, by omega⟩, hhi ⟨r.val + 24, by omega⟩]

theorem count12_mod4_high
    (b : Fin 36 → Int)
    (hmod4 :
      b 0 + b 4 + b 8 + b 12 + b 16 + b 20 + b 24 + b 28 + b 32 = 3 ∧
      b 1 + b 5 + b 9 + b 13 + b 17 + b 21 + b 25 + b 29 + b 33 = 3 ∧
      b 2 + b 6 + b 10 + b 14 + b 18 + b 22 + b 26 + b 30 + b 34 = 3 ∧
      b 3 + b 7 + b 11 + b 15 + b 19 + b 23 + b 27 + b 31 + b 35 = 3) :
    projection36Count12 b 0 + projection36Count12 b 4 +
        projection36Count12 b 8 = 3 ∧
    projection36Count12 b 1 + projection36Count12 b 5 +
        projection36Count12 b 9 = 3 ∧
    projection36Count12 b 2 + projection36Count12 b 6 +
        projection36Count12 b 10 = 3 ∧
    projection36Count12 b 3 + projection36Count12 b 7 +
        projection36Count12 b 11 = 3 := by
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

theorem count12_phi6_high
    (b : Fin 36 → Int) (k0 k1 : Int)
    (h0 : projection36Phi6R0 b = 5 * k0)
    (h1 : projection36Phi6R1 b = 5 * k1) :
    projection36Count12 b 0 - projection36Count12 b 2 -
        projection36Count12 b 3 + projection36Count12 b 5 +
        projection36Count12 b 6 - projection36Count12 b 8 -
        projection36Count12 b 9 + projection36Count12 b 11 = 5 * k0 ∧
    projection36Count12 b 1 + projection36Count12 b 2 -
        projection36Count12 b 4 - projection36Count12 b 5 +
        projection36Count12 b 7 + projection36Count12 b 8 -
        projection36Count12 b 10 - projection36Count12 b 11 = 5 * k1 := by
  constructor
  · dsimp only [projection36Count12]
    change (b 0 + b 12 + b 24) - (b 2 + b 14 + b 26) -
        (b 3 + b 15 + b 27) + (b 5 + b 17 + b 29) +
        (b 6 + b 18 + b 30) - (b 8 + b 20 + b 32) -
        (b 9 + b 21 + b 33) + (b 11 + b 23 + b 35) = 5 * k0
    dsimp only [projection36Phi6R0] at h0
    linear_combination h0
  · dsimp only [projection36Count12]
    change (b 1 + b 13 + b 25) + (b 2 + b 14 + b 26) -
        (b 4 + b 16 + b 28) - (b 5 + b 17 + b 29) +
        (b 7 + b 19 + b 31) + (b 8 + b 20 + b 32) -
        (b 10 + b 22 + b 34) - (b 11 + b 23 + b 35) = 5 * k1
    dsimp only [projection36Phi6R1] at h1
    linear_combination h1

#print axioms count12_nonneg_high
#print axioms count12_le_three_high
#print axioms count12_mod4_high
#print axioms count12_phi6_high

end Z180K12HighOrder

end Fuglede
