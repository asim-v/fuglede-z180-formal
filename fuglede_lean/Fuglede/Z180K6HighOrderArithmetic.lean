import Fuglede.Z180K6LowOrderArithmetic
import Mathlib.Tactic

/-!
# Arithmetic exclusions for the high-order cardinality-six branch

These are the three small Presburger certificates left by the exact
`(4,1,1)` residue pattern.  Orders twelve and eighteen need no coordinate
bounds.  Order thirty-six genuinely uses that every projected occupancy is
a zero-one variable.
-/

namespace Fuglede

set_option maxHeartbeats 0

/-- The four `Phi_12` remainder equations are incompatible with every
rotation of the cardinality-six residue pattern. -/
theorem z180_k6_phi12_count12_remainders_impossible
    (b : Fin 36 → Int)
    (hpattern : Z180K6ResidueSixPattern b)
    (h0 : (b 0 + b 12 + b 24) - (b 4 + b 16 + b 28) -
      (b 6 + b 18 + b 30) + (b 10 + b 22 + b 34) = 0)
    (h1 : (b 1 + b 13 + b 25) - (b 5 + b 17 + b 29) -
      (b 7 + b 19 + b 31) + (b 11 + b 23 + b 35) = 0)
    (h2 : (b 2 + b 14 + b 26) + (b 4 + b 16 + b 28) -
      (b 8 + b 20 + b 32) - (b 10 + b 22 + b 34) = 0)
    (h3 : (b 3 + b 15 + b 27) + (b 5 + b 17 + b 29) -
      (b 9 + b 21 + b 33) - (b 11 + b 23 + b 35) = 0) :
    False := by
  dsimp only [Z180K6ResidueSixPattern] at hpattern
  rcases hpattern with h | h | h | h | h | h <;>
    rcases h with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ <;>
    omega

/-- The six `Phi_18` remainder equations are incompatible with every
rotation of the cardinality-six residue pattern. -/
theorem z180_k6_phi18_remainders_impossible
    (b : Fin 36 → Int)
    (hpattern : Z180K6ResidueSixPattern b)
    (h0 : b 0 - b 6 - b 9 + b 15 + b 18 - b 24 - b 27 + b 33 = 0)
    (h1 : b 1 - b 7 - b 10 + b 16 + b 19 - b 25 - b 28 + b 34 = 0)
    (h2 : b 2 - b 8 - b 11 + b 17 + b 20 - b 26 - b 29 + b 35 = 0)
    (h3 : b 3 + b 6 - b 12 - b 15 + b 21 + b 24 - b 30 - b 33 = 0)
    (h4 : b 4 + b 7 - b 13 - b 16 + b 22 + b 25 - b 31 - b 34 = 0)
    (h5 : b 5 + b 8 - b 14 - b 17 + b 23 + b 26 - b 32 - b 35 = 0) :
    False := by
  dsimp only [Z180K6ResidueSixPattern] at hpattern
  rcases hpattern with h | h | h | h | h | h <;>
    rcases h with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ <;>
    omega

/-- The twelve `Phi_36` remainder equations are incompatible with the
cardinality-six residue pattern once all coordinates are zero-one. -/
private theorem phi36_zero_one_block_sum_ne_one
    (a0 a1 a2 a3 a4 a5 : Int)
    (hz0 : 0 ≤ a0) (hz1 : 0 ≤ a1) (hz2 : 0 ≤ a2)
    (hz3 : 0 ≤ a3) (hz4 : 0 ≤ a4) (hz5 : 0 ≤ a5)
    (ho0 : a0 ≤ 1) (ho1 : a1 ≤ 1) (ho2 : a2 ≤ 1)
    (ho3 : a3 ≤ 1) (ho4 : a4 ≤ 1) (ho5 : a5 ≤ 1)
    (he0 : a0 - a2 - a3 + a5 = 0)
    (he1 : a1 + a2 - a4 - a5 = 0) :
    a0 + a1 + a2 + a3 + a4 + a5 ≠ 1 := by
  interval_cases a0 <;> interval_cases a1 <;> interval_cases a2 <;>
    interval_cases a3 <;> interval_cases a4 <;> interval_cases a5 <;>
    omega

theorem z180_k6_phi36_remainders_impossible
    (b : Fin 36 → Int)
    (hpattern : Z180K6ResidueSixPattern b)
    (hzero : ∀ i, 0 ≤ b i) (hone : ∀ i, b i ≤ 1)
    (h0 : b 0 - b 12 - b 18 + b 30 = 0)
    (h1 : b 1 - b 13 - b 19 + b 31 = 0)
    (h2 : b 2 - b 14 - b 20 + b 32 = 0)
    (h3 : b 3 - b 15 - b 21 + b 33 = 0)
    (h4 : b 4 - b 16 - b 22 + b 34 = 0)
    (h5 : b 5 - b 17 - b 23 + b 35 = 0)
    (h6 : b 6 + b 12 - b 24 - b 30 = 0)
    (h7 : b 7 + b 13 - b 25 - b 31 = 0)
    (h8 : b 8 + b 14 - b 26 - b 32 = 0)
    (h9 : b 9 + b 15 - b 27 - b 33 = 0)
    (h10 : b 10 + b 16 - b 28 - b 34 = 0)
    (h11 : b 11 + b 17 - b 29 - b 35 = 0) :
    False := by
  have hz0 := hzero 0; have hz1 := hzero 1; have hz2 := hzero 2
  have hz3 := hzero 3; have hz4 := hzero 4; have hz5 := hzero 5
  have hz6 := hzero 6; have hz7 := hzero 7; have hz8 := hzero 8
  have hz9 := hzero 9; have hz10 := hzero 10; have hz11 := hzero 11
  have hz12 := hzero 12; have hz13 := hzero 13; have hz14 := hzero 14
  have hz15 := hzero 15; have hz16 := hzero 16; have hz17 := hzero 17
  have hz18 := hzero 18; have hz19 := hzero 19; have hz20 := hzero 20
  have hz21 := hzero 21; have hz22 := hzero 22; have hz23 := hzero 23
  have hz24 := hzero 24; have hz25 := hzero 25; have hz26 := hzero 26
  have hz27 := hzero 27; have hz28 := hzero 28; have hz29 := hzero 29
  have hz30 := hzero 30; have hz31 := hzero 31; have hz32 := hzero 32
  have hz33 := hzero 33; have hz34 := hzero 34; have hz35 := hzero 35
  have ho0 := hone 0; have ho1 := hone 1; have ho2 := hone 2
  have ho3 := hone 3; have ho4 := hone 4; have ho5 := hone 5
  have ho6 := hone 6; have ho7 := hone 7; have ho8 := hone 8
  have ho9 := hone 9; have ho10 := hone 10; have ho11 := hone 11
  have ho12 := hone 12; have ho13 := hone 13; have ho14 := hone 14
  have ho15 := hone 15; have ho16 := hone 16; have ho17 := hone 17
  have ho18 := hone 18; have ho19 := hone 19; have ho20 := hone 20
  have ho21 := hone 21; have ho22 := hone 22; have ho23 := hone 23
  have ho24 := hone 24; have ho25 := hone 25; have ho26 := hone 26
  have ho27 := hone 27; have ho28 := hone 28; have ho29 := hone 29
  have ho30 := hone 30; have ho31 := hone 31; have ho32 := hone 32
  have ho33 := hone 33; have ho34 := hone 34; have ho35 := hone 35
  have hn0 : b 0 + b 6 + b 12 + b 18 + b 24 + b 30 ≠ 1 :=
    phi36_zero_one_block_sum_ne_one
      (b 0) (b 6) (b 12) (b 18) (b 24) (b 30)
      hz0 hz6 hz12 hz18 hz24 hz30 ho0 ho6 ho12 ho18 ho24 ho30 h0 h6
  have hn1 : b 1 + b 7 + b 13 + b 19 + b 25 + b 31 ≠ 1 :=
    phi36_zero_one_block_sum_ne_one
      (b 1) (b 7) (b 13) (b 19) (b 25) (b 31)
      hz1 hz7 hz13 hz19 hz25 hz31 ho1 ho7 ho13 ho19 ho25 ho31 h1 h7
  have hn2 : b 2 + b 8 + b 14 + b 20 + b 26 + b 32 ≠ 1 :=
    phi36_zero_one_block_sum_ne_one
      (b 2) (b 8) (b 14) (b 20) (b 26) (b 32)
      hz2 hz8 hz14 hz20 hz26 hz32 ho2 ho8 ho14 ho20 ho26 ho32 h2 h8
  have hn3 : b 3 + b 9 + b 15 + b 21 + b 27 + b 33 ≠ 1 :=
    phi36_zero_one_block_sum_ne_one
      (b 3) (b 9) (b 15) (b 21) (b 27) (b 33)
      hz3 hz9 hz15 hz21 hz27 hz33 ho3 ho9 ho15 ho21 ho27 ho33 h3 h9
  have hn4 : b 4 + b 10 + b 16 + b 22 + b 28 + b 34 ≠ 1 :=
    phi36_zero_one_block_sum_ne_one
      (b 4) (b 10) (b 16) (b 22) (b 28) (b 34)
      hz4 hz10 hz16 hz22 hz28 hz34 ho4 ho10 ho16 ho22 ho28 ho34 h4 h10
  have hn5 : b 5 + b 11 + b 17 + b 23 + b 29 + b 35 ≠ 1 :=
    phi36_zero_one_block_sum_ne_one
      (b 5) (b 11) (b 17) (b 23) (b 29) (b 35)
      hz5 hz11 hz17 hz23 hz29 hz35 ho5 ho11 ho17 ho23 ho29 ho35 h5 h11
  dsimp only [Z180K6ResidueSixPattern] at hpattern
  rcases hpattern with h | h | h | h | h | h <;>
    rcases h with ⟨hr0, hr1, hr2, hr3, hr4, hr5⟩ <;>
    omega

#print axioms z180_k6_phi12_count12_remainders_impossible
#print axioms z180_k6_phi18_remainders_impossible
#print axioms z180_k6_phi36_remainders_impossible

end Fuglede
