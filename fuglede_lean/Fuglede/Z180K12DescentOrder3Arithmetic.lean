import Mathlib.Tactic

/-!
# Compact arithmetic kernel for direct base order three

Four triples of nonnegative counts have mass three.  The two `Phi_3`
remainders are multiples of five.  Their sum is a multiple of three, while
the real polytope cut out by the four mass equations excludes every nonzero
multiple-of-five possibility.  The proof below separates those two facts so
that no large Presburger search is presented to one tactic call.
-/

namespace Fuglede

namespace Z180K12HighOrder

set_option maxHeartbeats 0

/-- Under the cardinality-twelve modulo-four profile, two `Phi_3`
remainders which are multiples of five must both vanish. -/
theorem descent_order3_five_multiples_zero
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 k0 k1 : Int)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5)
    (hc6 : 0 ≤ c6) (hc7 : 0 ≤ c7) (hc8 : 0 ≤ c8)
    (hc9 : 0 ≤ c9) (hc10 : 0 ≤ c10) (hc11 : 0 ≤ c11)
    (hm0 : c0 + c4 + c8 = 3)
    (hm1 : c1 + c5 + c9 = 3)
    (hm2 : c2 + c6 + c10 = 3)
    (hm3 : c3 + c7 + c11 = 3)
    (hr0 : c0 - c2 + c3 - c5 + c6 - c8 + c9 - c11 = 5 * k0)
    (hr1 : c1 - c2 + c4 - c5 + c7 - c8 + c10 - c11 = 5 * k1) :
    c0 - c2 + c3 - c5 + c6 - c8 + c9 - c11 = 0 ∧
      c1 - c2 + c4 - c5 + c7 - c8 + c10 - c11 = 0 := by
  have hk0LowerRaw : -12 ≤ 5 * k0 := by
    linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
      hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr0]
  have hk0UpperRaw : 5 * k0 ≤ 12 := by
    linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
      hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr0]
  have hk1LowerRaw : -12 ≤ 5 * k1 := by
    linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
      hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr1]
  have hk1UpperRaw : 5 * k1 ≤ 12 := by
    linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
      hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr1]
  have hk0Lower : -2 ≤ k0 := by omega
  have hk0Upper : k0 ≤ 2 := by omega
  have hk1Lower : -2 ≤ k1 := by omega
  have hk1Upper : k1 ≤ 2 := by omega
  let q : Int := c0 - c2 + c3 + c4 - c5 + c7 - 2
  have hsumMultiple : 5 * (k0 + k1) = 3 * q := by
    dsimp only [q]
    linear_combination -hr0 - hr1 - 2 * hm0 + hm1 + hm2 - 2 * hm3
  let w : Int := 2 * (k0 + k1) - q
  have hsumThree : k0 + k1 = 3 * w := by
    dsimp only [w]
    linarith only [hsumMultiple]
  have hsumCases : k0 + k1 = -3 ∨ k0 + k1 = 0 ∨ k0 + k1 = 3 := by
    omega
  rcases hsumCases with hneg | hzero | hpos
  · have hpairs : (k0 = -2 ∧ k1 = -1) ∨ (k0 = -1 ∧ k1 = -2) := by
      omega
    rcases hpairs with ⟨hk0, hk1⟩ | ⟨hk0, hk1⟩ <;> exfalso <;>
      linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
        hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr0, hr1, hk0, hk1]
  · have hpairs :
        (k0 = -2 ∧ k1 = 2) ∨ (k0 = -1 ∧ k1 = 1) ∨
          (k0 = 0 ∧ k1 = 0) ∨ (k0 = 1 ∧ k1 = -1) ∨
            (k0 = 2 ∧ k1 = -2) := by
      omega
    rcases hpairs with h | h | ⟨hk0, hk1⟩ | h | h
    · rcases h with ⟨hk0, hk1⟩
      exfalso
      linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
        hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr0, hr1, hk0, hk1]
    · rcases h with ⟨hk0, hk1⟩
      exfalso
      linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
        hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr0, hr1, hk0, hk1]
    · constructor <;> linarith only [hr0, hr1, hk0, hk1]
    · rcases h with ⟨hk0, hk1⟩
      exfalso
      linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
        hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr0, hr1, hk0, hk1]
    · rcases h with ⟨hk0, hk1⟩
      exfalso
      linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
        hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr0, hr1, hk0, hk1]
  · exfalso
    linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8,
      hc9, hc10, hc11, hm0, hm1, hm2, hm3, hr0, hr1, hpos]

#print axioms descent_order3_five_multiples_zero

end Z180K12HighOrder

end Fuglede
