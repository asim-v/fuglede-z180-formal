import Fuglede.ExactOrderDistributionParity
import Fuglede.Z180K30FibreFourier
import Mathlib.Tactic

/-!
# Semantic input for the `k = 30` joint arithmetic certificate

This module isolates the finite-group facts needed before invoking the
generated QF_LIA proof.  A nontrivial difference inside one fifth-coordinate
slice has order among the eight nontrivial divisors of `36`, and the
corresponding exact-order distribution is strictly positive.

No arithmetic certificate is asserted here.
-/

namespace Fuglede

/-- An explicitly occurring ordered pair contributes positive exact-order
mass at the order of its difference. -/
theorem exactOrderDistributionInt_pos_of_mem_pair
    {N : Nat} [NeZero N] {X : Finset (ZMod N)}
    {x y : ZMod N} (hx : x ∈ X) (hy : y ∈ X) :
    0 < exactOrderDistributionInt X (frequencyOrder N (x - y)) := by
  classical
  rw [exactOrderDistributionInt, exactOrderDistribution, exactOrderPairs]
  have hpos :
      0 < ((X ×ˢ X).filter fun p ↦
        frequencyOrder N (p.1 - p.2) = frequencyOrder N (x - y)).card :=
    Finset.card_pos.mpr
      ⟨(x, y), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩
  exact_mod_cast hpos

/-- A difference inside a fixed fifth-coordinate slice has order dividing
the complementary factor `36`. -/
theorem z180_k30_frequencyOrder_diff_dvd_36_of_mem_fifth_slice
    {L : Finset (ZMod 180)} {c : ZMod 5} {y₁ y₂ : ZMod 180}
    (hy₁ : y₁ ∈ z180K30FifthSlice L c)
    (hy₂ : y₂ ∈ z180K30FifthSlice L c) :
    frequencyOrder 180 (y₁ - y₂) ∣ 36 := by
  have hy₁five : (ZMod.cast y₁ : ZMod 5) = c :=
    (Finset.mem_filter.mp hy₁).2
  have hy₂five : (ZMod.cast y₂ : ZMod 5) = c :=
    (Finset.mem_filter.mp hy₂).2
  have hfive : (ZMod.cast (y₁ - y₂) : ZMod 5) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 5 ∣ 180), hy₁five, hy₂five, sub_self]
  rw [z180_frequencyOrder_eq_projection36_of_fifthCoordinate_zero
    (y₁ - y₂) hfive]
  exact frequencyOrder_dvd_modulus _

/-- A nonzero difference never has exact order one. -/
theorem z180_k30_frequencyOrder_diff_ne_one
    {y₁ y₂ : ZMod 180} (hne : y₁ ≠ y₂) :
    frequencyOrder 180 (y₁ - y₂) ≠ 1 := by
  intro hone
  apply hne
  exact sub_eq_zero.mp
    ((frequencyOrder_eq_one_iff (by norm_num) (y₁ - y₂)).mp hone)

/-- Exhaustive arithmetic classification of the nontrivial divisors of
`36`.  This is intentionally a small trusted-kernel computation rather than
an assumption supplied to the generated certificate. -/
theorem eq_one_or_eight_nontrivial_divisors_of_36
    {m : Nat} (hm : m ∣ 36) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 9 ∨
      m = 12 ∨ m = 18 ∨ m = 36 := by
  have hmle : m ≤ 36 := Nat.le_of_dvd (by norm_num) hm
  interval_cases m <;> norm_num at hm <;> simp

/-- The exact order of a nontrivial same-fifth-slice difference is one of
eight cases that any complete closure argument must analyze.  The current
exact-order relaxation closes only orders `9` and `36`. -/
theorem z180_k30_frequencyOrder_diff_eight_cases
    {L : Finset (ZMod 180)} {c : ZMod 5} {y₁ y₂ : ZMod 180}
    (hy₁ : y₁ ∈ z180K30FifthSlice L c)
    (hy₂ : y₂ ∈ z180K30FifthSlice L c) (hne : y₁ ≠ y₂) :
    let m := frequencyOrder 180 (y₁ - y₂)
    m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 9 ∨
      m = 12 ∨ m = 18 ∨ m = 36 := by
  dsimp only
  have hdvd :=
    z180_k30_frequencyOrder_diff_dvd_36_of_mem_fifth_slice hy₁ hy₂
  have hneone := z180_k30_frequencyOrder_diff_ne_one hne
  rcases eq_one_or_eight_nontrivial_divisors_of_36 hdvd with h | h
  · exact (hneone h).elim
  · exact h

/-- The semantic premises carried by a nontrivial pair in the zeroth fifth
slice: positive mass at its order and the exhaustive eight-way order split. -/
theorem z180_k30_zeroth_fifth_slice_pair_semantic_input
    {L : Finset (ZMod 180)} {y₁ y₂ : ZMod 180}
    (hy₁ : y₁ ∈ z180K30FifthSlice L (0 : ZMod 5))
    (hy₂ : y₂ ∈ z180K30FifthSlice L (0 : ZMod 5)) (hne : y₁ ≠ y₂) :
    let m := frequencyOrder 180 (y₁ - y₂)
    0 < exactOrderDistributionInt L m ∧
      (m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 9 ∨
        m = 12 ∨ m = 18 ∨ m = 36) := by
  dsimp only
  refine ⟨?_, z180_k30_frequencyOrder_diff_eight_cases hy₁ hy₂ hne⟩
  exact exactOrderDistributionInt_pos_of_mem_pair
    (Finset.mem_filter.mp hy₁).1 (Finset.mem_filter.mp hy₂).1

#print axioms exactOrderDistributionInt_pos_of_mem_pair
#print axioms z180_k30_frequencyOrder_diff_dvd_36_of_mem_fifth_slice
#print axioms eq_one_or_eight_nontrivial_divisors_of_36
#print axioms z180_k30_zeroth_fifth_slice_pair_semantic_input

end Fuglede
