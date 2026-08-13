import Fuglede.ProjectionFiberTiling
import Mathlib.Tactic

/-!
# The three-primary fibres used at cardinality twelve in `ZMod 36`

Projection to `ZMod 4` has a kernel of order nine.  Every nonzero difference
inside one fibre therefore has exact order three or nine.  The two explicit
three-point kernel patterns below have the two opposite difference orders.
-/

namespace Fuglede

/-- A nonzero element in the kernel of `ZMod 36 → ZMod 4` has order three
or nine. -/
theorem z36_frequencyOrder_three_or_nine_of_cast4_eq :
    ∀ x y : ZMod 36,
      x ≠ y →
      (ZMod.cast x : ZMod 4) = ZMod.cast y →
      frequencyOrder 36 (x - y) = 3 ∨
        frequencyOrder 36 (x - y) = 9 := by
  intro x y hxy hcast
  have hcastZero : (ZMod.cast (x - y) : ZMod 4) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 4 ∣ 36), hcast, sub_self]
  have hnatCastZero : ((x - y).val : ZMod 4) = 0 := by
    simpa only [ZMod.cast_eq_val] using hcastZero
  have hdvd : 4 ∣ (x - y).val :=
    (ZMod.natCast_eq_zero_iff (x - y).val 4).1 hnatCastZero
  obtain ⟨k, hk⟩ := hdvd
  have hvalne : (x - y).val ≠ 0 := by
    intro hzero
    have hdiff : x - y = 0 := (ZMod.val_eq_zero (x - y)).1 hzero
    exact hxy (sub_eq_zero.mp hdiff)
  have hkpos : 0 < k := by omega
  have hklt : k < 9 := by
    have hvalLt := (x - y).val_lt
    omega
  unfold frequencyOrder
  rw [hk]
  interval_cases k <;> norm_num at hkpos ⊢

/-- Three kernel points whose nonzero differences have order nine. -/
def z36OrderNineComplement : Finset (ZMod 36) := {0, 4, 8}

/-- The order-three subgroup of `ZMod 36`. -/
def z36OrderThreeComplement : Finset (ZMod 36) := {0, 12, 24}

@[simp]
theorem z36OrderNineComplement_card : z36OrderNineComplement.card = 3 := by
  decide

@[simp]
theorem z36OrderThreeComplement_card : z36OrderThreeComplement.card = 3 := by
  decide

theorem z36OrderNineComplement_cast4_zero
    {b : ZMod 36} (hb : b ∈ z36OrderNineComplement) :
    (ZMod.cast b : ZMod 4) = 0 := by
  simp only [z36OrderNineComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;> decide

theorem z36OrderThreeComplement_cast4_zero
    {b : ZMod 36} (hb : b ∈ z36OrderThreeComplement) :
    (ZMod.cast b : ZMod 4) = 0 := by
  simp only [z36OrderThreeComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;> decide

theorem z36OrderNineComplement_difference_order
    {b b' : ZMod 36}
    (hb : b ∈ z36OrderNineComplement)
    (hb' : b' ∈ z36OrderNineComplement) (hne : b ≠ b') :
    frequencyOrder 36 (b - b') = 9 := by
  simp only [z36OrderNineComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb hb'
  rcases hb with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl
  all_goals first | exact (hne rfl).elim | decide

theorem z36OrderThreeComplement_difference_order
    {b b' : ZMod 36}
    (hb : b ∈ z36OrderThreeComplement)
    (hb' : b' ∈ z36OrderThreeComplement) (hne : b ≠ b') :
    frequencyOrder 36 (b - b') = 3 := by
  simp only [z36OrderThreeComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb hb'
  rcases hb with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl
  all_goals first | exact (hne rfl).elim | decide

#print axioms z36_frequencyOrder_three_or_nine_of_cast4_eq
#print axioms z36OrderNineComplement_difference_order
#print axioms z36OrderThreeComplement_difference_order

end Fuglede
