import Fuglede.Z180K10Projection20Pairs
import Mathlib.Tactic

/-!
# Mixed fifth-fibre pairs force every nontrivial divisor order of twenty

The only finite checks in this file are fixed local facts about one element
of `ZMod 20` and the four-element group `ZMod 4`.  In particular, no family
of cardinality-ten subsets is enumerated.
-/

namespace Fuglede

/-- The modulo-four coordinate on `ZMod 20`. -/
def z20K10FourthCoordinate (x : ZMod 20) : ZMod 4 :=
  ZMod.cast x

@[simp]
theorem z20K10FifthCoordinate_sub (x y : ZMod 20) :
    z20K10FifthCoordinate (x - y) =
      z20K10FifthCoordinate x - z20K10FifthCoordinate y := by
  exact ZMod.cast_sub (by norm_num : 5 ∣ 20) x y

@[simp]
theorem z20K10FourthCoordinate_sub (x y : ZMod 20) :
    z20K10FourthCoordinate (x - y) =
      z20K10FourthCoordinate x - z20K10FourthCoordinate y := by
  exact ZMod.cast_sub (by norm_num : 4 ∣ 20) x y

/-- Local CRT shadow of an order-two element. -/
theorem z20_fourthCoordinate_eq_two_of_frequencyOrder_two
    (d : ZMod 20) (horder : frequencyOrder 20 d = 2) :
    z20K10FourthCoordinate d = 2 := by
  revert d
  decide

/-- Local CRT shadow of an order-four element. -/
theorem z20_fourthCoordinate_eq_one_or_three_of_frequencyOrder_four
    (d : ZMod 20) (horder : frequencyOrder 20 d = 4) :
    z20K10FourthCoordinate d = 1 ∨
      z20K10FourthCoordinate d = 3 := by
  revert d
  decide

/-- A nonzero fifth coordinate and zero fourth coordinate characterize the
order-five cross difference used below. -/
theorem z20_frequencyOrder_five_of_fifth_ne_zero_of_fourth_eq_zero
    (d : ZMod 20) (hfive : z20K10FifthCoordinate d ≠ 0)
    (hfour : z20K10FourthCoordinate d = 0) :
    frequencyOrder 20 d = 5 := by
  revert d
  decide

/-- A nonzero fifth coordinate and fourth coordinate two give order ten. -/
theorem z20_frequencyOrder_ten_of_fifth_ne_zero_of_fourth_eq_two
    (d : ZMod 20) (hfive : z20K10FifthCoordinate d ≠ 0)
    (hfour : z20K10FourthCoordinate d = 2) :
    frequencyOrder 20 d = 10 := by
  revert d
  decide

/-- A nonzero fifth coordinate and odd fourth coordinate give order twenty. -/
theorem z20_frequencyOrder_twenty_of_fifth_ne_zero_of_fourth_odd
    (d : ZMod 20) (hfive : z20K10FifthCoordinate d ≠ 0)
    (hfour : z20K10FourthCoordinate d = 1 ∨
      z20K10FourthCoordinate d = 3) :
    frequencyOrder 20 d = 20 := by
  revert d
  decide

/-- An antipodal pair and an adjacent pair in `ZMod 4` have cross
differences covering all four residues.  This is the fixed four-point core
of the mixed-pair argument. -/
theorem zmod4_mixed_pairs_cross_differences_cover
    (x y u v r : ZMod 4)
    (hxy : x - y = 2)
    (huv : u - v = 1 ∨ u - v = 3) :
    x - u = r ∨ x - v = r ∨
      y - u = r ∨ y - v = r := by
  revert x y u v r
  decide

/-- In a balanced fifth fibre, any two nontrivial ordered pairs have the
same exact order (possibly after reversing orientation). -/
theorem z20_frequencyOrder_eq_of_pairs_in_same_balanced_fifth
    {S : Finset (ZMod 20)} (hbalanced : Z20K10BalancedFifths S)
    {x y u v : ZMod 20}
    (hx : x ∈ S) (hy : y ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hxy : x ≠ y) (huv : u ≠ v)
    (hxyFive : z20K10FifthCoordinate x = z20K10FifthCoordinate y)
    (huvFive : z20K10FifthCoordinate u = z20K10FifthCoordinate v)
    (hxuFive : z20K10FifthCoordinate x = z20K10FifthCoordinate u) :
    frequencyOrder 20 (x - y) = frequencyOrder 20 (u - v) := by
  classical
  let c := z20K10FifthCoordinate x
  let F := S.filter fun z => z20K10FifthCoordinate z = c
  have hFcard : F.card = 2 := by
    simpa [F, c, z20K10FifthOccupancy] using hbalanced c
  have hxySubset : ({x, y} : Finset (ZMod 20)) ⊆ F := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hx, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hy, hxyFive.symm⟩
  have hxyCard : ({x, y} : Finset (ZMod 20)).card = 2 := by
    simp [hxy]
  have hxyEq : ({x, y} : Finset (ZMod 20)) = F :=
    Finset.eq_of_subset_of_card_le hxySubset (by omega)
  have huF : u ∈ F := by
    apply Finset.mem_filter.mpr
    exact ⟨hu, hxuFive.symm⟩
  have hvF : v ∈ F := by
    apply Finset.mem_filter.mpr
    exact ⟨hv, huvFive.symm.trans hxuFive.symm⟩
  rw [← hxyEq] at huF hvF
  simp only [Finset.mem_insert, Finset.mem_singleton] at huF hvF
  have hsym :
      frequencyOrder 20 (x - y) = frequencyOrder 20 (y - x) :=
    frequencyOrder_sub_comm (by norm_num) x y
  rcases huF with rfl | rfl <;> rcases hvF with rfl | rfl
  · exact False.elim (huv rfl)
  · rfl
  · exact hsym
  · exact False.elim (huv rfl)

/-- A balanced set with both possible same-fibre pair types has the five
nontrivial exact orders dividing twenty among its differences. -/
theorem z20_k10_mixed_fifth_pairs_force_all_orders
    {S : Finset (ZMod 20)} (hbalanced : Z20K10BalancedFifths S)
    (htwo : Z20K10HasFifthPairOrder S 2)
    (hfour : Z20K10HasFifthPairOrder S 4) :
    Z20K10HasDifferenceOrder S 2 ∧
      Z20K10HasDifferenceOrder S 4 ∧
      Z20K10HasDifferenceOrder S 5 ∧
      Z20K10HasDifferenceOrder S 10 ∧
      Z20K10HasDifferenceOrder S 20 := by
  rcases htwo with ⟨x, hx, y, hy, hxy, hxyFive, hxyOrder⟩
  rcases hfour with ⟨u, hu, v, hv, huv, huvFive, huvOrder⟩
  have hxuCoordinate :
      z20K10FifthCoordinate x ≠ z20K10FifthCoordinate u := by
    intro hxu
    have horders := z20_frequencyOrder_eq_of_pairs_in_same_balanced_fifth
      hbalanced hx hy hu hv hxy huv hxyFive huvFive hxu
    rw [hxyOrder, huvOrder] at horders
    omega
  have hxyFourth :
      z20K10FourthCoordinate x - z20K10FourthCoordinate y = 2 := by
    simpa using z20_fourthCoordinate_eq_two_of_frequencyOrder_two
      (x - y) hxyOrder
  have huvFourth :
      z20K10FourthCoordinate u - z20K10FourthCoordinate v = 1 ∨
        z20K10FourthCoordinate u - z20K10FourthCoordinate v = 3 := by
    simpa using
      z20_fourthCoordinate_eq_one_or_three_of_frequencyOrder_four
        (u - v) huvOrder
  have hxuFifth : z20K10FifthCoordinate (x - u) ≠ 0 := by
    rw [z20K10FifthCoordinate_sub]
    exact sub_ne_zero.mpr hxuCoordinate
  have hxvCoordinate :
      z20K10FifthCoordinate x ≠ z20K10FifthCoordinate v := by
    intro h
    exact hxuCoordinate (h.trans huvFive.symm)
  have hxvFifth : z20K10FifthCoordinate (x - v) ≠ 0 := by
    rw [z20K10FifthCoordinate_sub]
    exact sub_ne_zero.mpr hxvCoordinate
  have hyuCoordinate :
      z20K10FifthCoordinate y ≠ z20K10FifthCoordinate u := by
    intro h
    exact hxuCoordinate (hxyFive.trans h)
  have hyuFifth : z20K10FifthCoordinate (y - u) ≠ 0 := by
    rw [z20K10FifthCoordinate_sub]
    exact sub_ne_zero.mpr hyuCoordinate
  have hyvCoordinate :
      z20K10FifthCoordinate y ≠ z20K10FifthCoordinate v := by
    intro h
    exact hxuCoordinate (hxyFive.trans (h.trans huvFive.symm))
  have hyvFifth : z20K10FifthCoordinate (y - v) ≠ 0 := by
    rw [z20K10FifthCoordinate_sub]
    exact sub_ne_zero.mpr hyvCoordinate
  have hxu : x ≠ u := fun h => hxuCoordinate (congrArg _ h)
  have hxv : x ≠ v := fun h => hxvCoordinate (congrArg _ h)
  have hyu : y ≠ u := fun h => hyuCoordinate (congrArg _ h)
  have hyv : y ≠ v := fun h => hyvCoordinate (congrArg _ h)
  have hcover (r : ZMod 4) :
      z20K10FourthCoordinate x - z20K10FourthCoordinate u = r ∨
        z20K10FourthCoordinate x - z20K10FourthCoordinate v = r ∨
        z20K10FourthCoordinate y - z20K10FourthCoordinate u = r ∨
        z20K10FourthCoordinate y - z20K10FourthCoordinate v = r :=
    zmod4_mixed_pairs_cross_differences_cover _ _ _ _ r
      hxyFourth huvFourth
  have horderFive : Z20K10HasDifferenceOrder S 5 := by
    rcases hcover 0 with h | h | h | h
    · exact ⟨x, hx, u, hu, hxu,
        z20_frequencyOrder_five_of_fifth_ne_zero_of_fourth_eq_zero
          (x - u) hxuFifth (by simpa using h)⟩
    · exact ⟨x, hx, v, hv, hxv,
        z20_frequencyOrder_five_of_fifth_ne_zero_of_fourth_eq_zero
          (x - v) hxvFifth (by simpa using h)⟩
    · exact ⟨y, hy, u, hu, hyu,
        z20_frequencyOrder_five_of_fifth_ne_zero_of_fourth_eq_zero
          (y - u) hyuFifth (by simpa using h)⟩
    · exact ⟨y, hy, v, hv, hyv,
        z20_frequencyOrder_five_of_fifth_ne_zero_of_fourth_eq_zero
          (y - v) hyvFifth (by simpa using h)⟩
  have horderTen : Z20K10HasDifferenceOrder S 10 := by
    rcases hcover 2 with h | h | h | h
    · exact ⟨x, hx, u, hu, hxu,
        z20_frequencyOrder_ten_of_fifth_ne_zero_of_fourth_eq_two
          (x - u) hxuFifth (by simpa using h)⟩
    · exact ⟨x, hx, v, hv, hxv,
        z20_frequencyOrder_ten_of_fifth_ne_zero_of_fourth_eq_two
          (x - v) hxvFifth (by simpa using h)⟩
    · exact ⟨y, hy, u, hu, hyu,
        z20_frequencyOrder_ten_of_fifth_ne_zero_of_fourth_eq_two
          (y - u) hyuFifth (by simpa using h)⟩
    · exact ⟨y, hy, v, hv, hyv,
        z20_frequencyOrder_ten_of_fifth_ne_zero_of_fourth_eq_two
          (y - v) hyvFifth (by simpa using h)⟩
  have horderTwenty : Z20K10HasDifferenceOrder S 20 := by
    rcases hcover 1 with h | h | h | h
    · exact ⟨x, hx, u, hu, hxu,
        z20_frequencyOrder_twenty_of_fifth_ne_zero_of_fourth_odd
          (x - u) hxuFifth (Or.inl (by simpa using h))⟩
    · exact ⟨x, hx, v, hv, hxv,
        z20_frequencyOrder_twenty_of_fifth_ne_zero_of_fourth_odd
          (x - v) hxvFifth (Or.inl (by simpa using h))⟩
    · exact ⟨y, hy, u, hu, hyu,
        z20_frequencyOrder_twenty_of_fifth_ne_zero_of_fourth_odd
          (y - u) hyuFifth (Or.inl (by simpa using h))⟩
    · exact ⟨y, hy, v, hv, hyv,
        z20_frequencyOrder_twenty_of_fifth_ne_zero_of_fourth_odd
          (y - v) hyvFifth (Or.inl (by simpa using h))⟩
  exact ⟨⟨x, hx, y, hy, hxy, hxyOrder⟩,
    ⟨u, hu, v, hv, huv, huvOrder⟩,
    horderFive, horderTen, horderTwenty⟩

#print axioms z20_k10_mixed_fifth_pairs_force_all_orders

end Fuglede
