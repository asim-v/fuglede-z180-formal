import Fuglede.Z180K10Structural
import Fuglede.ProjectionFiberTiling
import Mathlib.Tactic

/-!
# Pair structure in the modulo-twenty projection at cardinality ten

This file contains only the elementary cyclic-group part of the `|A| = 10`
argument.  A two-point fibre modulo five has a difference of order two or
four.  If only one of these two orders occurs, one of the fixed complements
`{0,5}` or `{0,10}` tiles the projected set.  Consequently a projected
nontiler has a pair of each order.

No enumeration of cardinality-ten subsets is used.
-/

namespace Fuglede

/-- The modulo-five coordinate on `ZMod 20`. -/
def z20K10FifthCoordinate (x : ZMod 20) : ZMod 5 :=
  ZMod.cast x

/-- Number of points in one modulo-five fibre. -/
def z20K10FifthOccupancy (S : Finset (ZMod 20)) (c : ZMod 5) : Nat :=
  (S.filter fun x => z20K10FifthCoordinate x = c).card

/-- Exactly two points occur in every modulo-five fibre. -/
def Z20K10BalancedFifths (S : Finset (ZMod 20)) : Prop :=
  ∀ c : ZMod 5, z20K10FifthOccupancy S c = 2

/-- A same-fibre pair whose nonzero difference has prescribed exact order. -/
def Z20K10HasFifthPairOrder (S : Finset (ZMod 20)) (r : Nat) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧
    z20K10FifthCoordinate x = z20K10FifthCoordinate y ∧
    frequencyOrder 20 (x - y) = r

/-- An arbitrary pair whose nonzero difference has prescribed exact order. -/
def Z20K10HasDifferenceOrder (S : Finset (ZMod 20)) (r : Nat) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧
    frequencyOrder 20 (x - y) = r

/-- Reduction through `ZMod 20` commutes with every further cyclic
projection used below. -/
theorem cast_projection20_eq_cast
    {m : Nat} (hm20 : m ∣ 20) (x : ZMod 180) :
    (ZMod.cast (z180K10Projection20 x) : ZMod m) = ZMod.cast x := by
  change (ZMod.cast (ZMod.cast x : ZMod 20) : ZMod m) = ZMod.cast x
  have hcomp := ZMod.castHom_comp hm20 (by norm_num : 20 ∣ 180)
  exact DFunLike.congr_fun hcomp x

/-- The fifth coordinate is unchanged by the projection to `ZMod 20`. -/
@[simp]
theorem z20K10FifthCoordinate_projection20 (x : ZMod 180) :
    z20K10FifthCoordinate (z180K10Projection20 x) =
      z180K10FifthCoordinate x := by
  rw [z180K10FifthCoordinate, toCRT180_apply]
  exact cast_projection20_eq_cast (by norm_num : 5 ∣ 20) x

/-- Injective projection preserves each fifth-fibre occupancy. -/
theorem z20K10FifthOccupancy_image_projection20
    {A : Finset (ZMod 180)}
    (hinj : Set.InjOn z180K10Projection20 (A : Set (ZMod 180)))
    (c : ZMod 5) :
    z20K10FifthOccupancy (A.image z180K10Projection20) c =
      z180K10FifthOccupancy A c := by
  classical
  let T := A.filter fun x => z180K10FifthCoordinate x = c
  have hfilter :
      (A.image z180K10Projection20).filter
          (fun z => z20K10FifthCoordinate z = c) =
        T.image z180K10Projection20 := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzimage, hzcoord⟩ := Finset.mem_filter.mp hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzimage
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hx, by
        simpa only [z20K10FifthCoordinate_projection20,
          Z180K10FifthCoordinateSpace, crt180Modulus_two] using hzcoord⟩
    · intro hz
      obtain ⟨x, hxT, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hx, hxcoord⟩ := Finset.mem_filter.mp hxT
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, by
        simpa only [z20K10FifthCoordinate_projection20,
          Z180K10FifthCoordinateSpace, crt180Modulus_two] using hxcoord⟩
  rw [z20K10FifthOccupancy, z180K10FifthOccupancy, hfilter]
  apply Finset.card_image_of_injOn
  exact hinj.mono (by
    intro x hx
    exact (Finset.mem_filter.mp hx).1)

/-- The balanced-fibre conclusion from the spectral gateway descends to the
injective modulo-twenty image. -/
theorem z20K10BalancedFifths_image_projection20
    {A : Finset (ZMod 180)}
    (hinj : Set.InjOn z180K10Projection20 (A : Set (ZMod 180)))
    (hbalanced : ∀ c : Z180K10FifthCoordinateSpace,
      z180K10FifthOccupancy A c = 2) :
    Z20K10BalancedFifths (A.image z180K10Projection20) := by
  intro c
  rw [z20K10FifthOccupancy_image_projection20 hinj c]
  exact hbalanced c

/-- A nonzero difference inside one modulo-five fibre of `ZMod 20` has
exact order two or four. -/
theorem z20_frequencyOrder_two_or_four_of_same_fifth
    (x y : ZMod 20) (hxy : x ≠ y)
    (hfive : z20K10FifthCoordinate x = z20K10FifthCoordinate y) :
    frequencyOrder 20 (x - y) = 2 ∨
      frequencyOrder 20 (x - y) = 4 := by
  have hcastZero : (ZMod.cast (x - y) : ZMod 5) = 0 := by
    rw [ZMod.cast_sub (by norm_num : 5 ∣ 20)]
    exact sub_eq_zero.mpr hfive
  have hnatCastZero : ((x - y).val : ZMod 5) = 0 := by
    simpa only [ZMod.cast_eq_val] using hcastZero
  have hdvd : 5 ∣ (x - y).val :=
    (ZMod.natCast_eq_zero_iff (x - y).val 5).1 hnatCastZero
  obtain ⟨k, hk⟩ := hdvd
  have hvalne : (x - y).val ≠ 0 := by
    intro hzero
    have hdiff : x - y = 0 := (ZMod.val_eq_zero (x - y)).1 hzero
    exact hxy (sub_eq_zero.mp hdiff)
  have hkpos : 0 < k := by omega
  have hklt : k < 4 := by
    have hvalLt := (x - y).val_lt
    omega
  unfold frequencyOrder
  rw [hk]
  interval_cases k <;> norm_num at hkpos ⊢

/-- Fixed complement whose nonzero difference has exact order two. -/
def z20K10OrderTwoComplement : Finset (ZMod 20) := {0, 10}

/-- Fixed complement whose nonzero difference has exact order four. -/
def z20K10OrderFourComplement : Finset (ZMod 20) := {0, 5}

@[simp]
theorem card_z20K10OrderTwoComplement :
    z20K10OrderTwoComplement.card = 2 := by
  decide

@[simp]
theorem card_z20K10OrderFourComplement :
    z20K10OrderFourComplement.card = 2 := by
  decide

theorem cast5_eq_zero_of_mem_z20K10OrderTwoComplement
    {b : ZMod 20} (hb : b ∈ z20K10OrderTwoComplement) :
    (ZMod.cast b : ZMod 5) = 0 := by
  simp only [z20K10OrderTwoComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl <;> decide

theorem cast5_eq_zero_of_mem_z20K10OrderFourComplement
    {b : ZMod 20} (hb : b ∈ z20K10OrderFourComplement) :
    (ZMod.cast b : ZMod 5) = 0 := by
  simp only [z20K10OrderFourComplement, Finset.mem_insert,
    Finset.mem_singleton] at hb
  rcases hb with rfl | rfl <;> decide

theorem frequencyOrder_two_of_distinct_mem_z20K10OrderTwoComplement :
    ∀ b ∈ z20K10OrderTwoComplement,
      ∀ b' ∈ z20K10OrderTwoComplement, b ≠ b' →
        frequencyOrder 20 (b - b') = 2 := by
  decide

theorem frequencyOrder_four_of_distinct_mem_z20K10OrderFourComplement :
    ∀ b ∈ z20K10OrderFourComplement,
      ∀ b' ∈ z20K10OrderFourComplement, b ≠ b' →
        frequencyOrder 20 (b - b') = 4 := by
  decide

/-- If no same-fibre order-two pair occurs, every same-fibre difference has
order four and the shift-ten complement tiles. -/
theorem z20_k10_tiles_of_no_fifth_pair_order_two
    {S : Finset (ZMod 20)} (hcard : S.card = 10)
    (hno : ¬ Z20K10HasFifthPairOrder S 2) :
    Tiles S z20K10OrderTwoComplement := by
  apply tiles_of_cyclic_projection_fiber_opposite_orders
      (m := 5) (rA := 4) (rB := 2)
  · norm_num
  · simp [hcard]
  · exact fun b hb => cast5_eq_zero_of_mem_z20K10OrderTwoComplement hb
  · intro x hx y hy hxy hfive
    rcases z20_frequencyOrder_two_or_four_of_same_fifth x y hxy hfive
      with htwo | hfour
    · exact False.elim (hno ⟨x, hx, y, hy, hxy, hfive, htwo⟩)
    · exact hfour
  · exact frequencyOrder_two_of_distinct_mem_z20K10OrderTwoComplement
  · norm_num

/-- If no same-fibre order-four pair occurs, every same-fibre difference has
order two and the shift-five complement tiles. -/
theorem z20_k10_tiles_of_no_fifth_pair_order_four
    {S : Finset (ZMod 20)} (hcard : S.card = 10)
    (hno : ¬ Z20K10HasFifthPairOrder S 4) :
    Tiles S z20K10OrderFourComplement := by
  apply tiles_of_cyclic_projection_fiber_opposite_orders
      (m := 5) (rA := 2) (rB := 4)
  · norm_num
  · simp [hcard]
  · exact fun b hb => cast5_eq_zero_of_mem_z20K10OrderFourComplement hb
  · intro x hx y hy hxy hfive
    rcases z20_frequencyOrder_two_or_four_of_same_fifth x y hxy hfive
      with htwo | hfour
    · exact htwo
    · exact False.elim (hno ⟨x, hx, y, hy, hxy, hfive, hfour⟩)
  · exact frequencyOrder_four_of_distinct_mem_z20K10OrderFourComplement
  · norm_num

/-- A cardinality-ten projected nontiler necessarily contains one
same-fibre pair of each possible order. -/
theorem z20_k10_nontiler_has_mixed_fifth_pair_orders
    {S : Finset (ZMod 20)} (hcard : S.card = 10)
    (hnot : ¬ ∃ B : Finset (ZMod 20), Tiles S B) :
    Z20K10HasFifthPairOrder S 2 ∧
      Z20K10HasFifthPairOrder S 4 := by
  constructor
  · by_contra hno
    apply hnot
    exact ⟨z20K10OrderTwoComplement,
      z20_k10_tiles_of_no_fifth_pair_order_two hcard hno⟩
  · by_contra hno
    apply hnot
    exact ⟨z20K10OrderFourComplement,
      z20_k10_tiles_of_no_fifth_pair_order_four hcard hno⟩

#print axioms z20_k10_nontiler_has_mixed_fifth_pair_orders

end Fuglede
