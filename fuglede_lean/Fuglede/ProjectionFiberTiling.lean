import Fuglede.FiniteTiling
import Fuglede.FrequencyOrder
import Mathlib.Tactic

/-!
# Tiling from opposite orders inside cyclic projection fibres

This is the modulus-independent additive endpoint behind the prime-power
fibre argument.  A candidate complement lies in the kernel of a cyclic
projection.  If nonzero differences of the set inside a projection fibre
have one exact order, while nonzero differences of the complement have a
different exact order, then the addition map is injective.  The cardinality
identity upgrades this to a tiling.
-/

namespace Fuglede

/-- A projection-fibre set and a kernel complement tile when their possible
nonzero exact difference orders lie in disjoint finite palettes.

The former single-order endpoint is the singleton-palette specialization.
Allowing palettes is essential already in `ZMod 8`: valid complements can
have differences of orders `2` and `8` while the set has order `4`.
-/
theorem tiles_of_cyclic_projection_fiber_disjoint_order_palettes
    {N : Nat} [NeZero N] {A B : Finset (ZMod N)}
    {m : Nat} {setOrders complementOrders : Finset Nat}
    (hm : m ∣ N)
    (hcard : A.card * B.card = N)
    (hBkernel : ∀ b ∈ B, (ZMod.cast b : ZMod m) = 0)
    (hAorders : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
      (ZMod.cast a : ZMod m) = ZMod.cast a' →
      frequencyOrder N (a - a') ∈ setOrders)
    (hBorders : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' →
      frequencyOrder N (b - b') ∈ complementOrders)
    (hdisjoint : Disjoint setOrders complementOrders) :
    Tiles A B := by
  apply (Fintype.bijective_iff_injective_and_card (sumMap A B)).2
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ hsum
    have ha : a ∈ A := (Finset.mem_product.mp hab).1
    have hb : b ∈ B := (Finset.mem_product.mp hab).2
    have ha' : a' ∈ A := (Finset.mem_product.mp hab').1
    have hb' : b' ∈ B := (Finset.mem_product.mp hab').2
    change a + b = a' + b' at hsum
    have haa : a = a' := by
      by_contra hane
      have hcast : (ZMod.cast a : ZMod m) = ZMod.cast a' := by
        have hmapped := congrArg
          (fun z : ZMod N => (ZMod.cast z : ZMod m)) hsum
        simpa [ZMod.cast_add hm, hBkernel b hb, hBkernel b' hb'] using hmapped
      have hbbne : b' ≠ b := by
        intro hbb
        subst b'
        exact hane (add_right_cancel hsum)
      have hdiff : a - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add]
        simpa [add_comm] using hsum
      have hset : frequencyOrder N (a - a') ∈ setOrders :=
        hAorders a ha a' ha' hane hcast
      have hcomplement : frequencyOrder N (a - a') ∈ complementOrders := by
        rw [hdiff]
        exact hBorders b' hb' b hb hbbne
      exact (Finset.disjoint_left.mp hdisjoint) hset hcomplement
    subst a'
    have hbb : b = b' := add_left_cancel hsum
    subst b'
    rfl
  · simpa only [Fintype.card_coe, Finset.card_product, ZMod.card] using hcard

/-- A cyclic projection-fibre set and a kernel complement with different
nonzero difference orders tile as soon as their cardinalities multiply to
the modulus. -/
theorem tiles_of_cyclic_projection_fiber_opposite_orders
    {N : Nat} [NeZero N] {A B : Finset (ZMod N)} {m rA rB : Nat}
    (hm : m ∣ N)
    (hcard : A.card * B.card = N)
    (hBkernel : ∀ b ∈ B, (ZMod.cast b : ZMod m) = 0)
    (hAorder : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' →
      (ZMod.cast a : ZMod m) = ZMod.cast a' →
      frequencyOrder N (a - a') = rA)
    (hBorder : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' →
      frequencyOrder N (b - b') = rB)
    (horders : rA ≠ rB) :
    Tiles A B := by
  apply (Fintype.bijective_iff_injective_and_card (sumMap A B)).2
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ hsum
    have ha : a ∈ A := (Finset.mem_product.mp hab).1
    have hb : b ∈ B := (Finset.mem_product.mp hab).2
    have ha' : a' ∈ A := (Finset.mem_product.mp hab').1
    have hb' : b' ∈ B := (Finset.mem_product.mp hab').2
    change a + b = a' + b' at hsum
    have haa : a = a' := by
      by_contra hane
      have hcast : (ZMod.cast a : ZMod m) = ZMod.cast a' := by
        have hmapped := congrArg
          (fun z : ZMod N => (ZMod.cast z : ZMod m)) hsum
        simpa [ZMod.cast_add hm, hBkernel b hb, hBkernel b' hb'] using hmapped
      have hbbne : b' ≠ b := by
        intro hbb
        subst b'
        exact hane (add_right_cancel hsum)
      have hdiff : a - a' = b' - b := by
        rw [sub_eq_sub_iff_add_eq_add]
        simpa [add_comm] using hsum
      apply horders
      calc
        rA = frequencyOrder N (a - a') :=
          (hAorder a ha a' ha' hane hcast).symm
        _ = frequencyOrder N (b' - b) := congrArg _ hdiff
        _ = rB := hBorder b' hb' b hb hbbne
    subst a'
    have hbb : b = b' := add_left_cancel hsum
    subst b'
    rfl
  · simpa only [Fintype.card_coe, Finset.card_product, ZMod.card] using hcard

#print axioms tiles_of_cyclic_projection_fiber_opposite_orders
#print axioms tiles_of_cyclic_projection_fiber_disjoint_order_palettes

end Fuglede
