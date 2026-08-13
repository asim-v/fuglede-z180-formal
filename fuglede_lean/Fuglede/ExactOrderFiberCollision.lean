import Fuglede.ExactOrderDistribution
import Fuglede.FinsetFiberCollision

/-!
# Residue collisions as exact-order distribution sums

This file is the semantic bridge between a finite residue projection and an
integer exact-order certificate.  The only projection-specific input is the
pointwise statement `f x = f y ↔ frequencyOrder N (x - y) ∈ orders`.

Once that statement is available, the collision count is exactly the sum of
the corresponding exact-order distribution variables.  The final two
theorems transfer the generic balanced lower bound and capacity upper bound
to that integer sum.  No Fourier, spectral, or solver claim is used here.
-/

namespace Fuglede

open scoped BigOperators

variable {N : ℕ} [NeZero N]
variable {β : Type*}

/-- A projection collision count is the sum of the exact-order classes that
are invisible to the projection.  Keeping the order set as an explicit
argument makes this theorem usable by generated fixed-modulus adapters. -/
theorem finsetSameFiberPairs_card_eq_sum_exactOrderDistribution
    (X : Finset (ZMod N)) (f : ZMod N → β) (orders : Finset ℕ)
    (hiff : ∀ x ∈ X, ∀ y ∈ X,
      f x = f y ↔ frequencyOrder N (x - y) ∈ orders) :
    (finsetSameFiberPairs X f).card =
      ∑ d ∈ orders, exactOrderDistribution X d := by
  classical
  let P := finsetSameFiberPairs X f
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := P)
    (t := orders)
    (f := fun p ↦ frequencyOrder N (p.1 - p.2))
    (by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpX, hpEq⟩
      exact (hiff p.1 (Finset.mem_product.mp hpX).1
        p.2 (Finset.mem_product.mp hpX).2).mp hpEq)
  rw [show (finsetSameFiberPairs X f).card = P.card from rfl, hfiber]
  apply Finset.sum_congr rfl
  intro d hd
  rw [exactOrderDistribution]
  congr 1
  ext p
  simp only [P, finsetSameFiberPairs, exactOrderPairs,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hpX, _hpEq⟩, hpOrder⟩
    exact ⟨hpX, hpOrder⟩
  · rintro ⟨hpX, hpOrder⟩
    have hpInvisible : frequencyOrder N (p.1 - p.2) ∈ orders := by
      rw [hpOrder]
      exact hd
    have hpEq : f p.1 = f p.2 :=
      (hiff p.1 hpX.1 p.2 hpX.2).mpr hpInvisible
    exact ⟨⟨hpX, hpEq⟩, hpOrder⟩

/-- Integer form consumed directly by QF_LIA certificate adapters. -/
theorem finsetSameFiberPairs_card_eq_sum_exactOrderDistributionInt
    (X : Finset (ZMod N)) (f : ZMod N → β) (orders : Finset ℕ)
    (hiff : ∀ x ∈ X, ∀ y ∈ X,
      f x = f y ↔ frequencyOrder N (x - y) ∈ orders) :
    ((finsetSameFiberPairs X f).card : ℤ) =
      ∑ d ∈ orders, exactOrderDistributionInt X d := by
  simp only [exactOrderDistributionInt]
  exact_mod_cast
    finsetSameFiberPairs_card_eq_sum_exactOrderDistribution X f orders hiff

/-- Balanced occupancy gives a lower bound on the exact-order sum invisible
to a finite projection. -/
theorem sum_exactOrderDistributionInt_lower_balanced_of_fibres
    [Fintype β] (X : Finset (ZMod N)) (f : ZMod N → β)
    (orders : Finset ℕ) {m u r : ℕ}
    (hiff : ∀ x ∈ X, ∀ y ∈ X,
      f x = f y ↔ frequencyOrder N (x - y) ∈ orders)
    (hcard : Fintype.card β = m)
    (hmass : X.card = m * u + r) (hr : r ≤ m) :
    (r : ℤ) * ((u : ℤ) + 1) ^ 2 +
        ((m : ℤ) - (r : ℤ)) * (u : ℤ) ^ 2 ≤
      ∑ d ∈ orders, exactOrderDistributionInt X d := by
  rw [← finsetSameFiberPairs_card_eq_sum_exactOrderDistributionInt
    X f orders hiff]
  exact finsetSameFiberPairs_card_lower_balanced X f hcard hmass hr

/-- A pointwise fibre-capacity estimate gives an upper bound on the same
exact-order sum. -/
theorem sum_exactOrderDistributionInt_le_capacityEnergy_of_fibres
    [Fintype β] (X : Finset (ZMod N)) (f : ZMod N → β)
    (orders : Finset ℕ) {c : ℕ}
    (hiff : ∀ x ∈ X, ∀ y ∈ X,
      f x = f y ↔ frequencyOrder N (x - y) ∈ orders)
    (hc : 0 < c) (hcap : ∀ b, finsetFiberOccupancy X f b ≤ c) :
    (∑ d ∈ orders, exactOrderDistributionInt X d) ≤
      (capacityEnergy c X.card : ℤ) := by
  rw [← finsetSameFiberPairs_card_eq_sum_exactOrderDistributionInt
    X f orders hiff]
  exact finsetSameFiberPairs_card_le_capacityEnergy X f hc hcap

end Fuglede
