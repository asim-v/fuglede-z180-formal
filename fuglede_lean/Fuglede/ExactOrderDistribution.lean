import Fuglede.SpectralFourier
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod

/-!
# Exact-order inner distributions in a cyclic group

For a finite set `X ⊆ ZMod N`, `exactOrderDistribution X d` counts ordered
pairs whose difference has additive order exactly `d`.  These are the typed
variables used by the exact-order Ramanujan relaxation for non-square-free
cyclic groups.

This file deliberately starts with the purely combinatorial layer.  The
Fourier/Ramanujan transform and spectral cross-implications are built on top
of these definitions in a separate module.
-/

namespace Fuglede

open scoped BigOperators

variable {N : ℕ} [NeZero N]

/-- Ordered pairs in `X × X` whose difference has exact additive order `d`. -/
noncomputable def exactOrderPairs
    (X : Finset (ZMod N)) (d : ℕ) : Finset (ZMod N × ZMod N) :=
  (X ×ˢ X).filter fun p ↦ frequencyOrder N (p.1 - p.2) = d

/-- Exact-order inner distribution of a finite cyclic set. -/
noncomputable def exactOrderDistribution
    (X : Finset (ZMod N)) (d : ℕ) : ℕ :=
  (exactOrderPairs X d).card

/-- Integer-valued copy used by the linear arithmetic certificate. -/
noncomputable def exactOrderDistributionInt
    (X : Finset (ZMod N)) (d : ℕ) : ℤ :=
  exactOrderDistribution X d

theorem exactOrderDistributionInt_nonneg
    (X : Finset (ZMod N)) (d : ℕ) :
    0 ≤ exactOrderDistributionInt X d := by
  simp [exactOrderDistributionInt]

/-- The order-one fibre is precisely the diagonal. -/
@[simp]
theorem exactOrderDistribution_one (X : Finset (ZMod N)) :
    exactOrderDistribution X 1 = X.card := by
  classical
  rw [exactOrderDistribution, exactOrderPairs]
  have hfilter :
      ((X ×ˢ X).filter fun p ↦ frequencyOrder N (p.1 - p.2) = 1) =
        X.diag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
    rw [frequencyOrder_eq_one_iff (NeZero.ne N), sub_eq_zero]
    constructor
    · rintro ⟨⟨hp, hq⟩, hpq⟩
      exact ⟨hp, hpq⟩
    · rintro ⟨hp, hpq⟩
      exact ⟨⟨hp, hpq ▸ hp⟩, hpq⟩
  rw [hfilter, Finset.diag_card]

@[simp]
theorem exactOrderDistributionInt_one (X : Finset (ZMod N)) :
    exactOrderDistributionInt X 1 = X.card := by
  simp [exactOrderDistributionInt]

/-- Every difference order in `ZMod N` divides the ambient modulus. -/
theorem frequencyOrder_dvd_modulus (d : ZMod N) :
    frequencyOrder N d ∣ N := by
  rw [frequencyOrder_eq_addOrderOf (NeZero.ne N)]
  simpa only [ZMod.card] using (addOrderOf_dvd_card (x := d))

/-- The divisor-indexed exact-order fibres partition `X × X`. -/
theorem sum_exactOrderDistribution (X : Finset (ZMod N)) :
    ∑ d ∈ N.divisors, exactOrderDistribution X d = X.card ^ 2 := by
  classical
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := X ×ˢ X)
    (t := N.divisors)
    (f := fun p ↦ frequencyOrder N (p.1 - p.2))
    (by
      intro p hp
      exact Nat.mem_divisors.mpr
        ⟨frequencyOrder_dvd_modulus (p.1 - p.2), NeZero.ne N⟩)
  simpa [exactOrderDistribution, exactOrderPairs, pow_two] using hfiber.symm

/-- Integer form of the total-mass identity. -/
theorem sum_exactOrderDistributionInt (X : Finset (ZMod N)) :
    ∑ d ∈ N.divisors, exactOrderDistributionInt X d = (X.card ^ 2 : ℕ) := by
  simp only [exactOrderDistributionInt]
  exact_mod_cast sum_exactOrderDistribution X

/-- A positive fibre supplies an actual ordered pair of that order. -/
theorem exists_pair_of_exactOrderDistribution_pos
    {X : Finset (ZMod N)} {d : ℕ}
    (hpos : 0 < exactOrderDistribution X d) :
    ∃ x ∈ X, ∃ y ∈ X, frequencyOrder N (x - y) = d := by
  rw [exactOrderDistribution, exactOrderPairs] at hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_product] at hp
  exact ⟨p.1, hp.1.1, p.2, hp.1.2, hp.2⟩

end Fuglede
