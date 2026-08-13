import Fuglede.ProjectionBounds
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Collision identities for fibres of a finite map

This file is the purely combinatorial interface between residue fibres and
integer arithmetic certificates.  For a finite set `X` and a map `f`, the
second moment of the fibre occupancies is exactly the number of ordered
pairs in `X × X` with the same image under `f`.

The lower and upper bounds below are consequences of the generic occupancy
bounds in `ProjectionBounds`; they make no Fourier or spectral assumption.
-/

namespace Fuglede

open scoped BigOperators

variable {α β : Type*}

/-- Number of elements of `X` in one fibre of `f`. -/
noncomputable def finsetFiberOccupancy
    (X : Finset α) (f : α → β) (b : β) : Nat := by
  classical
  exact (X.filter fun x => f x = b).card

/-- Ordered pairs of elements of `X` that collide under `f`. -/
noncomputable def finsetSameFiberPairs
    (X : Finset α) (f : α → β) : Finset (α × α) := by
  classical
  exact (X ×ˢ X).filter fun p => f p.1 = f p.2

/-- The fibres over a finite codomain partition `X`. -/
theorem occupancyMass_finsetFiberOccupancy
    [Fintype β] (X : Finset α) (f : α → β) :
    occupancyMass (finsetFiberOccupancy X f) = X.card := by
  classical
  simpa [occupancyMass, finsetFiberOccupancy] using
    (Finset.sum_card_fiberwise_eq_card_filter X
      (Finset.univ : Finset β) f)

/-- Fibrewise double counting: the sum of squared occupancies is the exact
ordered-pair collision count. -/
theorem sum_finsetFiberOccupancy_sq
    [Fintype β] (X : Finset α) (f : α → β) :
    (∑ b : β, finsetFiberOccupancy X f b ^ 2) =
      (finsetSameFiberPairs X f).card := by
  classical
  let P := finsetSameFiberPairs X f
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := P)
    (t := (Finset.univ : Finset β))
    (f := fun p => f p.1)
    (by simp [P, finsetSameFiberPairs])
  rw [show (finsetSameFiberPairs X f).card = P.card from rfl]
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro b _
  rw [finsetFiberOccupancy, pow_two]
  have hfilter :
      P.filter (fun p => f p.1 = b) =
        (X.filter fun x => f x = b) ×ˢ
          (X.filter fun x => f x = b) := by
    ext p
    simp only [P, finsetSameFiberPairs, Finset.mem_filter,
      Finset.mem_product]
    aesop
  rw [hfilter, Finset.card_product]

/-- Integer collision mass is the natural ordered-pair count coerced to
`Int`. -/
theorem collisionMass_finsetFiberOccupancy
    [Fintype β] (X : Finset α) (f : α → β) :
    collisionMass (finsetFiberOccupancy X f) =
      ((finsetSameFiberPairs X f).card : Int) := by
  calc
    collisionMass (finsetFiberOccupancy X f) =
        ((∑ b : β, finsetFiberOccupancy X f b ^ 2 : Nat) : Int) := by
      simp [collisionMass]
    _ = ((finsetSameFiberPairs X f).card : Int) := by
      rw [sum_finsetFiberOccupancy_sq]

/-- Balanced collision lower bound over an arbitrary finite codomain of
known cardinality. -/
theorem collisionMass_lower_balanced_of_fintype_card
    [Fintype β] (n : β → Nat) {m u r : Nat}
    (hcard : Fintype.card β = m)
    (hmass : occupancyMass n = m * u + r) (hr : r ≤ m) :
    (r : Int) * ((u : Int) + 1) ^ 2 +
        ((m : Int) - (r : Int)) * (u : Int) ^ 2 ≤ collisionMass n := by
  let e : Fin m ≃ β := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let n' : Fin m → Nat := fun i => n (e i)
  have hoccupancy : occupancyMass n' = occupancyMass n := by
    simpa only [occupancyMass, n'] using e.sum_comp n
  have hcollision : collisionMass n' = collisionMass n := by
    simpa only [collisionMass, n'] using
      e.sum_comp (fun i => (n i : Int) ^ 2)
  have hmass' : occupancyMass n' = m * u + r := hoccupancy.trans hmass
  exact (collisionMass_lower_balanced n' hmass' hr).trans_eq hcollision

/-- Sharp balanced lower bound for the number of same-fibre ordered pairs. -/
theorem finsetSameFiberPairs_card_lower_balanced
    [Fintype β] (X : Finset α) (f : α → β) {m u r : Nat}
    (hcard : Fintype.card β = m)
    (hmass : X.card = m * u + r) (hr : r ≤ m) :
    (r : Int) * ((u : Int) + 1) ^ 2 +
        ((m : Int) - (r : Int)) * (u : Int) ^ 2 ≤
      ((finsetSameFiberPairs X f).card : Int) := by
  rw [← collisionMass_finsetFiberOccupancy X f]
  apply collisionMass_lower_balanced_of_fintype_card
      (finsetFiberOccupancy X f) hcard
  · simpa only [occupancyMass_finsetFiberOccupancy] using hmass
  · exact hr

/-- Capacity-energy upper bound for the number of same-fibre ordered pairs. -/
theorem finsetSameFiberPairs_card_le_capacityEnergy
    [Fintype β] (X : Finset α) (f : α → β) {c : Nat}
    (hc : 0 < c) (hcap : ∀ b, finsetFiberOccupancy X f b ≤ c) :
    ((finsetSameFiberPairs X f).card : Int) ≤
      (capacityEnergy c X.card : Int) := by
  rw [← collisionMass_finsetFiberOccupancy X f,
    ← occupancyMass_finsetFiberOccupancy X f]
  exact collisionMass_le_capacityEnergy (finsetFiberOccupancy X f) hc hcap

end Fuglede
