import Fuglede.MultiaxisRelaxation
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact local and projection bounds for the 2310 multi-axis relaxation

This file connects the combinatorial objects attached to an actual finite
subset of `ZMod 2310` with the integer bounds used by the multi-axis SMT
instances.  All statements are uniform in a subset of the five CRT axes.
-/

namespace Fuglede

open scoped BigOperators

@[simp]
theorem supportValency_empty : supportValency ∅ = 1 := by
  simp [supportValency]

/-- Allowed values in coordinate `i` for a vector with exact support `D`. -/
noncomputable def exactSupportCoordinateFinset
    (D : Finset (Fin 5)) (i : Fin 5) : Finset (ZMod (crt2310Modulus i)) :=
  Finset.univ.filter fun z ↦ (z ≠ 0 ↔ i ∈ D)

theorem card_exactSupportCoordinateFinset
    (D : Finset (Fin 5)) (i : Fin 5) :
    (exactSupportCoordinateFinset D i).card =
      if i ∈ D then crt2310Modulus i - 1 else 1 := by
  classical
  by_cases hi : i ∈ D
  · have hfinset : exactSupportCoordinateFinset D i =
        (Finset.univ : Finset (ZMod (crt2310Modulus i))).erase 0 := by
      ext z
      simp [exactSupportCoordinateFinset, hi]
    rw [hfinset, Finset.card_erase_of_mem (Finset.mem_univ 0)]
    simp [hi]
  · have hfinset : exactSupportCoordinateFinset D i = {0} := by
      ext z
      simp [exactSupportCoordinateFinset, hi]
    rw [hfinset]
    simp [hi]

/-- CRT vectors whose nonzero coordinate set is exactly `D`. -/
noncomputable def exactCRTSupportFinset (D : Finset (Fin 5)) : Finset CRT2310 :=
  Fintype.piFinset (exactSupportCoordinateFinset D)

@[simp]
theorem mem_exactCRTSupportFinset {D : Finset (Fin 5)} {v : CRT2310} :
    v ∈ exactCRTSupportFinset D ↔
      ∀ i : Fin 5, (v i ≠ 0 ↔ i ∈ D) := by
  classical
  simp [exactCRTSupportFinset, exactSupportCoordinateFinset]

theorem card_exactCRTSupportFinset (D : Finset (Fin 5)) :
    (exactCRTSupportFinset D).card = supportValency D := by
  classical
  rw [exactCRTSupportFinset, Fintype.card_piFinset]
  simp_rw [card_exactSupportCoordinateFinset]
  simp [supportValency]

/-- The trivial local bound obtained by forgetting the exact-support
condition on an ordered pair. -/
theorem innerDistribution_le_card_sq
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    innerDistribution X D ≤ X.card ^ 2 := by
  classical
  calc
    innerDistribution X D =
        ((X ×ˢ X).filter fun p ↦ differenceSupport p.1 p.2 = D).card := rfl
    _ ≤ (X ×ˢ X).card := Finset.card_filter_le _ _
    _ = X.card ^ 2 := by simp [pow_two]

/-- The local valency bound: after fixing the first endpoint, an exact
support `D` difference has only `supportValency D` possible CRT values. -/
theorem innerDistribution_le_card_mul_supportValency
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    innerDistribution X D ≤ X.card * supportValency D := by
  classical
  let P := (X ×ˢ X).filter fun p ↦ differenceSupport p.1 p.2 = D
  let f : ZMod 2310 × ZMod 2310 → ZMod 2310 × CRT2310 :=
    fun p ↦ (p.1, toCRT2310 (p.1 - p.2))
  have hmaps : Set.MapsTo f (P : Set (ZMod 2310 × ZMod 2310))
      (X ×ˢ exactCRTSupportFinset D : Finset (ZMod 2310 × CRT2310)) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpX, hsupp⟩
    apply Finset.mem_product.mpr
    constructor
    · exact (Finset.mem_product.mp hpX).1
    · apply mem_exactCRTSupportFinset.mpr
      intro i
      rw [← hsupp]
      exact (mem_crt2310Support (x := p.1 - p.2) (i := i)).symm
  have hinj : Set.InjOn f (P : Set (ZMod 2310 × ZMod 2310)) := by
    rintro ⟨x, y⟩ _ ⟨x', y'⟩ _ h
    have hx : x = x' := congrArg Prod.fst h
    have hd : toCRT2310 (x - y) = toCRT2310 (x' - y') :=
      congrArg Prod.snd h
    subst x'
    have hsub : x - y = x - y' := toCRT2310_injective hd
    have hy : y = y' := by simpa using hsub
    subst y'
    rfl
  calc
    innerDistribution X D = P.card := rfl
    _ ≤ (X ×ˢ exactCRTSupportFinset D).card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    _ = X.card * supportValency D := by
      rw [Finset.card_product, card_exactCRTSupportFinset]

/-- The single `min` bound appearing literally in the generated SMT-LIB. -/
theorem innerDistribution_le_min_card_sq_card_mul_supportValency
    (X : Finset (ZMod 2310)) (D : Finset (Fin 5)) :
    innerDistribution X D ≤
      min (X.card ^ 2) (X.card * supportValency D) := by
  exact le_min (innerDistribution_le_card_sq X D)
    (innerDistribution_le_card_mul_supportValency X D)

/-- The selected CRT projection has one cell for every choice of its
coordinates, hence exactly the product of the selected prime moduli. -/
theorem card_CRTProjection (S : Finset (Fin 5)) :
    Fintype.card (CRTProjection S) = supportModulus S := by
  classical
  rw [Fintype.card_pi]
  simpa only [ZMod.card, supportModulus] using
    (Finset.prod_coe_sort S crt2310Modulus)

theorem supportModulus_pos (S : Finset (Fin 5)) :
    0 < supportModulus S := by
  classical
  unfold supportModulus
  apply Finset.prod_pos
  intro i hi
  fin_cases i <;> norm_num [crt2310Modulus]

/-- Selected and complementary coordinate products multiply to `2310`. -/
theorem supportModulus_mul_compl (S : Finset (Fin 5)) :
    supportModulus S * supportModulus Sᶜ = 2310 := by
  classical
  simpa only [supportModulus, crt2310Modulus_prod] using
    (Finset.prod_mul_prod_compl S crt2310Modulus)

/-- The product of the complementary axes is the exact fibre capacity. -/
theorem supportModulus_compl_eq_div (S : Finset (Fin 5)) :
    supportModulus Sᶜ = 2310 / supportModulus S := by
  symm
  exact Nat.div_eq_of_eq_mul_right (supportModulus_pos S)
    (supportModulus_mul_compl S).symm

/-- Projection occupancies partition `X`. -/
theorem occupancyMass_projectionOccupancy
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    occupancyMass (projectionOccupancy X S) = X.card := by
  classical
  simpa [occupancyMass, projectionOccupancy] using
    (Finset.sum_card_fiberwise_eq_card_filter X
      (Finset.univ : Finset (CRTProjection S)) (crtProjection S))

/-- Each selected-coordinate fibre has at most the full complementary CRT
capacity `2310 / supportModulus S`. -/
theorem projectionOccupancy_le_capacity
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) (z : CRTProjection S) :
    projectionOccupancy X S z ≤ 2310 / supportModulus S := by
  classical
  let F := X.filter fun x ↦ crtProjection S x = z
  have hinj : Set.InjOn (crtProjection Sᶜ) (F : Set (ZMod 2310)) := by
    intro x hx y hy hcomp
    have hxz : crtProjection S x = z := (Finset.mem_filter.mp hx).2
    have hyz : crtProjection S y = z := (Finset.mem_filter.mp hy).2
    apply toCRT2310_injective
    funext i
    by_cases hi : i ∈ S
    · exact congrFun (hxz.trans hyz.symm) ⟨i, hi⟩
    · have hic : i ∈ Sᶜ := by simp [hi]
      exact congrFun hcomp ⟨i, hic⟩
  calc
    projectionOccupancy X S z = F.card := rfl
    _ ≤ (Finset.univ : Finset (CRTProjection Sᶜ)).card :=
      Finset.card_le_card_of_injOn (crtProjection Sᶜ) (by simp) hinj
    _ = Fintype.card (CRTProjection Sᶜ) := Finset.card_univ
    _ = supportModulus Sᶜ := card_CRTProjection Sᶜ
    _ = 2310 / supportModulus S := supportModulus_compl_eq_div S

/-- The abstract integer collision mass of the occupancy function is the
natural-number projection pair count, coerced to `ℤ`. -/
theorem collisionMass_projectionOccupancy
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    collisionMass (projectionOccupancy X S) =
      (projectionPairCount X S : ℤ) := by
  unfold collisionMass
  simp_rw [← Nat.cast_pow]
  rw [← Nat.cast_sum]
  exact congrArg (fun n : ℕ ↦ (n : ℤ))
    (sum_projectionOccupancy_sq X S)

/-- `collisionMass_lower_balanced` transported from `Fin m` to an arbitrary
finite type of cardinality `m`. -/
theorem collisionMass_lower_balanced_fintype
    {ι : Type*} [Fintype ι] (n : ι → ℕ) {m u r : ℕ}
    (hcard : Fintype.card ι = m)
    (hmass : occupancyMass n = m * u + r) (hr : r ≤ m) :
    (r : ℤ) * ((u : ℤ) + 1) ^ 2 +
        ((m : ℤ) - (r : ℤ)) * (u : ℤ) ^ 2 ≤ collisionMass n := by
  let e : Fin m ≃ ι := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let n' : Fin m → ℕ := fun i ↦ n (e i)
  have hoccupancy : occupancyMass n' = occupancyMass n := by
    simpa only [occupancyMass, n'] using e.sum_comp n
  have hcollision : collisionMass n' = collisionMass n := by
    simpa only [collisionMass, n'] using
      e.sum_comp (fun i ↦ (n i : ℤ) ^ 2)
  have hmass' : occupancyMass n' = m * u + r := hoccupancy.trans hmass
  exact (collisionMass_lower_balanced n' hmass' hr).trans_eq hcollision

/-- Balanced lower bound for an arbitrary selected set of CRT axes. -/
theorem projectionPairCount_lower_balanced
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) {u r : ℕ}
    (hmass : X.card = supportModulus S * u + r)
    (hr : r ≤ supportModulus S) :
    (r : ℤ) * ((u : ℤ) + 1) ^ 2 +
        ((supportModulus S : ℤ) - (r : ℤ)) * (u : ℤ) ^ 2 ≤
      (projectionPairCount X S : ℤ) := by
  rw [← collisionMass_projectionOccupancy]
  apply collisionMass_lower_balanced_fintype
      (projectionOccupancy X S) (card_CRTProjection S)
  · simpa only [occupancyMass_projectionOccupancy] using hmass
  · exact hr

/-- Capacity-energy upper bound for every selected set of CRT axes. -/
theorem projectionPairCount_le_capacityEnergy
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    (projectionPairCount X S : ℤ) ≤
      (capacityEnergy (2310 / supportModulus S) X.card : ℤ) := by
  rw [← collisionMass_projectionOccupancy,
    ← occupancyMass_projectionOccupancy X S]
  apply collisionMass_le_capacityEnergy
  · rw [← supportModulus_compl_eq_div]
    exact supportModulus_pos Sᶜ
  · exact projectionOccupancy_le_capacity X S

/-- Lower bound in the named form used by `MultiaxisConstraints`. -/
theorem projectionPairCount_lower_relaxation
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    (balancedCollisionLower X.card (supportModulus S) : ℤ) ≤
      (projectionPairCount X S : ℤ) := by
  let m := supportModulus S
  let u := X.card / m
  let r := X.card % m
  have hm : 0 < m := supportModulus_pos S
  have hr : r ≤ m := (Nat.mod_lt X.card hm).le
  have hmass : X.card = m * u + r := by
    simpa [m, u, r, Nat.mul_comm] using
      (Nat.div_add_mod X.card (supportModulus S)).symm
  have h := projectionPairCount_lower_balanced X S hmass hr
  simpa [balancedCollisionLower, m, u, r, Nat.cast_sub hr] using h

/-- Upper bound in the named form used by `MultiaxisConstraints`. -/
theorem projectionPairCount_upper_relaxation
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    (projectionPairCount X S : ℤ) ≤
      (projectionCapacityUpper X.card (supportModulus S) : ℤ) := by
  simpa [projectionCapacityUpper] using
    projectionPairCount_le_capacityEnergy X S

/-- Explicit saturated upper bound for an arbitrary quotient/remainder
decomposition by the fibre capacity. -/
theorem projectionPairCount_upper_capacity
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) {v s : ℕ}
    (hs : s < 2310 / supportModulus S)
    (hmass : X.card = (2310 / supportModulus S) * v + s) :
    (projectionPairCount X S : ℤ) ≤
      (v : ℤ) * (2310 / supportModulus S : ℤ) ^ 2 + (s : ℤ) ^ 2 := by
  rw [← collisionMass_projectionOccupancy]
  apply collisionMass_upper_capacity
      (projectionOccupancy X S)
  · rw [← supportModulus_compl_eq_div]
    exact supportModulus_pos Sᶜ
  · exact hs
  · exact projectionOccupancy_le_capacity X S
  · simpa only [occupancyMass_projectionOccupancy] using hmass

/-- Canonical balanced endpoint, with exactly the `div`/`mod` expression
used by `projection_collision_bounds` in the Python certificate generator. -/
theorem projectionPairCount_lower_divMod
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    (X.card % supportModulus S : ℤ) *
          ((X.card / supportModulus S : ℤ) + 1) ^ 2 +
        ((supportModulus S : ℤ) - (X.card % supportModulus S : ℤ)) *
          (X.card / supportModulus S : ℤ) ^ 2 ≤
      (projectionPairCount X S : ℤ) := by
  apply projectionPairCount_lower_balanced
  · simpa [Nat.mul_comm] using
      (Nat.div_add_mod X.card (supportModulus S)).symm
  · exact (Nat.mod_lt X.card (supportModulus_pos S)).le

/-- Canonical saturated endpoint, again in the exact `div`/`mod` form used
by the Python generator. -/
theorem projectionPairCount_upper_divMod
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    (projectionPairCount X S : ℤ) ≤
      ((X.card / (2310 / supportModulus S) : ℕ) : ℤ) *
          ((2310 / supportModulus S : ℕ) : ℤ) ^ 2 +
        ((X.card % (2310 / supportModulus S) : ℕ) : ℤ) ^ 2 := by
  apply projectionPairCount_upper_capacity
  · apply Nat.mod_lt
    rw [← supportModulus_compl_eq_div]
    exact supportModulus_pos Sᶜ
  · simpa [Nat.mul_comm] using
      (Nat.div_add_mod X.card (2310 / supportModulus S)).symm

/-- The lower endpoint rewritten as the exact support sum constrained in
the SMT instances. -/
theorem projectionSupportSum_lower_divMod
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    (X.card % supportModulus S : ℤ) *
          ((X.card / supportModulus S : ℤ) + 1) ^ 2 +
        ((supportModulus S : ℤ) - (X.card % supportModulus S : ℤ)) *
          (X.card / supportModulus S : ℤ) ^ 2 ≤
      ((∑ T ∈ (Finset.univ : Finset (Finset (Fin 5))).filter
          (fun T ↦ Disjoint T S), innerDistribution X T : ℕ) : ℤ) := by
  simpa only [projectionPairCount_eq_sum_innerDistribution_filter] using
    projectionPairCount_lower_divMod X S

/-- The saturated endpoint rewritten as the exact support sum constrained
in the SMT instances. -/
theorem projectionSupportSum_upper_divMod
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
      ((∑ T ∈ (Finset.univ : Finset (Finset (Fin 5))).filter
          (fun T ↦ Disjoint T S), innerDistribution X T : ℕ) : ℤ) ≤
      ((X.card / (2310 / supportModulus S) : ℕ) : ℤ) *
          ((2310 / supportModulus S : ℕ) : ℤ) ^ 2 +
        ((X.card % (2310 / supportModulus S) : ℕ) : ℤ) ^ 2 := by
  simpa only [projectionPairCount_eq_sum_innerDistribution_filter] using
    projectionPairCount_upper_divMod X S

/-- On side `0`, the abstract collision functional of the concrete
distribution is the actual projection pair count. -/
theorem multiaxisProjectionCollision_spectralPairDistribution_set
    (A L : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    multiaxisProjectionCollision (spectralPairDistribution A L) 0 S =
      (projectionPairCount A S : ℤ) := by
  rw [projectionPairCount_eq_sum_innerDistribution_filter]
  simp only [multiaxisProjectionCollision, spectralPairDistribution_set]
  rw [← Finset.sum_filter]
  simp only [innerDistributionInt, Nat.cast_sum]

/-- The corresponding collision identity on side `1`. -/
theorem multiaxisProjectionCollision_spectralPairDistribution_spectrum
    (A L : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    multiaxisProjectionCollision (spectralPairDistribution A L) 1 S =
      (projectionPairCount L S : ℤ) := by
  rw [projectionPairCount_eq_sum_innerDistribution_filter]
  simp only [multiaxisProjectionCollision, spectralPairDistribution_spectrum]
  rw [← Finset.sum_filter]
  simp only [innerDistributionInt, Nat.cast_sum]

end Fuglede
