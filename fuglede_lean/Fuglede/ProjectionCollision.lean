import Fuglede.CRT2310
import Fuglede.InnerDistribution
import Fuglede.ProjectionBounds
import Fuglede.ProjectionTiling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Projection fibres and collision counts for `ZMod 2310`

For a collection `S` of CRT coordinates, this file packages the coordinate
projection, the occupancies of its fibres, and the exact identities relating
their second moment to the inner distribution.  The final theorem turns the
vanishing of all off-diagonal projection collisions into a tiling by the
kernel of the projection.
-/

namespace Fuglede

open scoped BigOperators

/-- The dependent product of the CRT coordinate groups selected by `S`. -/
abbrev CRTProjection (S : Finset (Fin 5)) :=
  (i : {i : Fin 5 // i ∈ S}) → ZMod (crt2310Modulus i.1)

/-- Restriction of the full CRT map to the coordinates selected by `S`. -/
noncomputable def crtProjection (S : Finset (Fin 5)) :
    ZMod 2310 →+ CRTProjection S where
  toFun x i := toCRT2310 x i.1
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    exact congrFun (toCRT2310_add x y) i.1

@[simp]
theorem crtProjection_apply (S : Finset (Fin 5)) (x : ZMod 2310)
    (i : {i : Fin 5 // i ∈ S}) :
    crtProjection S x i = toCRT2310 x i.1 := rfl

/-- Two points have the same selected coordinates exactly when their
difference support is disjoint from the selected set. -/
theorem crtProjection_eq_iff_disjoint (S : Finset (Fin 5))
    (x y : ZMod 2310) :
    crtProjection S x = crtProjection S y ↔
      Disjoint (differenceSupport x y) S := by
  classical
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro i hi hS
    have hi' : toCRT2310 x i ≠ toCRT2310 y i :=
      mem_differenceSupport.mp hi
    exact hi' (congrFun h ⟨i, hS⟩)
  · intro h
    funext i
    by_contra hne
    have hi : i.1 ∈ differenceSupport x y :=
      mem_differenceSupport.mpr hne
    exact (Finset.disjoint_left.mp h) hi i.2

/-- Intersection form of `crtProjection_eq_iff_disjoint`. -/
theorem crtProjection_eq_iff_inter_eq_empty (S : Finset (Fin 5))
    (x y : ZMod 2310) :
    crtProjection S x = crtProjection S y ↔
      differenceSupport x y ∩ S = ∅ := by
  rw [crtProjection_eq_iff_disjoint, Finset.disjoint_iff_inter_eq_empty]

/-- Number of elements of `X` in one fibre of the selected-coordinate map. -/
noncomputable def projectionOccupancy (X : Finset (ZMod 2310))
    (S : Finset (Fin 5)) (z : CRTProjection S) : ℕ :=
  (X.filter fun x => crtProjection S x = z).card

/-- Ordered pairs in `X` which collide under the selected-coordinate map. -/
noncomputable def projectionPairCount (X : Finset (ZMod 2310))
    (S : Finset (Fin 5)) : ℕ :=
  ((X ×ˢ X).filter fun p => crtProjection S p.1 = crtProjection S p.2).card

/-- Ordered, off-diagonal pairs in `X` which collide under the projection. -/
noncomputable def projectionOffDiagonalCount (X : Finset (ZMod 2310))
    (S : Finset (Fin 5)) : ℕ :=
  ((X ×ˢ X).filter fun p =>
    p.1 ≠ p.2 ∧ crtProjection S p.1 = crtProjection S p.2).card

/-- The second moment of the fibre occupancies is exactly the number of
ordered pairs with equal projection. -/
theorem sum_projectionOccupancy_sq (X : Finset (ZMod 2310))
    (S : Finset (Fin 5)) :
    ∑ z : CRTProjection S, projectionOccupancy X S z ^ 2 =
      projectionPairCount X S := by
  classical
  let P := (X ×ˢ X).filter fun p =>
    crtProjection S p.1 = crtProjection S p.2
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := P)
    (t := (Finset.univ : Finset (CRTProjection S)))
    (f := fun p => crtProjection S p.1)
    (by simp)
  rw [projectionPairCount, show
      ((X ×ˢ X).filter fun p =>
        crtProjection S p.1 = crtProjection S p.2) = P from rfl]
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro z _
  rw [projectionOccupancy, pow_two]
  have hfilter :
      P.filter (fun p => crtProjection S p.1 = z) =
        (X.filter fun x => crtProjection S x = z) ×ˢ
          (X.filter fun x => crtProjection S x = z) := by
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_product]
    aesop
  rw [hfilter, Finset.card_product]

/-- Projection collisions are precisely the inner-distribution classes whose
support avoids all selected coordinates. -/
theorem projectionPairCount_eq_sum_innerDistribution
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    projectionPairCount X S =
      ∑ T ∈ (Finset.univ : Finset (Finset (Fin 5))),
        if Disjoint T S then innerDistribution X T else 0 := by
  classical
  let P := (X ×ˢ X).filter fun p =>
    crtProjection S p.1 = crtProjection S p.2
  let supports := (Finset.univ : Finset (Finset (Fin 5))).filter fun T =>
    Disjoint T S
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := P)
    (t := supports)
    (f := fun p => differenceSupport p.1 p.2)
    (by
      intro p hp
      have heq := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (crtProjection_eq_iff_disjoint S p.1 p.2).mp heq⟩)
  rw [projectionPairCount, show
      ((X ×ˢ X).filter fun p =>
        crtProjection S p.1 = crtProjection S p.2) = P from rfl]
  rw [hfiber]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hTS : Disjoint T S
  · simp only [hTS, if_true]
    rw [innerDistribution]
    congr 1
    ext p
    simp only [P, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hpX, hproj⟩, hsupp⟩
      exact ⟨hpX, hsupp⟩
    · rintro ⟨hpX, hsupp⟩
      exact ⟨⟨hpX,
        (crtProjection_eq_iff_disjoint S p.1 p.2).mpr (hsupp ▸ hTS)⟩,
        hsupp⟩
  · simp [hTS]

/-- A support-filter presentation without an `if`, convenient for later
arithmetical estimates. -/
theorem projectionPairCount_eq_sum_innerDistribution_filter
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    projectionPairCount X S =
      ∑ T ∈ (Finset.univ : Finset (Finset (Fin 5))).filter
          (fun T => Disjoint T S),
        innerDistribution X T := by
  classical
  rw [projectionPairCount_eq_sum_innerDistribution, Finset.sum_filter]

/-- Off-diagonal projection collisions are exactly the nonempty support
classes which avoid the selected coordinates. -/
theorem projectionOffDiagonalCount_eq_sum_innerDistribution
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    projectionOffDiagonalCount X S =
      ∑ T ∈ (Finset.univ : Finset (Finset (Fin 5))).filter
          (fun T => T ≠ ∅ ∧ Disjoint T S),
        innerDistribution X T := by
  classical
  let P := (X ×ˢ X).filter fun p =>
    p.1 ≠ p.2 ∧ crtProjection S p.1 = crtProjection S p.2
  let supports := (Finset.univ : Finset (Finset (Fin 5))).filter fun T =>
    T ≠ ∅ ∧ Disjoint T S
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := P)
    (t := supports)
    (f := fun p => differenceSupport p.1 p.2)
    (by
      intro p hp
      rcases (Finset.mem_filter.mp hp).2 with ⟨hne, heq⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨fun hsupp => hne ((differenceSupport_eq_empty_iff _ _).mp hsupp),
          (crtProjection_eq_iff_disjoint S p.1 p.2).mp heq⟩⟩)
  rw [projectionOffDiagonalCount, show
      ((X ×ˢ X).filter fun p =>
        p.1 ≠ p.2 ∧ crtProjection S p.1 = crtProjection S p.2) = P from rfl]
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro T hT
  rcases (Finset.mem_filter.mp hT).2 with ⟨hTne, hTS⟩
  rw [innerDistribution]
  congr 1
  ext p
  simp only [P, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hpX, hne, hproj⟩, hsupp⟩
    exact ⟨hpX, hsupp⟩
  · rintro ⟨hpX, hsupp⟩
    refine ⟨⟨hpX, ?_, ?_⟩, hsupp⟩
    · intro heq
      apply hTne
      rw [← hsupp]
      exact (differenceSupport_eq_empty_iff _ _).mpr heq
    · exact (crtProjection_eq_iff_disjoint S p.1 p.2).mpr (hsupp ▸ hTS)

/-- Vanishing off-diagonal collision count is equivalent to injectivity of
the projection on `X`. -/
theorem projectionOffDiagonalCount_eq_zero_iff_injOn
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5)) :
    projectionOffDiagonalCount X S = 0 ↔
      Set.InjOn (crtProjection S) (X : Set (ZMod 2310)) := by
  classical
  rw [projectionOffDiagonalCount, Finset.card_eq_zero]
  constructor
  · intro hempty x hx y hy hxy
    by_contra hne
    have hp : (x, y) ∈
        ((X ×ˢ X).filter fun p =>
          p.1 ≠ p.2 ∧ crtProjection S p.1 = crtProjection S p.2) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩,
        ⟨hne, hxy⟩⟩
    rw [hempty] at hp
    exact Finset.notMem_empty _ hp
  · intro hinj
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpX, hne, heq⟩
    exact hne (hinj (Finset.mem_product.mp hpX).1
      (Finset.mem_product.mp hpX).2 heq)

/-- The vanishing of every nonempty inner-distribution class invisible to
the selected coordinates forces injectivity of the projection on `X`. -/
theorem projection_injOn_of_sum_innerDistribution_eq_zero
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5))
    (hzero :
      (∑ T ∈ (Finset.univ : Finset (Finset (Fin 5))).filter
          (fun T => T ≠ ∅ ∧ Disjoint T S),
        innerDistribution X T) = 0) :
    Set.InjOn (crtProjection S) (X : Set (ZMod 2310)) := by
  apply (projectionOffDiagonalCount_eq_zero_iff_injOn X S).mp
  rw [projectionOffDiagonalCount_eq_sum_innerDistribution]
  exact hzero

/-- A full set of collision-free representatives tiles `ZMod 2310` by the
kernel of the selected-coordinate projection. -/
theorem projection_tiles_kernel_of_sum_innerDistribution_eq_zero
    (X : Finset (ZMod 2310)) (S : Finset (Fin 5))
    (hzero :
      (∑ T ∈ (Finset.univ : Finset (Finset (Fin 5))).filter
          (fun T => T ≠ ∅ ∧ Disjoint T S),
        innerDistribution X T) = 0)
    (hcard : X.card = Fintype.card (CRTProjection S)) :
    Tiles X (kernelFinset (crtProjection S)) := by
  apply transversal_tiles_kernel (crtProjection S) X
  · have hinj := projection_injOn_of_sum_innerDistribution_eq_zero X S hzero
    intro a ha b hb hab
    apply hinj ha hb
    exact (sub_mem_ker_iff_map_eq (crtProjection S) a b).mp hab
  · exact hcard

end Fuglede
