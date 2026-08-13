import Fuglede.CRT2310
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod

/-!
# Inner distributions in the five CRT coordinates of `ZMod 2310`

For a finite set `X`, `innerDistribution X T` counts ordered pairs of
elements of `X` whose difference is nonzero in exactly the coordinates in
`T`.  The elementary mass identities in this file are the combinatorial
input for the later Krawtchouk/character-energy layer.
-/

namespace Fuglede

open scoped BigOperators

/-- The CRT-coordinate support on which two residues differ. -/
noncomputable def differenceSupport (x y : ZMod 2310) : Finset (Fin 5) :=
  crt2310Support (x - y)

@[simp]
theorem mem_differenceSupport {x y : ZMod 2310} {i : Fin 5} :
    i ∈ differenceSupport x y ↔ toCRT2310 x i ≠ toCRT2310 y i := by
  exact mem_crt2310Support_sub_iff x y i

/-- Two residues have empty difference support precisely when they agree. -/
@[simp]
theorem differenceSupport_eq_empty_iff (x y : ZMod 2310) :
    differenceSupport x y = ∅ ↔ x = y := by
  classical
  constructor
  · intro h
    apply toCRT2310_injective
    funext i
    by_contra hne
    have hi : i ∈ differenceSupport x y := mem_differenceSupport.mpr hne
    have hnot : i ∉ differenceSupport x y := by simp [h]
    exact hnot hi
  · intro h
    subst y
    ext i
    simp

/-- Swapping the endpoints does not change the coordinate support. -/
theorem differenceSupport_comm (x y : ZMod 2310) :
    differenceSupport x y = differenceSupport y x := by
  classical
  ext i
  simp [ne_comm]

/-- Number of ordered pairs in `X × X` having exact difference support `T`. -/
noncomputable def innerDistribution
    (X : Finset (ZMod 2310)) (T : Finset (Fin 5)) : ℕ :=
  ((X ×ˢ X).filter fun p ↦ differenceSupport p.1 p.2 = T).card

theorem innerDistribution_nonneg
    (X : Finset (ZMod 2310)) (T : Finset (Fin 5)) :
    0 ≤ innerDistribution X T :=
  Nat.zero_le _

/-- The integer-valued copy used by signed character-energy sums. -/
noncomputable def innerDistributionInt
    (X : Finset (ZMod 2310)) (T : Finset (Fin 5)) : ℤ :=
  innerDistribution X T

theorem innerDistributionInt_nonneg
    (X : Finset (ZMod 2310)) (T : Finset (Fin 5)) :
    0 ≤ innerDistributionInt X T := by
  simp [innerDistributionInt]

/-- The zero-support mass is exactly the diagonal of `X × X`. -/
@[simp]
theorem innerDistribution_empty (X : Finset (ZMod 2310)) :
    innerDistribution X ∅ = X.card := by
  classical
  rw [innerDistribution]
  have hfilter :
      ((X ×ˢ X).filter fun p ↦ differenceSupport p.1 p.2 = ∅) = X.diag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product,
      differenceSupport_eq_empty_iff, Finset.mem_diag]
    constructor
    · rintro ⟨⟨hp, hq⟩, hpq⟩
      exact ⟨hp, hpq⟩
    · rintro ⟨hp, hpq⟩
      exact ⟨⟨hp, hpq ▸ hp⟩, hpq⟩
  rw [hfilter, Finset.diag_card]

/-- Every ordered pair has one and only one exact support. -/
theorem sum_innerDistribution (X : Finset (ZMod 2310)) :
    ∑ T : Finset (Fin 5), innerDistribution X T = X.card ^ 2 := by
  classical
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := X ×ˢ X)
    (t := (Finset.univ : Finset (Finset (Fin 5))))
    (f := fun p ↦ differenceSupport p.1 p.2)
    (by simp)
  simpa [innerDistribution, pow_two] using hfiber.symm

private def swapResiduePair :
    (ZMod 2310 × ZMod 2310) ↪ (ZMod 2310 × ZMod 2310) where
  toFun p := (p.2, p.1)
  inj' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simpa using congrArg Prod.swap h

/-- Off the diagonal, ordered pairs occur in swapped pairs; hence every
nonzero exact-support mass is even. -/
theorem innerDistribution_even_of_nonempty
    (X : Finset (ZMod 2310)) {T : Finset (Fin 5)} (hT : T ≠ ∅) :
    Even (innerDistribution X T) := by
  classical
  let P := (X ×ˢ X).filter fun p ↦ differenceSupport p.1 p.2 = T
  let L := P.filter fun p ↦ p.1.val < p.2.val
  let U := P.filter fun p ↦ p.2.val < p.1.val
  have hP : P = L ∪ U := by
    ext p
    constructor
    · intro hp
      have hsupp : differenceSupport p.1 p.2 = T := by
        exact (Finset.mem_filter.mp hp).2
      have hne : p.1 ≠ p.2 := by
        intro heq
        apply hT
        rw [← hsupp]
        exact (differenceSupport_eq_empty_iff _ _).2 heq
      have hval : p.1.val ≠ p.2.val := fun h ↦
        hne (ZMod.val_injective 2310 h)
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · exact Finset.mem_union_left U (Finset.mem_filter.mpr ⟨hp, hlt⟩)
      · exact Finset.mem_union_right L (Finset.mem_filter.mpr ⟨hp, hgt⟩)
    · intro hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
  have hLU : Disjoint L U := by
    refine Finset.disjoint_left.mpr ?_
    intro p hpL hpU
    have hlt := (Finset.mem_filter.mp hpL).2
    have hgt := (Finset.mem_filter.mp hpU).2
    exact Nat.lt_asymm hlt hgt
  have hswap : L.map swapResiduePair = U := by
    ext p
    simp only [Finset.mem_map, swapResiduePair]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases Finset.mem_filter.mp hq with ⟨hqP, hqval⟩
      rcases Finset.mem_filter.mp hqP with ⟨hqXX, hqsupp⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
            ⟨(Finset.mem_product.mp hqXX).2, (Finset.mem_product.mp hqXX).1⟩,
          by simpa [differenceSupport_comm] using hqsupp⟩
      · exact hqval
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpval⟩
      rcases Finset.mem_filter.mp hpP with ⟨hpXX, hpsupp⟩
      refine ⟨(p.2, p.1), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
            ⟨(Finset.mem_product.mp hpXX).2, (Finset.mem_product.mp hpXX).1⟩,
          by simpa [differenceSupport_comm] using hpsupp⟩
      · exact hpval
  have hcardLU : L.card = U.card := by
    rw [← hswap, Finset.card_map]
  refine ⟨L.card, ?_⟩
  rw [innerDistribution, show
      ((X ×ˢ X).filter fun p ↦ differenceSupport p.1 p.2 = T) = P from rfl]
  rw [hP, Finset.card_union_of_disjoint hLU, ← hcardLU]

end Fuglede
