import Fuglede.ExactOrderDistribution
import Mathlib.Tactic

/-!
# Parity of nontrivial exact-order distributions

Every non-diagonal ordered pair is accompanied by its swapped pair.  Since
swapping reverses the difference without changing its additive order, each
exact-order class other than order one has even cardinality.
-/

namespace Fuglede

private def swapExactOrderPair {N : Nat} :
    (ZMod N × ZMod N) ↪ (ZMod N × ZMod N) where
  toFun p := (p.2, p.1)
  inj' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simpa using congrArg Prod.swap h

/-- Every exact-order mass away from the diagonal is even. -/
theorem exactOrderDistribution_even_of_ne_one
    {N : Nat} [NeZero N] (X : Finset (ZMod N)) {d : Nat} (hd : d ≠ 1) :
    Even (exactOrderDistribution X d) := by
  classical
  let P := exactOrderPairs X d
  let L := P.filter fun p ↦ p.1.val < p.2.val
  let U := P.filter fun p ↦ p.2.val < p.1.val
  have hP : P = L ∪ U := by
    ext p
    constructor
    · intro hp
      have horder : frequencyOrder N (p.1 - p.2) = d := by
        exact (Finset.mem_filter.mp hp).2
      have hne : p.1 ≠ p.2 := by
        intro heq
        apply hd
        calc
          d = frequencyOrder N (p.1 - p.2) := horder.symm
          _ = 1 := by
            rw [heq, sub_self]
            exact (frequencyOrder_eq_one_iff (NeZero.ne N) 0).2 rfl
      have hval : p.1.val ≠ p.2.val := fun h ↦
        hne (ZMod.val_injective N h)
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
  have hswap : L.map swapExactOrderPair = U := by
    ext p
    simp only [Finset.mem_map, swapExactOrderPair]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases Finset.mem_filter.mp hq with ⟨hqP, hqval⟩
      rcases Finset.mem_filter.mp hqP with ⟨hqXX, hqorder⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
            ⟨(Finset.mem_product.mp hqXX).2, (Finset.mem_product.mp hqXX).1⟩,
          by
            change frequencyOrder N (q.2 - q.1) = d
            simpa only [frequencyOrder_sub_comm (NeZero.ne N)] using hqorder⟩
      · exact hqval
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpval⟩
      rcases Finset.mem_filter.mp hpP with ⟨hpXX, hporder⟩
      refine ⟨(p.2, p.1), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
            ⟨(Finset.mem_product.mp hpXX).2, (Finset.mem_product.mp hpXX).1⟩,
          by simpa only [frequencyOrder_sub_comm (NeZero.ne N)] using hporder⟩
      · exact hpval
  have hcardLU : L.card = U.card := by
    rw [← hswap, Finset.card_map]
  refine ⟨L.card, ?_⟩
  rw [exactOrderDistribution, show exactOrderPairs X d = P from rfl]
  rw [hP, Finset.card_union_of_disjoint hLU, ← hcardLU]

/-- Integer witness form consumed directly by linear-arithmetic adapters. -/
theorem exactOrderDistributionInt_eq_two_mul
    {N : Nat} [NeZero N] (X : Finset (ZMod N)) {d : Nat} (hd : d ≠ 1) :
    ∃ k : Int, exactOrderDistributionInt X d = 2 * k := by
  obtain ⟨k, hk⟩ := exactOrderDistribution_even_of_ne_one X hd
  refine ⟨(k : Int), ?_⟩
  have hk' : exactOrderDistribution X d = 2 * k := by omega
  rw [exactOrderDistributionInt]
  exact_mod_cast hk'

#print axioms exactOrderDistribution_even_of_ne_one
#print axioms exactOrderDistributionInt_eq_two_mul

end Fuglede
