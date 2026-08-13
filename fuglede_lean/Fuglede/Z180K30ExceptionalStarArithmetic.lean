import Mathlib.Tactic

/-!
# Tiny integral obstructions for the seven non-H Gram orbits
-/

namespace Fuglede

theorem z180_k30_five_pm_six_sum_ne_zero
    (x : Fin 5 -> Int) (hx : forall i, x i = 6 \/ x i = -6) :
    (Finset.univ.sum x) != 0 := by
  have h0 := hx (0 : Fin 5)
  have h1 := hx (1 : Fin 5)
  have h2 := hx (2 : Fin 5)
  have h3 := hx (3 : Fin 5)
  have h4 := hx (4 : Fin 5)
  fin_cases h0 <;> fin_cases h1 <;> fin_cases h2 <;>
    fin_cases h3 <;> fin_cases h4 <;> norm_num_all

theorem z180_k30_five_gram_pair_types_sum_ne_zero
    (x y : Fin 5 -> Int)
    (hxy : forall i,
      (x i = 6 /\ y i = 0) \/
      (x i = -6 /\ y i = 6) \/
      (x i = 0 /\ y i = -6)) :
    (Finset.univ.sum x) != 0 \/ (Finset.univ.sum y) != 0 := by
  have h0 := hxy (0 : Fin 5)
  have h1 := hxy (1 : Fin 5)
  have h2 := hxy (2 : Fin 5)
  have h3 := hxy (3 : Fin 5)
  have h4 := hxy (4 : Fin 5)
  rcases h0 with h0 | h0 | h0 <;>
    rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;>
    rcases h4 with h4 | h4 | h4 <;>
    rcases h0 with ⟨rfl, rfl⟩ <;>
    rcases h1 with ⟨rfl, rfl⟩ <;>
    rcases h2 with ⟨rfl, rfl⟩ <;>
    rcases h3 with ⟨rfl, rfl⟩ <;>
    rcases h4 with ⟨rfl, rfl⟩ <;>
    norm_num

#print axioms z180_k30_five_pm_six_sum_ne_zero
#print axioms z180_k30_five_gram_pair_types_sum_ne_zero

end Fuglede
