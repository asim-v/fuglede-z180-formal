import Mathlib.Tactic

/-!
# Tiny integral obstructions for the seven non-H Gram orbits (V3)
-/

namespace Fuglede

theorem z180_k30_five_pm_six_sum_ne_zero_v3
    (x : Fin 5 -> Int) (hx : forall i, x i = 6 \/ x i = -6) :
    (Finset.univ.sum x) ≠ 0 := by
  have h0 := hx (0 : Fin 5)
  have h1 := hx (1 : Fin 5)
  have h2 := hx (2 : Fin 5)
  have h3 := hx (3 : Fin 5)
  have h4 := hx (4 : Fin 5)
  rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;>
    norm_num [Fin.sum_univ_succ] at *

theorem z180_k30_five_gram_pair_types_sum_ne_zero_v3
    (x y : Fin 5 -> Int)
    (hxy : forall i,
      (x i = 6 /\ y i = 0) \/
      (x i = -6 /\ y i = 6) \/
      (x i = 0 /\ y i = -6)) :
    (Finset.univ.sum x) ≠ 0 \/ (Finset.univ.sum y) ≠ 0 := by
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
    rcases h0 with ⟨hx0, hy0⟩ <;>
    rcases h1 with ⟨hx1, hy1⟩ <;>
    rcases h2 with ⟨hx2, hy2⟩ <;>
    rcases h3 with ⟨hx3, hy3⟩ <;>
    rcases h4 with ⟨hx4, hy4⟩ <;>
    norm_num [Fin.sum_univ_succ] at *

#print axioms z180_k30_five_pm_six_sum_ne_zero_v3
#print axioms z180_k30_five_gram_pair_types_sum_ne_zero_v3

end Fuglede
