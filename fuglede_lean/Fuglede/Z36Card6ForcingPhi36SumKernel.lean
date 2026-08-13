import Mathlib.Tactic

/-! Fixed reindexing of the 36 coordinates into six residue blocks modulo 6. -/

namespace Fuglede

def z36Mod6Block (b : Fin 36 → Int) (r : Fin 6) : Int :=
  ∑ q : Fin 6, b (finProdFinEquiv (q, r))

theorem z36_sum36_blocks_mod6
    (b : Fin 36 → Int) (hsum : (∑ i : Fin 36, b i) = 6) :
    (∑ r : Fin 6, z36Mod6Block b r) = 6 := by
  have hequiv : (∑ p : Fin 6 × Fin 6, b (finProdFinEquiv p)) =
      ∑ i : Fin 36, b i :=
    (finProdFinEquiv : Fin 6 × Fin 6 ≃ Fin 36).sum_comp b
  calc
    (∑ r : Fin 6, z36Mod6Block b r) =
        ∑ r : Fin 6, ∑ q : Fin 6, b (finProdFinEquiv (q, r)) := rfl
    _ = ∑ q : Fin 6, ∑ r : Fin 6, b (finProdFinEquiv (q, r)) :=
      Finset.sum_comm
    _ = ∑ p : Fin 6 × Fin 6, b (finProdFinEquiv p) := by
      simpa only [Prod.eta] using
        (Fintype.sum_prod_type'
          (fun (q : Fin 6) (r : Fin 6) => b (finProdFinEquiv (q, r)))).symm
    _ = ∑ i : Fin 36, b i := hequiv
    _ = 6 := hsum

#print axioms z36_sum36_blocks_mod6

end Fuglede
