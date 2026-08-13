import Fuglede.Z180MasterReduction
import Fuglede.Z180NondivisorK33Closure

/-!
# Master reduction after the compact cardinality-33 exclusion

This wrapper keeps the previously sealed master reduction unchanged and
removes its final `A.card = 33` branch with the dedicated typed adapter.
-/

namespace Fuglede

/-- After excluding cardinality thirty-three, the only remaining frontier
below the upper-half endpoint consists of five divisor cases and the
cardinality-twenty-four exceptional case. -/
theorem z180_spectral_master_reduction_without_k33
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    (∃ B : Finset (ZMod 180), Tiles A B) ∨
      A.card = 6 ∨ A.card = 10 ∨ A.card = 12 ∨
      A.card = 18 ∨ A.card = 30 ∨ A.card = 24 := by
  rcases z180_spectral_master_reduction hSpec with
    htiles | h6 | h10 | h12 | h18 | h30 | h24 | h33
  · exact Or.inl htiles
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · right; omega
  · exact (z180_nondivisor_k33_card_ne_of_spectral hSpec h33).elim

#print axioms z180_spectral_master_reduction_without_k33

end Fuglede
