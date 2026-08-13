import Fuglede.Z180MasterReductionK33
import Fuglede.Z180K6UnconditionalClosure
import Fuglede.Z180K10Closure
import Fuglede.Z180K12UnconditionalClosure

/-!
# Master reduction to cardinalities 18, 24, and 30

This wrapper consumes the kernel-checked unconditional closures for
cardinalities `6`, `10`, and `12`.  It leaves exactly the three active
cardinality branches and does not assume any certificate for them.
-/

namespace Fuglede

theorem z180_spectral_master_reduction_to_eighteen_twentyfour_thirty
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    (∃ B : Finset (ZMod 180), Tiles A B) ∨
      A.card = 18 ∨ A.card = 24 ∨ A.card = 30 := by
  rcases z180_spectral_master_reduction_without_k33 hSpec with
    htiles | h6 | h10 | h12 | h18 | h30 | h24
  · exact Or.inl htiles
  · exact Or.inl (z180_k6_exists_tiling_of_spectral hSpec h6)
  · exact Or.inl (z180_k10_exists_tiling_of_spectral hSpec h10)
  · exact Or.inl (z180_k12_exists_tiling_of_spectral hSpec h12)
  · exact Or.inr (Or.inl h18)
  · exact Or.inr (Or.inr (Or.inr h30))
  · exact Or.inr (Or.inr (Or.inl h24))

#print axioms z180_spectral_master_reduction_to_eighteen_twentyfour_thirty

end Fuglede
