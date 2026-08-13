import Fuglede.Z180K12EnvelopeBridge
import Fuglede.Z180FiveLevelFourier

/-!
# Removing the five-level premise from the cardinality-twelve descent

Once a non-tiler is known to satisfy `Phi_30 | A` and `Phi_6 ∤ A`, the
five-level Fourier theorem forces every residue class modulo five to occur.
Thus the existing `Z180K12NonTilerM6Reduction` interface is equivalent to the
two cyclotomic assertions alone.
-/

namespace Fuglede

open Polynomial

/-- The genuinely remaining cyclotomic content of the non-tiler descent. -/
def Z180K12NonTilerCyclotomicM6Reduction
    (A : Finset (ZMod 180)) : Prop :=
  (¬ ∃ B : Finset (ZMod 180), Tiles A B) →
    cyclotomic 30 Int ∣ maskPolynomial 180 A ∧
      ¬ cyclotomic 6 Int ∣ maskPolynomial 180 A

theorem z180_k12_nonTilerM6Reduction_of_cyclotomic_reduction
    {A : Finset (ZMod 180)}
    (hcore : Z180K12NonTilerCyclotomicM6Reduction A) :
    Z180K12NonTilerM6Reduction A := by
  intro hnotTiles
  obtain ⟨h30, h6⟩ := hcore hnotTiles
  exact ⟨h30, h6,
    z180_phi30_defect_fiveLevels_nonempty A h30 h6⟩

theorem z180_k12_nonTiler_cyclotomic_reduction_of_M6Reduction
    {A : Finset (ZMod 180)}
    (hreduction : Z180K12NonTilerM6Reduction A) :
    Z180K12NonTilerCyclotomicM6Reduction A := by
  intro hnotTiles
  exact ⟨(hreduction hnotTiles).1, (hreduction hnotTiles).2.1⟩

theorem z180_k12_nonTilerM6Reduction_iff_cyclotomic_reduction
    (A : Finset (ZMod 180)) :
    Z180K12NonTilerM6Reduction A ↔
      Z180K12NonTilerCyclotomicM6Reduction A := by
  constructor
  · exact z180_k12_nonTiler_cyclotomic_reduction_of_M6Reduction
  · exact z180_k12_nonTilerM6Reduction_of_cyclotomic_reduction

#print axioms z180_k12_nonTilerM6Reduction_of_cyclotomic_reduction
#print axioms z180_k12_nonTilerM6Reduction_iff_cyclotomic_reduction

end Fuglede
