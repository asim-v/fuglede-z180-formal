import Fuglede.Z180K6Bridge

/-!
# Conditional closure of the cardinality-six branch in `ZMod 180`

`Z180K6Bridge` proves every automatic and terminal part of the branch.  This
module exposes the final result with exactly one additional mathematical
hypothesis: a non-tiling cardinality-six set has no nonzero Fourier-zero order
outside `{4, 30}`.  That hypothesis is precisely the still-unformalized
five-level descent plus normalized zero-profile classification.
-/

namespace Fuglede

/-- Spectral-to-tile for `|A|=6`, conditional on the exact structural lemma
that remains outside the kernel.  The hypothesis says only what is consumed
by the already kernel-checked terminal graph; it does not assume a tiling
complement or any stronger classification. -/
theorem z180_k6_exists_tiling_of_spectral_of_nonTiler_zero_order_classification
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 6)
    (hclassification :
      (¬ ∃ B : Finset (ZMod 180), Tiles A B) →
        ∀ d : ZMod 180, d ≠ 0 → CyclotomicZero 180 A d →
          (frequencyOrder 180 d = 4 ∨ frequencyOrder 180 d = 30)) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  apply z180_k6_exists_tiling_of_spectral_of_nonTilerReduction
    hSpec hcard
  intro hnot d hd hzero
  exact ⟨hd, hclassification hnot d hd hzero⟩

#print axioms
  z180_k6_exists_tiling_of_spectral_of_nonTiler_zero_order_classification

end Fuglede
