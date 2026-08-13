import Fuglede.Z180K30ExceptionalBoundaryOfGramV60
import Fuglede.Z180K30FibreTiling
import Fuglede.Z180SmallCardinality
import Mathlib.Tactic

/-!
# Tiling closure after the normal/exceptional K30 dichotomy

Both honest outputs of the Fourier-block analysis already imply a tiling.
A common six-point spectrum gives one common complement for all five fibres;
injectivity modulo thirty makes the set a complete transversal for the kernel
of the projection to `ZMod 30`.
-/

namespace Fuglede

noncomputable section

/-- A thirty-point transversal for reduction modulo thirty tiles by the
six-element kernel of that reduction. -/
theorem z180_k30_tiles_of_projection30_injOn_v61
    {A : Finset (ZMod 180)} (hcard : A.card = 30)
    (hinj : Set.InjOn z180K30Projection30 (A : Set (ZMod 180))) :
    Tiles A (kernelFinset z180K30Projection30) := by
  apply transversal_tiles_kernel z180K30Projection30 A
  · exact (kernel_difference_free_iff_injOn
      z180K30Projection30 A).2 hinj
  · simpa using hcard

/-- Either output of the sealed normal/exceptional boundary gives an exact
tiling of the original set in `ZMod 180`. -/
theorem z180_k30_exists_tiling_of_common_or_projection30_injOn_v61
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (hor : (∃ s, Z180K30CommonSpectrumAt A L s) ∨
      Set.InjOn z180K30Projection30 (A : Set (ZMod 180))) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  rcases hor with ⟨s, hcommon⟩ | hinj
  · have hcardA : ∀ i : Fin 5,
        (z180K30FifthFibres36 A i).card = 6 := by
      intro i
      exact z180_k30_fibre_card_six hSpec hcard (i.val : ZMod 5)
    obtain ⟨B, hB⟩ :=
      z180_k30_five_fibres_common_complement_of_common_spectrum
        (z180K30FifthFibres36 A) (z180K30FifthFibres36 L s)
          hcardA hcommon
    refine ⟨z180K30LiftComplement B,
      z180_k30_tiles_of_common_fibre_complement A B ?_⟩
    intro c
    simpa only [z180K30FifthFibres36, z180K30FinOfZMod5_cast] using
      hB (z180K30FinOfZMod5 c)
  · exact ⟨kernelFinset z180K30Projection30,
      z180_k30_tiles_of_projection30_injOn_v61 hcard hinj⟩

/-- The remaining hypotheses are exactly the two analytic/projective bridges
and the exact finite catalogue-to-H implication from the exceptional branch.
No total order-closure premise is used. -/
theorem z180_k30_exists_tiling_of_gram_bridges_v61
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 30)
    (data : Z180K30BalancedFibreDataV22 A L)
    (ProjectiveAlternative ResidueCandidate : Fin 5 → Prop)
    (rankTwoProjective : ∀ s,
      Z180K30ExceptionalGramEigenvalueData
        (z180K30DephasedFiveBlockGramDataV54
          hSpec hcard data s).toPositiveFamily.eigenvalue →
        ProjectiveAlternative s)
    (fourierProjectiveClasses : ∀ s,
      ProjectiveAlternative s → ResidueCandidate s)
    (certifiedOnlyH : ∀ s, ResidueCandidate s →
      Z180K30HCosetColumnConcrete L s) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  apply z180_k30_exists_tiling_of_common_or_projection30_injOn_v61
    hSpec hcard
  exact z180_k30_common_spectrum_or_projection30_injOn_of_gram_bridges_v60
    hSpec hcard data ProjectiveAlternative ResidueCandidate
      rankTwoProjective fourierProjectiveClasses certifiedOnlyH

#print axioms z180_k30_tiles_of_projection30_injOn_v61
#print axioms z180_k30_exists_tiling_of_common_or_projection30_injOn_v61
#print axioms z180_k30_exists_tiling_of_gram_bridges_v61

end
end Fuglede
