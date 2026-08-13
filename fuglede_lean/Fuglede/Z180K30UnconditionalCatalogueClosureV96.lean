import Fuglede.Z180K30ExceptionalProjectiveProfileAggregateV97
import Fuglede.Z180K30ExceptionalFramedCandidateExtractionV95
import Fuglede.Z180K30CatalogueMasterClosureV81

/-!
# Unconditional K30 catalogue closure

The complete V97 projective-profile audit supplies marginal orbit coverage, while
the V95 common-frame audit supplies the coupled five-Gram catalogue witness.
Together they discharge the finite K30 catalogue hypothesis in V83 and hence
the final `ZMod 180` spectral-to-tiling theorem through V81.
-/

namespace Fuglede

noncomputable section

theorem z180_k30_exceptional_marginalCoverage_v96 :
    Z180K30ExceptionalMarginalCoverageV83 :=
  z180_k30_exceptional_marginalCoverage_of_projectiveNormalization_v86
    Z180K30ExceptionalRawV2.z180_k30_projective_normalization_v97

noncomputable def z180_k30_exceptional_catalogue_completeness_v96 :
    Z180K30ExceptionalCatalogueCompletenessV80 :=
  z180_k30_catalogue_completeness_of_kernels_v83
    z180_k30_exceptional_marginalCoverage_v96
    z180_k30_exceptionalFramedStarCatalogue_v95

theorem z180_exists_tiling_of_spectral_v96
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  exact z180_exists_tiling_of_spectral_of_k30_catalogue_v81
    z180_k30_exceptional_catalogue_completeness_v96 hSpec

#print axioms z180_k30_exceptional_catalogue_completeness_v96
#print axioms z180_exists_tiling_of_spectral_v96

end
end Fuglede
