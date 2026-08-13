import Fuglede.Z180K30ExceptionalCatalogueBridgeV80
import Fuglede.Z180MasterConditionalClosure

/-!
# Master closure from the finite K30 catalogue

This wrapper records that the exact finite catalogue constructor is the only
remaining input to the full spectral-to-tiling theorem on `ZMod 180`.
-/

namespace Fuglede

noncomputable section

theorem z180_k30_spectral_tiling_closure_of_catalogue_v81
    (hcomplete : Z180K30ExceptionalCatalogueCompletenessV80) :
    Z180K30SpectralTilingClosure := by
  intro A L hSpec hcard
  exact z180_k30_exists_tiling_of_catalogue_completeness_v80
    hcomplete hSpec hcard

theorem z180_exists_tiling_of_spectral_of_k30_catalogue_v81
    (hcomplete : Z180K30ExceptionalCatalogueCompletenessV80)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  exact z180_exists_tiling_of_spectral_of_k30_closure
    (z180_k30_spectral_tiling_closure_of_catalogue_v81 hcomplete) hSpec

#print axioms z180_k30_spectral_tiling_closure_of_catalogue_v81
#print axioms z180_exists_tiling_of_spectral_of_k30_catalogue_v81

end
end Fuglede
