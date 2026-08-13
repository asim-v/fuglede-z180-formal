import Fuglede.Z180K30ExceptionalActualFiveGramV79
import Fuglede.Z180K30CatalogueTilingClosureV68Fix

/-!
# K30 closure reduced to one finite catalogue theorem

The Fourier-block analysis and its normal branch are already formal.  In the
exceptional branch, `Z180K30ExceptionalActualFiveGramV79` constructs the exact
Boolean five-Gram certificate for the faithful raw fibres.  Consequently the
only remaining input is the finite statement that such a certificate belongs
to the exceptional catalogue.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

noncomputable section

/-- The sole finite certificate constructor still needed by the K30 analytic
closure. -/
def Z180K30ExceptionalCatalogueCompletenessV80 : Type :=
  ∀ U : Fin 5 → RawSet, ∀ V : RawSet,
    fiveGramStarB U V = true → Z180K30CatalogueAlternativeV65 V

/-- A complete finite catalogue turns every thirty-point spectral set into a
tiler.  No order-closure relaxation is used. -/
theorem z180_k30_exists_tiling_of_catalogue_completeness_v80
    (hcomplete : Z180K30ExceptionalCatalogueCompletenessV80)
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L)
    (hcard : A.card = 30) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  let data : Z180K30BalancedFibreDataV22 A L :=
    z180K30BalancedFibreDataV22_of_spectral hSpec hcard
  apply z180_k30_exists_tiling_of_catalogue_bridge_v68Fix
    hSpec hcard data
  intro s hex
  apply hcomplete
  exact z180_k30_actual_exceptional_fiveGramStar_v79
    hSpec hcard data s hex

#print axioms z180_k30_exists_tiling_of_catalogue_completeness_v80

end
end Fuglede
