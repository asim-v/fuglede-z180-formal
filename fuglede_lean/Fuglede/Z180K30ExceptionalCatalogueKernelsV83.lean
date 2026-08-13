import Fuglede.Z180K30ExceptionalCatalogueBridgeV80
import Fuglede.Z180K30FiveGramStarSemanticsV82

/-!
# Independent finite kernels for the K30 catalogue

The finite completeness proof naturally splits into a marginal projective
normalization and a coupled five-Gram calculation in one common affine frame.
This module records that split without hiding either obligation.
-/

namespace Fuglede

open Z180K30ExceptionalRawV2

/-- Every accepted rank-two projective pair is covered by the eight affine
orbits audited by the projective shards. -/
def Z180K30ExceptionalMarginalCoverageV83 : Prop :=
  ∀ U V : RawSet, exceptionalPairB U V = true →
    orbitCoveredB U = true ∧ orbitCoveredB V = true

/-- Once all six-point sets have been placed in the audited affine orbits,
the common-frame star calculation constructs the exact catalogue witness. -/
def Z180K30ExceptionalFramedStarCatalogueV83 : Type :=
  ∀ U : Fin 5 → RawSet, ∀ V : RawSet,
    fiveGramStarB U V = true →
    (∀ i, orbitCoveredB (U i) = true) →
    orbitCoveredB V = true →
    Z180K30CatalogueAlternativeV65 V

def z180_k30_catalogue_completeness_of_kernels_v83
    (hmarginal : Z180K30ExceptionalMarginalCoverageV83)
    (hframed : Z180K30ExceptionalFramedStarCatalogueV83) :
    Z180K30ExceptionalCatalogueCompletenessV80 := by
  intro U V hstar
  have hcovered (i : Fin 5) :
      orbitCoveredB (U i) = true ∧ orbitCoveredB V = true :=
    hmarginal (U i) V
      (fiveGramStar_exceptionalPair_v82 U V hstar i)
  exact hframed U V hstar (fun i => (hcovered i).1) (hcovered 0).2

#print axioms z180_k30_catalogue_completeness_of_kernels_v83

end Fuglede
