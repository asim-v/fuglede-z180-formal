import Fuglede.Z180K10ModThreeObstruction
import Mathlib.Tactic

/-!
# Closure of the cardinality-ten spectral branch in `ZMod 180`

The modulo-twenty image either tiles immediately with one of the two fixed
two-point complements, or it has mixed order-two/order-four fifth fibres.
The mixed case forces every nontrivial divisor order of twenty and is
excluded by the characteristic-three geometric-sum obstruction.
-/

namespace Fuglede

set_option maxHeartbeats 0

/-- The injective modulo-twenty image of a cardinality-ten spectral set
tiles `ZMod 20`. -/
theorem z180_k10_projection20_image_tiles_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 10) :
    ∃ C : Finset (ZMod 20), Tiles (A.image z180K10Projection20) C := by
  classical
  obtain ⟨hinjA, hinjL, hbalancedA, _hbalancedL⟩ :=
    z180_k10_fkms_pr_gateway hSpec hcard
  have hcardL : L.card = 10 := hSpec.2.1.symm.trans hcard
  have himageCard : (A.image z180K10Projection20).card = 10 := by
    rw [Finset.card_image_of_injOn hinjA, hcard]
  by_contra hnontile
  obtain ⟨htwo, hfour⟩ :=
    z20_k10_nontiler_has_mixed_fifth_pair_orders himageCard hnontile
  have hbalancedImage :
      Z20K10BalancedFifths (A.image z180K10Projection20) :=
    z20K10BalancedFifths_image_projection20 hinjA hbalancedA
  have horders := z20_k10_mixed_fifth_pairs_force_all_orders
    hbalancedImage htwo hfour
  have hfactors :=
    z180_k10_all_projection20_spectrum_factors_of_all_difference_orders
      hSpec horders
  exact (z180_k10_not_all_projection20_factors hcardL hinjL) hfactors

/-- Every cardinality-ten cyclotomic spectral set in `ZMod 180` tiles. -/
theorem z180_k10_exists_tiling_of_spectral
    {A L : Finset (ZMod 180)}
    (hSpec : CyclotomicSpectrum 180 A L) (hcard : A.card = 10) :
    ∃ B : Finset (ZMod 180), Tiles A B := by
  apply z180_k10_exists_tiling_of_projection20_image_tile hSpec hcard
  exact z180_k10_projection20_image_tiles_of_spectral hSpec hcard

#print axioms z180_k10_exists_tiling_of_spectral

end Fuglede
