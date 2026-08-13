import Fuglede.Z36Card6SpectralGateway
import Fuglede.Z36Card6ForcingThreeNine
import Fuglede.Z36Card6ForcingPhi3Phi18Semantic
import Fuglede.Z36Card6ForcingPhi3Phi36Semantic
import Fuglede.Z36Card6ForcingPhi36Semantic
import Fuglede.Z36Card6ForcingPhi6Phi9Phi18Semantic
import Fuglede.Z36Card6ForcingPhi9Phi12Phi36Semantic

/-!
# Closing the cardinality-six spectral case in `ZMod 36`

The six independently checked 0/1 cyclotomic forcing fields are assembled
here and passed to the exact nine-pattern spectral gateway.
-/

namespace Fuglede

/-- The complete set-side forcing package for six-point subsets of
`ZMod 36`. -/
theorem z36_card6_cyclotomic_forcing : Z36Card6CyclotomicForcing where
  zero_3_9_impossible := z36_zero_3_and_9_impossible
  zero_3_18_forces_2_6 := z36_zero_3_18_forces_2_6
  zero_3_36_forces_4_12 := z36_zero_3_36_forces_4_12
  zero_36_forces_12_or_18 := z36_zero_36_forces_12_or_18
  zero_6_9_18_forces_2 := z36_zero_6_9_18_forces_2
  zero_9_12_36_forces_4 := z36_zero_9_12_36_forces_4

/-- Every spectral six-point subset of `ZMod 36` tiles.  This inhabits the
exact induction premise exported by `Z180K6DescentImages`. -/
theorem z36_spectral_card6_implies_tile : Z36SpectralCard6ImpliesTile :=
  z36_spectral_card6_implies_tile_of_forcing z36_card6_cyclotomic_forcing

#print axioms z36_card6_cyclotomic_forcing
#print axioms z36_spectral_card6_implies_tile

end Fuglede
