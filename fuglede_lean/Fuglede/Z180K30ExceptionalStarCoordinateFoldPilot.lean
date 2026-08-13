import Fuglede.Z180K30ExceptionalStarCoordinateCoreV2

namespace Fuglede.Z180K30ExceptionalRawV2

theorem fiveGramStar_orbitZero_entry_three_sum_zero
    (U : Fin 5 -> RawSet)
    (hstar : fiveGramStarB U [0, 1, 12, 18, 24, 30] = true) :
    (Finset.univ.sum fun i =>
      gramCoefficientV2 (gram (U i) [0, 1, 12, 18, 24, 30]) 3 0) = 0 := by
  have h := fiveGramStar_gramCoefficient_eq_v2 U
    [0, 1, 12, 18, 24, 30] 3 0 hstar
  simpa [gramCoefficientV2, gramSum, gramAdd, gramZero, coeffAdd,
    coeffZero, gramTarget30, List.ofFn] using h

#print axioms fiveGramStar_orbitZero_entry_three_sum_zero

end Fuglede.Z180K30ExceptionalRawV2
