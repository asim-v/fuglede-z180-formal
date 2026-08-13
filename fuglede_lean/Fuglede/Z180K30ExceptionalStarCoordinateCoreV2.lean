import Fuglede.Z180K30ExceptionalHGramWitness

/-!
# Coordinate consequences of an exact five-Gram star (V2)
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def gramCoefficientV2 (G : Gram) (entry coefficient : Nat) : Int :=
  (G.getD entry coeffZero).getD coefficient 0

theorem fiveGramStar_gramSum_eq_v2
    (U : Fin 5 -> RawSet) (V : RawSet)
    (hstar : fiveGramStarB U V = true) :
    gramSum (List.ofFn fun i => gram (U i) V) = gramTarget30 := by
  have h := hstar
  simp only [fiveGramStarB, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem fiveGramStar_gramCoefficient_eq_v2
    (U : Fin 5 -> RawSet) (V : RawSet)
    (entry coefficient : Nat)
    (hstar : fiveGramStarB U V = true) :
    gramCoefficientV2 (gramSum (List.ofFn fun i => gram (U i) V))
        entry coefficient =
      gramCoefficientV2 gramTarget30 entry coefficient := by
  rw [fiveGramStar_gramSum_eq_v2 U V hstar]

#print axioms fiveGramStar_gramCoefficient_eq_v2

end Fuglede.Z180K30ExceptionalRawV2
