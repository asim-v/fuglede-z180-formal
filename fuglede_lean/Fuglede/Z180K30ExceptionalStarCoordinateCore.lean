import Fuglede.Z180K30ExceptionalHGramWitness

/-!
# Coordinate consequences of an exact five-Gram star

The exact non-H obstruction needs only one or two integral coefficients of
the Gram matrices.  This module isolates the generic extraction from the
raw five-Gram equality.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def gramCoefficient (G : Gram) (entry coefficient : Nat) : Int :=
  (G.getD entry coeffZero).getD coefficient 0

theorem fiveGramStar_gramSum_eq
    (U : Fin 5 -> RawSet) (V : RawSet)
    (hstar : fiveGramStarB U V = true) :
    gramSum (List.ofFn fun i => gram (U i) V) = gramTarget30 := by
  simpa only [fiveGramStarB, Bool.and_eq_true, beq_iff_eq] using hstar

theorem fiveGramStar_gramCoefficient_eq
    (U : Fin 5 -> RawSet) (V : RawSet)
    (entry coefficient : Nat)
    (hstar : fiveGramStarB U V = true) :
    gramCoefficient (gramSum (List.ofFn fun i => gram (U i) V))
        entry coefficient =
      gramCoefficient gramTarget30 entry coefficient := by
  rw [fiveGramStar_gramSum_eq U V hstar]

#print axioms fiveGramStar_gramCoefficient_eq

end Fuglede.Z180K30ExceptionalRawV2
