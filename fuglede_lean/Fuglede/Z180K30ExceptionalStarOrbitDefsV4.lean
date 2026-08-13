import Fuglede.Z180K30ExceptionalStarCandidateObstructionV2

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalOrbitColumnV4 (o : Fin 8) : RawSet :=
  match o with
  | 0 => [0, 1, 12, 18, 24, 30]
  | 1 => [0, 10, 12, 18, 24, 30]
  | 2 => [0, 10, 12, 22, 24, 34]
  | 3 => [0, 12, 15, 18, 24, 30]
  | 4 => [0, 12, 15, 18, 30, 33]
  | 5 => [0, 12, 16, 18, 24, 30]
  | 6 => [0, 12, 18, 21, 24, 30]
  | 7 => [0, 6, 12, 18, 24, 30]

def z180K30ExceptionalOrbitChoicesV4 (o : Fin 8) : List RawSet :=
  match o with
  | 0 => z180K30ExceptionalSixCosets
  | 1 => z180K30ExceptionalSixCosets
  | 2 => z180K30ExceptionalOrbitTwoChoices
  | 3 => z180K30ExceptionalSixCosets
  | 4 => z180K30ExceptionalOrbitFourChoices
  | 5 => z180K30ExceptionalSixCosets
  | 6 => z180K30ExceptionalSixCosets
  | 7 => []

def z180K30FiveGramCoefficientSumV4
    (U : Fin 5 -> RawSet) (V : RawSet)
    (entry coefficient : Nat) : Int :=
  gramCoefficientV2 (gram (U 0) V) entry coefficient +
    gramCoefficientV2 (gram (U 1) V) entry coefficient +
    gramCoefficientV2 (gram (U 2) V) entry coefficient +
    gramCoefficientV2 (gram (U 3) V) entry coefficient +
    gramCoefficientV2 (gram (U 4) V) entry coefficient

def Z180K30ExceptionalOrbitStarCoordinatesV4
    (o : Fin 8) (U : Fin 5 -> RawSet) : Prop :=
  match o with
  | 0 => z180K30FiveGramCoefficientSumV4 U
      (z180K30ExceptionalOrbitColumnV4 0) 3 0 = 0
  | 1 => z180K30FiveGramCoefficientSumV4 U
      (z180K30ExceptionalOrbitColumnV4 1) 3 0 = 0
  | 2 => z180K30FiveGramCoefficientSumV4 U
        (z180K30ExceptionalOrbitColumnV4 2) 2 0 = 0 /\
      z180K30FiveGramCoefficientSumV4 U
        (z180K30ExceptionalOrbitColumnV4 2) 2 6 = 0
  | 3 => z180K30FiveGramCoefficientSumV4 U
      (z180K30ExceptionalOrbitColumnV4 3) 3 0 = 0
  | 4 => z180K30FiveGramCoefficientSumV4 U
      (z180K30ExceptionalOrbitColumnV4 4) 3 0 = 0
  | 5 => z180K30FiveGramCoefficientSumV4 U
      (z180K30ExceptionalOrbitColumnV4 5) 3 0 = 0
  | 6 => z180K30FiveGramCoefficientSumV4 U
      (z180K30ExceptionalOrbitColumnV4 6) 2 0 = 0
  | 7 => True

end Fuglede.Z180K30ExceptionalRawV2
