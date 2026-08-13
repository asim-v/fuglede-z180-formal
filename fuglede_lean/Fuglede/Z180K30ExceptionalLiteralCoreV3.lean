import Fuglede.Z180K30ExceptionalRawCoreV2

namespace Fuglede.Z180K30ExceptionalRawV2

/--
The source-only certificate leaves pass literal pairs to this module.  In
particular, evaluating one leaf never rebuilds or drops a prefix of the global
159516-pair enumeration.
-/
def rawAffinePoint (a b : Nat) (x : RawPoint) : RawPoint :=
  ⟨(a * x.val + b) % 36, Nat.mod_lt _ (by decide)⟩

def rawAffineSet (a b : Nat) (X : RawSet) : RawSet :=
  X.map (rawAffinePoint a b)

def sameRawSetB (X Y : RawSet) : Bool :=
  X.length == Y.length && X.all fun x => Y.contains x

def rawUnits36 : List Nat :=
  [1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35]

def exceptionalOrbitReps : List RawSet :=
  [ [0, 1, 12, 18, 24, 30],
    [0, 10, 12, 18, 24, 30],
    [0, 10, 12, 22, 24, 34],
    [0, 12, 15, 18, 24, 30],
    [0, 12, 15, 18, 30, 33],
    [0, 12, 16, 18, 24, 30],
    [0, 12, 18, 21, 24, 30],
    [0, 6, 12, 18, 24, 30] ]

def rawAffineOrbitB (X R : RawSet) : Bool :=
  rawUnits36.any fun a =>
    (List.range 36).any fun b =>
      sameRawSetB (rawAffineSet a b X) R

def coveredByExceptionalOrbitsB (X : RawSet) : Bool :=
  exceptionalOrbitReps.any fun R => rawAffineOrbitB X R

def literalPairCoveredB (p : RawSet × RawSet) : Bool :=
  coveredByExceptionalOrbitsB p.1 && coveredByExceptionalOrbitsB p.2

def auditLiteralPairs (pairs : List (RawSet × RawSet)) : BatchAudit :=
  let acceptedPairs := pairs.filter fun p => exceptionalPairB p.1 p.2
  let uncoveredPairs := acceptedPairs.filter fun p => !literalPairCoveredB p
  { enumerated := pairs.length
    accepted := acceptedPairs.length
    uncovered := uncoveredPairs.length }

end Fuglede.Z180K30ExceptionalRawV2

