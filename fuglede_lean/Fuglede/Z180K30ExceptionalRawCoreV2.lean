import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Defs
import Mathlib.Tactic

/-!
# Exact raw core V2 for the K30 exceptional certificate

All calculations use Fin 36 and the integral basis 1,z,...,z^11 of
Z[z]/(z^12-z^6+1). No floating point and no native_decide occur here.

This V2 module is the only raw core imported by the certificate DAG.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

abbrev RawPoint := Fin 36
abbrev RawSet := List RawPoint
abbrev Coeff := List Int
abbrev Gram := List Coeff

def coeffZero : Coeff := List.replicate 12 0

def coeffAdd (left right : Coeff) : Coeff :=
  (left.zip right).map fun entry => entry.1 + entry.2

def coeffSum (values : List Coeff) : Coeff :=
  values.foldl coeffAdd coeffZero

def scalarCoeff (value : Int) : Coeff :=
  value :: List.replicate 11 0

def zetaPowerTable : List Coeff :=
  [
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [-1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
    [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    [1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]
  ]

def zetaPower (exponent : Nat) : Coeff :=
  zetaPowerTable.getD (exponent % 36) coeffZero

def rawUniverse : List RawPoint := List.finRange 36

def rawSetEqB (left right : RawSet) : Bool :=
  left.length == right.length &&
    left.all fun point => decide (point ∈ right)

def validSixSetB (set : RawSet) : Bool :=
  set.length == 6 && set.eraseDups.length == 6

def affinePoint (unit translation point : RawPoint) : RawPoint :=
  ⟨(unit.val * point.val + translation.val) % 36, Nat.mod_lt _ (by decide)⟩

def affineSet (unit translation : RawPoint) (set : RawSet) : RawSet :=
  set.map (affinePoint unit translation)

def units36 : List RawPoint := [1, 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35]

def affineEquivalentB (left right : RawSet) : Bool :=
  units36.any fun unit =>
    rawUniverse.any fun translation =>
      rawSetEqB (affineSet unit translation left) right

def orbitRepresentatives : List RawSet :=
  [
    [0, 1, 12, 18, 24, 30],
    [0, 10, 12, 18, 24, 30],
    [0, 10, 12, 22, 24, 34],
    [0, 12, 15, 18, 24, 30],
    [0, 12, 15, 18, 30, 33],
    [0, 12, 16, 18, 24, 30],
    [0, 12, 18, 21, 24, 30],
    [0, 6, 12, 18, 24, 30]
  ]

def orbitCoveredB (set : RawSet) : Bool :=
  orbitRepresentatives.any fun representative =>
    affineEquivalentB representative set

def choose : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | count + 1, head :: tail =>
      (choose count tail).map (head :: ·) ++ choose (count + 1) tail
termination_by _ values => values.length

def natAbsDiff (left right : Nat) : Nat :=
  if left ≤ right then right - left else left - right

def differenceGcd (set : RawSet) : Nat :=
  match set with
  | [] => 36
  | head :: tail =>
      tail.foldl
        (fun result point => Nat.gcd result (natAbsDiff point.val head.val))
        36

def classCount (set : RawSet) (modulus : Nat) : Nat :=
  (set.map fun point => point.val % modulus).eraseDups.length

def rankTwoProjectiveCoverB (U V : RawSet) : Bool :=
  decide (classCount U (36 / differenceGcd V) ≤ 2) ||
    decide (classCount V (36 / differenceGcd U) ≤ 2)

def energy (V : RawSet) (difference : Nat) : Coeff :=
  coeffSum <| V.flatMap fun v =>
    V.map fun w =>
      zetaPower (difference * ((v.val + 36 - w.val) % 36))

def gramTraceSquare (U V : RawSet) : Coeff :=
  coeffSum <| U.flatMap fun u =>
    U.map fun w =>
      energy V ((u.val + 36 - w.val) % 36)

def exceptionalPairB (U V : RawSet) : Bool :=
  validSixSetB U && validSixSetB V &&
    rankTwoProjectiveCoverB U V &&
    gramTraceSquare U V == scalarCoeff 936

def gram (U V : RawSet) : Gram :=
  V.flatMap fun row =>
    V.map fun column =>
      coeffSum <| U.map fun u =>
        zetaPower (u.val * ((column.val + 36 - row.val) % 36))

def gramZero : Gram := List.replicate 36 coeffZero

def gramAdd (left right : Gram) : Gram :=
  (left.zip right).map fun entry => coeffAdd entry.1 entry.2

def gramSum (values : List Gram) : Gram :=
  values.foldl gramAdd gramZero

def gramTarget30 : Gram :=
  (List.range 36).map fun index =>
    if index / 6 = index % 6 then scalarCoeff 30 else coeffZero

def fiveGramStarB (U : Fin 5 → RawSet) (V : RawSet) : Bool :=
  (List.ofFn fun i => exceptionalPairB (U i) V).all id &&
    gramSum (List.ofFn fun i => gram (U i) V) == gramTarget30

def baseForDivisor (divisor : Nat) : List RawPoint :=
  rawUniverse.filter fun point => point.val % divisor == 0

def classForDivisor (divisor residue : Nat) : List RawPoint :=
  rawUniverse.filter fun point => point.val % (36 / divisor) == residue

def classPairsForDivisor (divisor : Nat) : List (List Nat) :=
  choose 2 (List.range (36 / divisor))

def candidatesForVAndPairs
    (divisor : Nat) (V : RawSet) (pairs : List (List Nat)) :
    List (RawSet × RawSet) :=
  pairs.flatMap fun pair =>
    match pair with
    | [first, second] =>
        (choose 6 (classForDivisor divisor first ++
          classForDivisor divisor second)).map fun U => (U, V)
    | _ => []

def projectiveCandidateBatch
    (divisor vStart vCount pairStart pairCount : Nat) :
    List (RawSet × RawSet) :=
  ((choose 6 (baseForDivisor divisor)).drop vStart |>.take vCount).flatMap fun V =>
    candidatesForVAndPairs divisor V
      ((classPairsForDivisor divisor).drop pairStart |>.take pairCount)

structure BatchAudit where
  enumerated : Nat
  accepted : Nat
  uncovered : Nat
deriving DecidableEq, Repr

def auditBatch
    (divisor vStart vCount pairStart pairCount : Nat) : BatchAudit :=
  let candidates :=
    projectiveCandidateBatch divisor vStart vCount pairStart pairCount
  let accepted := candidates.filter fun pair => exceptionalPairB pair.1 pair.2
  {
    enumerated := candidates.length
    accepted := accepted.length
    uncovered := (accepted.filter fun pair =>
      !(orbitCoveredB pair.1 && orbitCoveredB pair.2)).length
  }

def combineAudit (left right : BatchAudit) : BatchAudit :=
  {
    enumerated := left.enumerated + right.enumerated
    accepted := left.accepted + right.accepted
    uncovered := left.uncovered + right.uncovered
  }

def combineAudits (values : List BatchAudit) : BatchAudit :=
  values.foldl combineAudit { enumerated := 0, accepted := 0, uncovered := 0 }

def HCosetB (set : RawSet) : Bool :=
  validSixSetB set &&
    (List.range 6).any fun residue =>
      set.all fun point => point.val % 6 == residue

end Fuglede.Z180K30ExceptionalRawV2

