import Fuglede.Z180K30ExceptionalOrbitSignatureAuditV78

/-!
# Literal signature table for the coupled K30 orbit audit (V78)

The expensive 432-image Boolean leaves are not imported here.  Translation
does not affect a row Gram matrix, so the useful finite payload is the
12-unit table below.  Each row records the exact signature of the normalized
affine image with translation zero; a separate covariance lemma can transport
it to arbitrary translations without re-evaluating 36 copies.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30OrbitUnitImagesV78 (r : Fin 8) : List RawSet :=
  units36.map fun unit =>
    affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r)

def z180K30OrbitUnitSignatureTableV78
    (o r : Fin 8) : List (List Int) :=
  (z180K30OrbitUnitImagesV78 r).map (z180K30StarSignatureV78 o)

def z180K30ExpectedUnitSignatureTableV78 (o r : Fin 8) : List (List Int) :=
  match o, r with
  | 0, 7 => [[6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6]]
  | 1, 7 => [[6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6]]
  | 2, 4 =>
      [[6, 0], [0, -6], [-6, 6], [6, 0], [0, -6], [-6, 6],
       [6, 0], [0, -6], [-6, 6], [6, 0], [0, -6], [-6, 6]]
  | 3, 7 => [[6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6]]
  | 4, 2 => [[6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6]]
  | 5, 7 => [[6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6]]
  | 6, 7 => [[6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6], [6], [-6]]
  | _, _ => []

/-- The seven possible nonempty `(column orbit, row orbit)` pairs. -/
def z180K30CompatibleOrbitPairBV78 (o r : Fin 8) : Bool :=
  (o == 0 && r == 7) ||
  (o == 1 && r == 7) ||
  (o == 2 && r == 4) ||
  (o == 3 && r == 7) ||
  (o == 4 && r == 2) ||
  (o == 5 && r == 7) ||
  (o == 6 && r == 7)

end Fuglede.Z180K30ExceptionalRawV2
