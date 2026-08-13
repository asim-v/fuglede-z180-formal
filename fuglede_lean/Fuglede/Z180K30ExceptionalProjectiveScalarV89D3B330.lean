import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B330UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B330VGroup : List RawSet :=
[
  [0, 9, 18, 21, 24, 30],
  [0, 9, 18, 21, 24, 33],
  [0, 9, 18, 21, 27, 30],
  [0, 9, 18, 21, 27, 33]
]

def z180K30ProjectiveScalarV89D3B330Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 18, 21, 24, 30])
def z180K30ProjectiveScalarV89D3B330Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 18, 21, 24, 33])
def z180K30ProjectiveScalarV89D3B330Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 18, 21, 27, 30])
def z180K30ProjectiveScalarV89D3B330Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 18, 21, 27, 33])

def z180K30ProjectiveScalarV89D3B330Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B330Pair00,
  z180K30ProjectiveScalarV89D3B330Pair01,
  z180K30ProjectiveScalarV89D3B330Pair02,
  z180K30ProjectiveScalarV89D3B330Pair03
]



theorem z180K30ProjectiveScalarV89D3B330Pairs_eq :
    z180K30ProjectiveScalarV89D3B330Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B330UGroup z180K30ProjectiveScalarV89D3B330VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B330Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B330Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B330Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B330Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B330Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B330Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B330Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B330Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B330Audit :
    z180K30ProjectiveScalarV89D3B330Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B330Pairs,
    z180K30ProjectiveScalarV89D3B330Pair00Refuted,
    z180K30ProjectiveScalarV89D3B330Pair01Refuted,
    z180K30ProjectiveScalarV89D3B330Pair02Refuted,
    z180K30ProjectiveScalarV89D3B330Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B330Audit

end Fuglede.Z180K30ExceptionalRawV2
