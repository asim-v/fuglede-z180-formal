import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B260UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B260VGroup : List RawSet :=
[
  [0, 3, 9, 15, 21, 30],
  [0, 3, 9, 15, 21, 33],
  [0, 3, 9, 15, 24, 27],
  [0, 3, 9, 15, 24, 30]
]

def z180K30ProjectiveScalarV89D3B260Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 15, 21, 30])
def z180K30ProjectiveScalarV89D3B260Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 15, 21, 33])
def z180K30ProjectiveScalarV89D3B260Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 15, 24, 27])
def z180K30ProjectiveScalarV89D3B260Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 15, 24, 30])

def z180K30ProjectiveScalarV89D3B260Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B260Pair00,
  z180K30ProjectiveScalarV89D3B260Pair01,
  z180K30ProjectiveScalarV89D3B260Pair02,
  z180K30ProjectiveScalarV89D3B260Pair03
]



theorem z180K30ProjectiveScalarV89D3B260Pairs_eq :
    z180K30ProjectiveScalarV89D3B260Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B260UGroup z180K30ProjectiveScalarV89D3B260VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B260Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B260Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B260Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B260Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B260Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B260Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B260Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B260Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B260Audit :
    z180K30ProjectiveScalarV89D3B260Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B260Pairs,
    z180K30ProjectiveScalarV89D3B260Pair00Refuted,
    z180K30ProjectiveScalarV89D3B260Pair01Refuted,
    z180K30ProjectiveScalarV89D3B260Pair02Refuted,
    z180K30ProjectiveScalarV89D3B260Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B260Audit

end Fuglede.Z180K30ExceptionalRawV2
