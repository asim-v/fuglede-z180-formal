import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B304UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B304VGroup : List RawSet :=
[
  [0, 6, 12, 18, 27, 30],
  [0, 6, 12, 18, 27, 33],
  [0, 6, 12, 18, 30, 33],
  [0, 6, 12, 21, 24, 27]
]

def z180K30ProjectiveScalarV89D3B304Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 18, 27, 30])
def z180K30ProjectiveScalarV89D3B304Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 18, 27, 33])
def z180K30ProjectiveScalarV89D3B304Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 18, 30, 33])
def z180K30ProjectiveScalarV89D3B304Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 21, 24, 27])

def z180K30ProjectiveScalarV89D3B304Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B304Pair00,
  z180K30ProjectiveScalarV89D3B304Pair01,
  z180K30ProjectiveScalarV89D3B304Pair02,
  z180K30ProjectiveScalarV89D3B304Pair03
]



theorem z180K30ProjectiveScalarV89D3B304Pairs_eq :
    z180K30ProjectiveScalarV89D3B304Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B304UGroup z180K30ProjectiveScalarV89D3B304VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B304Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B304Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B304Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B304Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B304Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B304Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B304Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B304Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B304Audit :
    z180K30ProjectiveScalarV89D3B304Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B304Pairs,
    z180K30ProjectiveScalarV89D3B304Pair00Refuted,
    z180K30ProjectiveScalarV89D3B304Pair01Refuted,
    z180K30ProjectiveScalarV89D3B304Pair02Refuted,
    z180K30ProjectiveScalarV89D3B304Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B304Audit

end Fuglede.Z180K30ExceptionalRawV2
