import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B310UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B310VGroup : List RawSet :=
[
  [0, 6, 15, 21, 24, 30],
  [0, 6, 15, 21, 24, 33],
  [0, 6, 15, 21, 27, 30],
  [0, 6, 15, 21, 27, 33]
]

def z180K30ProjectiveScalarV89D3B310Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 15, 21, 24, 30])
def z180K30ProjectiveScalarV89D3B310Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 15, 21, 24, 33])
def z180K30ProjectiveScalarV89D3B310Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 15, 21, 27, 30])
def z180K30ProjectiveScalarV89D3B310Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 15, 21, 27, 33])

def z180K30ProjectiveScalarV89D3B310Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B310Pair00,
  z180K30ProjectiveScalarV89D3B310Pair01,
  z180K30ProjectiveScalarV89D3B310Pair02,
  z180K30ProjectiveScalarV89D3B310Pair03
]



theorem z180K30ProjectiveScalarV89D3B310Pairs_eq :
    z180K30ProjectiveScalarV89D3B310Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B310UGroup z180K30ProjectiveScalarV89D3B310VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B310Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B310Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B310Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B310Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B310Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B310Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B310Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B310Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B310Audit :
    z180K30ProjectiveScalarV89D3B310Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B310Pairs,
    z180K30ProjectiveScalarV89D3B310Pair00Refuted,
    z180K30ProjectiveScalarV89D3B310Pair01Refuted,
    z180K30ProjectiveScalarV89D3B310Pair02Refuted,
    z180K30ProjectiveScalarV89D3B310Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B310Audit

end Fuglede.Z180K30ExceptionalRawV2
