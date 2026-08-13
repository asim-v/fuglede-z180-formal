import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B339UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B339VGroup : List RawSet :=
[
  [0, 12, 18, 21, 24, 33],
  [0, 12, 18, 21, 27, 30],
  [0, 12, 18, 21, 27, 33],
  [0, 12, 18, 21, 30, 33]
]

def z180K30ProjectiveScalarV89D3B339Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 18, 21, 24, 33])
def z180K30ProjectiveScalarV89D3B339Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 18, 21, 27, 30])
def z180K30ProjectiveScalarV89D3B339Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 18, 21, 27, 33])
def z180K30ProjectiveScalarV89D3B339Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 18, 21, 30, 33])

def z180K30ProjectiveScalarV89D3B339Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B339Pair00,
  z180K30ProjectiveScalarV89D3B339Pair01,
  z180K30ProjectiveScalarV89D3B339Pair02,
  z180K30ProjectiveScalarV89D3B339Pair03
]



theorem z180K30ProjectiveScalarV89D3B339Pairs_eq :
    z180K30ProjectiveScalarV89D3B339Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B339UGroup z180K30ProjectiveScalarV89D3B339VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B339Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B339Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B339Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B339Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B339Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B339Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B339Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B339Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B339Audit :
    z180K30ProjectiveScalarV89D3B339Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B339Pairs,
    z180K30ProjectiveScalarV89D3B339Pair00Refuted,
    z180K30ProjectiveScalarV89D3B339Pair01Refuted,
    z180K30ProjectiveScalarV89D3B339Pair02Refuted,
    z180K30ProjectiveScalarV89D3B339Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B339Audit

end Fuglede.Z180K30ExceptionalRawV2
