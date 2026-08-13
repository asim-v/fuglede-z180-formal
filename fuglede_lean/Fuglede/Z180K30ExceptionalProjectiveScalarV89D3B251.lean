import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B251UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B251VGroup : List RawSet :=
[
  [0, 3, 6, 21, 24, 33],
  [0, 3, 6, 21, 27, 30],
  [0, 3, 6, 21, 27, 33],
  [0, 3, 6, 21, 30, 33]
]

def z180K30ProjectiveScalarV89D3B251Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 21, 24, 33])
def z180K30ProjectiveScalarV89D3B251Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 21, 27, 30])
def z180K30ProjectiveScalarV89D3B251Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 21, 27, 33])
def z180K30ProjectiveScalarV89D3B251Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 21, 30, 33])

def z180K30ProjectiveScalarV89D3B251Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B251Pair00,
  z180K30ProjectiveScalarV89D3B251Pair01,
  z180K30ProjectiveScalarV89D3B251Pair02,
  z180K30ProjectiveScalarV89D3B251Pair03
]



theorem z180K30ProjectiveScalarV89D3B251Pairs_eq :
    z180K30ProjectiveScalarV89D3B251Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B251UGroup z180K30ProjectiveScalarV89D3B251VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B251Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B251Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B251Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B251Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B251Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B251Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B251Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B251Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B251Audit :
    z180K30ProjectiveScalarV89D3B251Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B251Pairs,
    z180K30ProjectiveScalarV89D3B251Pair00Refuted,
    z180K30ProjectiveScalarV89D3B251Pair01Refuted,
    z180K30ProjectiveScalarV89D3B251Pair02Refuted,
    z180K30ProjectiveScalarV89D3B251Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B251Audit

end Fuglede.Z180K30ExceptionalRawV2
