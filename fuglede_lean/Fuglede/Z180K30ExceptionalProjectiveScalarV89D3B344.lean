import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B344UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B344VGroup : List RawSet :=
[
  [0, 15, 18, 24, 27, 33],
  [0, 15, 18, 24, 30, 33],
  [0, 15, 18, 27, 30, 33],
  [0, 15, 21, 24, 27, 30]
]

def z180K30ProjectiveScalarV89D3B344Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 18, 24, 27, 33])
def z180K30ProjectiveScalarV89D3B344Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 18, 24, 30, 33])
def z180K30ProjectiveScalarV89D3B344Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 18, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B344Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 21, 24, 27, 30])

def z180K30ProjectiveScalarV89D3B344Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B344Pair00,
  z180K30ProjectiveScalarV89D3B344Pair01,
  z180K30ProjectiveScalarV89D3B344Pair02,
  z180K30ProjectiveScalarV89D3B344Pair03
]



theorem z180K30ProjectiveScalarV89D3B344Pairs_eq :
    z180K30ProjectiveScalarV89D3B344Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B344UGroup z180K30ProjectiveScalarV89D3B344VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B344Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B344Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B344Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B344Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B344Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B344Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B344Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B344Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B344Audit :
    z180K30ProjectiveScalarV89D3B344Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B344Pairs,
    z180K30ProjectiveScalarV89D3B344Pair00Refuted,
    z180K30ProjectiveScalarV89D3B344Pair01Refuted,
    z180K30ProjectiveScalarV89D3B344Pair02Refuted,
    z180K30ProjectiveScalarV89D3B344Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B344Audit

end Fuglede.Z180K30ExceptionalRawV2
