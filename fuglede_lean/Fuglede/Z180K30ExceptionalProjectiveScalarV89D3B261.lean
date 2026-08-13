import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B261UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B261VGroup : List RawSet :=
[
  [0, 3, 9, 15, 24, 33],
  [0, 3, 9, 15, 27, 30],
  [0, 3, 9, 15, 27, 33],
  [0, 3, 9, 15, 30, 33]
]

def z180K30ProjectiveScalarV89D3B261Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 15, 24, 33])
def z180K30ProjectiveScalarV89D3B261Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 15, 27, 30])
def z180K30ProjectiveScalarV89D3B261Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 15, 27, 33])
def z180K30ProjectiveScalarV89D3B261Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 15, 30, 33])

def z180K30ProjectiveScalarV89D3B261Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B261Pair00,
  z180K30ProjectiveScalarV89D3B261Pair01,
  z180K30ProjectiveScalarV89D3B261Pair02,
  z180K30ProjectiveScalarV89D3B261Pair03
]



theorem z180K30ProjectiveScalarV89D3B261Pairs_eq :
    z180K30ProjectiveScalarV89D3B261Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B261UGroup z180K30ProjectiveScalarV89D3B261VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B261Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B261Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B261Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B261Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B261Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B261Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B261Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B261Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B261Audit :
    z180K30ProjectiveScalarV89D3B261Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B261Pairs,
    z180K30ProjectiveScalarV89D3B261Pair00Refuted,
    z180K30ProjectiveScalarV89D3B261Pair01Refuted,
    z180K30ProjectiveScalarV89D3B261Pair02Refuted,
    z180K30ProjectiveScalarV89D3B261Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B261Audit

end Fuglede.Z180K30ExceptionalRawV2
