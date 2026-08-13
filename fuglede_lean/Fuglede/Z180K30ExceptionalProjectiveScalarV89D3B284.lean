import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B284UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B284VGroup : List RawSet :=
[
  [0, 3, 21, 27, 30, 33],
  [0, 3, 24, 27, 30, 33],
  [0, 6, 9, 12, 15, 18],
  [0, 6, 9, 12, 15, 21]
]

def z180K30ProjectiveScalarV89D3B284Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 21, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B284Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 24, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B284Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 15, 18])
def z180K30ProjectiveScalarV89D3B284Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 15, 21])

def z180K30ProjectiveScalarV89D3B284Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B284Pair00,
  z180K30ProjectiveScalarV89D3B284Pair01,
  z180K30ProjectiveScalarV89D3B284Pair02,
  z180K30ProjectiveScalarV89D3B284Pair03
]



theorem z180K30ProjectiveScalarV89D3B284Pairs_eq :
    z180K30ProjectiveScalarV89D3B284Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B284UGroup z180K30ProjectiveScalarV89D3B284VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B284Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B284Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B284Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B284Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B284Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B284Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B284Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B284Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B284Audit :
    z180K30ProjectiveScalarV89D3B284Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B284Pairs,
    z180K30ProjectiveScalarV89D3B284Pair00Refuted,
    z180K30ProjectiveScalarV89D3B284Pair01Refuted,
    z180K30ProjectiveScalarV89D3B284Pair02Refuted,
    z180K30ProjectiveScalarV89D3B284Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B284Audit

end Fuglede.Z180K30ExceptionalRawV2
