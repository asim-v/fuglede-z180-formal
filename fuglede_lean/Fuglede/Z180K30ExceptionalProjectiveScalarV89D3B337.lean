import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B337UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B337VGroup : List RawSet :=
[
  [0, 12, 15, 21, 27, 33],
  [0, 12, 15, 21, 30, 33],
  [0, 12, 15, 24, 27, 30],
  [0, 12, 15, 24, 27, 33]
]

def z180K30ProjectiveScalarV89D3B337Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 21, 27, 33])
def z180K30ProjectiveScalarV89D3B337Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 21, 30, 33])
def z180K30ProjectiveScalarV89D3B337Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 24, 27, 30])
def z180K30ProjectiveScalarV89D3B337Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 24, 27, 33])

def z180K30ProjectiveScalarV89D3B337Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B337Pair00,
  z180K30ProjectiveScalarV89D3B337Pair01,
  z180K30ProjectiveScalarV89D3B337Pair02,
  z180K30ProjectiveScalarV89D3B337Pair03
]



theorem z180K30ProjectiveScalarV89D3B337Pairs_eq :
    z180K30ProjectiveScalarV89D3B337Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B337UGroup z180K30ProjectiveScalarV89D3B337VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B337Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B337Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B337Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B337Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B337Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B337Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B337Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B337Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B337Audit :
    z180K30ProjectiveScalarV89D3B337Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B337Pairs,
    z180K30ProjectiveScalarV89D3B337Pair00Refuted,
    z180K30ProjectiveScalarV89D3B337Pair01Refuted,
    z180K30ProjectiveScalarV89D3B337Pair02Refuted,
    z180K30ProjectiveScalarV89D3B337Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B337Audit

end Fuglede.Z180K30ExceptionalRawV2
