import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B328UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B328VGroup : List RawSet :=
[
  [0, 9, 15, 21, 27, 30],
  [0, 9, 15, 21, 27, 33],
  [0, 9, 15, 21, 30, 33],
  [0, 9, 15, 24, 27, 30]
]

def z180K30ProjectiveScalarV89D3B328Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 21, 27, 30])
def z180K30ProjectiveScalarV89D3B328Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 21, 27, 33])
def z180K30ProjectiveScalarV89D3B328Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 21, 30, 33])
def z180K30ProjectiveScalarV89D3B328Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 24, 27, 30])

def z180K30ProjectiveScalarV89D3B328Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B328Pair00,
  z180K30ProjectiveScalarV89D3B328Pair01,
  z180K30ProjectiveScalarV89D3B328Pair02,
  z180K30ProjectiveScalarV89D3B328Pair03
]



theorem z180K30ProjectiveScalarV89D3B328Pairs_eq :
    z180K30ProjectiveScalarV89D3B328Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B328UGroup z180K30ProjectiveScalarV89D3B328VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B328Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B328Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B328Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B328Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B328Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B328Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B328Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B328Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B328Audit :
    z180K30ProjectiveScalarV89D3B328Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B328Pairs,
    z180K30ProjectiveScalarV89D3B328Pair00Refuted,
    z180K30ProjectiveScalarV89D3B328Pair01Refuted,
    z180K30ProjectiveScalarV89D3B328Pair02Refuted,
    z180K30ProjectiveScalarV89D3B328Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B328Audit

end Fuglede.Z180K30ExceptionalRawV2
