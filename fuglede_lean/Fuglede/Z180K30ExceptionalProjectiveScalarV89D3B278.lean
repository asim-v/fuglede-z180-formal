import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B278UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B278VGroup : List RawSet :=
[
  [0, 3, 15, 18, 30, 33],
  [0, 3, 15, 21, 24, 27],
  [0, 3, 15, 21, 24, 30],
  [0, 3, 15, 21, 24, 33]
]

def z180K30ProjectiveScalarV89D3B278Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 15, 18, 30, 33])
def z180K30ProjectiveScalarV89D3B278Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 15, 21, 24, 27])
def z180K30ProjectiveScalarV89D3B278Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 15, 21, 24, 30])
def z180K30ProjectiveScalarV89D3B278Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 15, 21, 24, 33])

def z180K30ProjectiveScalarV89D3B278Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B278Pair00,
  z180K30ProjectiveScalarV89D3B278Pair01,
  z180K30ProjectiveScalarV89D3B278Pair02,
  z180K30ProjectiveScalarV89D3B278Pair03
]



theorem z180K30ProjectiveScalarV89D3B278Pairs_eq :
    z180K30ProjectiveScalarV89D3B278Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B278UGroup z180K30ProjectiveScalarV89D3B278VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B278Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B278Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B278Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B278Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B278Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B278Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B278Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B278Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B278Audit :
    z180K30ProjectiveScalarV89D3B278Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B278Pairs,
    z180K30ProjectiveScalarV89D3B278Pair00Refuted,
    z180K30ProjectiveScalarV89D3B278Pair01Refuted,
    z180K30ProjectiveScalarV89D3B278Pair02Refuted,
    z180K30ProjectiveScalarV89D3B278Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B278Audit

end Fuglede.Z180K30ExceptionalRawV2
