import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B265UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B265VGroup : List RawSet :=
[
  [0, 3, 9, 21, 24, 33],
  [0, 3, 9, 21, 27, 30],
  [0, 3, 9, 21, 27, 33],
  [0, 3, 9, 21, 30, 33]
]

def z180K30ProjectiveScalarV89D3B265Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 21, 24, 33])
def z180K30ProjectiveScalarV89D3B265Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 21, 27, 30])
def z180K30ProjectiveScalarV89D3B265Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 21, 27, 33])
def z180K30ProjectiveScalarV89D3B265Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 21, 30, 33])

def z180K30ProjectiveScalarV89D3B265Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B265Pair00,
  z180K30ProjectiveScalarV89D3B265Pair01,
  z180K30ProjectiveScalarV89D3B265Pair02,
  z180K30ProjectiveScalarV89D3B265Pair03
]



theorem z180K30ProjectiveScalarV89D3B265Pairs_eq :
    z180K30ProjectiveScalarV89D3B265Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B265UGroup z180K30ProjectiveScalarV89D3B265VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B265Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B265Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B265Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B265Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B265Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B265Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B265Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B265Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B265Audit :
    z180K30ProjectiveScalarV89D3B265Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B265Pairs,
    z180K30ProjectiveScalarV89D3B265Pair00Refuted,
    z180K30ProjectiveScalarV89D3B265Pair01Refuted,
    z180K30ProjectiveScalarV89D3B265Pair02Refuted,
    z180K30ProjectiveScalarV89D3B265Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B265Audit

end Fuglede.Z180K30ExceptionalRawV2
