import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B275UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B275VGroup : List RawSet :=
[
  [0, 3, 12, 24, 27, 33],
  [0, 3, 12, 24, 30, 33],
  [0, 3, 12, 27, 30, 33],
  [0, 3, 15, 18, 21, 24]
]

def z180K30ProjectiveScalarV89D3B275Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 24, 27, 33])
def z180K30ProjectiveScalarV89D3B275Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 24, 30, 33])
def z180K30ProjectiveScalarV89D3B275Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B275Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 15, 18, 21, 24])

def z180K30ProjectiveScalarV89D3B275Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B275Pair00,
  z180K30ProjectiveScalarV89D3B275Pair01,
  z180K30ProjectiveScalarV89D3B275Pair02,
  z180K30ProjectiveScalarV89D3B275Pair03
]



theorem z180K30ProjectiveScalarV89D3B275Pairs_eq :
    z180K30ProjectiveScalarV89D3B275Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B275UGroup z180K30ProjectiveScalarV89D3B275VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B275Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B275Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B275Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B275Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B275Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B275Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B275Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B275Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B275Audit :
    z180K30ProjectiveScalarV89D3B275Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B275Pairs,
    z180K30ProjectiveScalarV89D3B275Pair00Refuted,
    z180K30ProjectiveScalarV89D3B275Pair01Refuted,
    z180K30ProjectiveScalarV89D3B275Pair02Refuted,
    z180K30ProjectiveScalarV89D3B275Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B275Audit

end Fuglede.Z180K30ExceptionalRawV2
