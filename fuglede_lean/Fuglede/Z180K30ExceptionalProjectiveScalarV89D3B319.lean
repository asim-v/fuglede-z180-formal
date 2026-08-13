import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B319UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B319VGroup : List RawSet :=
[
  [0, 9, 12, 15, 27, 30],
  [0, 9, 12, 15, 27, 33],
  [0, 9, 12, 15, 30, 33],
  [0, 9, 12, 18, 21, 24]
]

def z180K30ProjectiveScalarV89D3B319Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 27, 30])
def z180K30ProjectiveScalarV89D3B319Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 27, 33])
def z180K30ProjectiveScalarV89D3B319Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 30, 33])
def z180K30ProjectiveScalarV89D3B319Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 18, 21, 24])

def z180K30ProjectiveScalarV89D3B319Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B319Pair00,
  z180K30ProjectiveScalarV89D3B319Pair01,
  z180K30ProjectiveScalarV89D3B319Pair02,
  z180K30ProjectiveScalarV89D3B319Pair03
]



theorem z180K30ProjectiveScalarV89D3B319Pairs_eq :
    z180K30ProjectiveScalarV89D3B319Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B319UGroup z180K30ProjectiveScalarV89D3B319VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B319Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B319Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B319Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B319Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B319Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B319Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B319Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B319Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B319Audit :
    z180K30ProjectiveScalarV89D3B319Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B319Pairs,
    z180K30ProjectiveScalarV89D3B319Pair00Refuted,
    z180K30ProjectiveScalarV89D3B319Pair01Refuted,
    z180K30ProjectiveScalarV89D3B319Pair02Refuted,
    z180K30ProjectiveScalarV89D3B319Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B319Audit

end Fuglede.Z180K30ExceptionalRawV2
