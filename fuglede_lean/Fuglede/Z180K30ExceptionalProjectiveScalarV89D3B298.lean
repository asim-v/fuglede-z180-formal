import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B298UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B298VGroup : List RawSet :=
[
  [0, 6, 9, 24, 30, 33],
  [0, 6, 9, 27, 30, 33],
  [0, 6, 12, 15, 18, 21],
  [0, 6, 12, 15, 18, 24]
]

def z180K30ProjectiveScalarV89D3B298Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 24, 30, 33])
def z180K30ProjectiveScalarV89D3B298Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B298Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 18, 21])
def z180K30ProjectiveScalarV89D3B298Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 18, 24])

def z180K30ProjectiveScalarV89D3B298Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B298Pair00,
  z180K30ProjectiveScalarV89D3B298Pair01,
  z180K30ProjectiveScalarV89D3B298Pair02,
  z180K30ProjectiveScalarV89D3B298Pair03
]



theorem z180K30ProjectiveScalarV89D3B298Pairs_eq :
    z180K30ProjectiveScalarV89D3B298Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B298UGroup z180K30ProjectiveScalarV89D3B298VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B298Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B298Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B298Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B298Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B298Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B298Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B298Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B298Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B298Audit :
    z180K30ProjectiveScalarV89D3B298Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B298Pairs,
    z180K30ProjectiveScalarV89D3B298Pair00Refuted,
    z180K30ProjectiveScalarV89D3B298Pair01Refuted,
    z180K30ProjectiveScalarV89D3B298Pair02Refuted,
    z180K30ProjectiveScalarV89D3B298Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B298Audit

end Fuglede.Z180K30ExceptionalRawV2
