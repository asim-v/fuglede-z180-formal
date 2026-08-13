import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B234UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B234VGroup : List RawSet :=
[
  [0, 3, 6, 9, 15, 21],
  [0, 3, 6, 9, 15, 24],
  [0, 3, 6, 9, 15, 27],
  [0, 3, 6, 9, 15, 30]
]

def z180K30ProjectiveScalarV89D3B234Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 15, 21])
def z180K30ProjectiveScalarV89D3B234Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 15, 24])
def z180K30ProjectiveScalarV89D3B234Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 15, 27])
def z180K30ProjectiveScalarV89D3B234Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 15, 30])

def z180K30ProjectiveScalarV89D3B234Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B234Pair00,
  z180K30ProjectiveScalarV89D3B234Pair01,
  z180K30ProjectiveScalarV89D3B234Pair02,
  z180K30ProjectiveScalarV89D3B234Pair03
]



theorem z180K30ProjectiveScalarV89D3B234Pairs_eq :
    z180K30ProjectiveScalarV89D3B234Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B234UGroup z180K30ProjectiveScalarV89D3B234VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B234Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B234Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B234Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B234Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B234Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B234Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B234Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B234Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B234Audit :
    z180K30ProjectiveScalarV89D3B234Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B234Pairs,
    z180K30ProjectiveScalarV89D3B234Pair00Refuted,
    z180K30ProjectiveScalarV89D3B234Pair01Refuted,
    z180K30ProjectiveScalarV89D3B234Pair02Refuted,
    z180K30ProjectiveScalarV89D3B234Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B234Audit

end Fuglede.Z180K30ExceptionalRawV2
