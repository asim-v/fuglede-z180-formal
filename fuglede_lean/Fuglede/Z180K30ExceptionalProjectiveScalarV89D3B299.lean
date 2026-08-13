import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B299UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B299VGroup : List RawSet :=
[
  [0, 6, 12, 15, 18, 27],
  [0, 6, 12, 15, 18, 30],
  [0, 6, 12, 15, 18, 33],
  [0, 6, 12, 15, 21, 24]
]

def z180K30ProjectiveScalarV89D3B299Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 18, 27])
def z180K30ProjectiveScalarV89D3B299Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 18, 30])
def z180K30ProjectiveScalarV89D3B299Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 18, 33])
def z180K30ProjectiveScalarV89D3B299Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 21, 24])

def z180K30ProjectiveScalarV89D3B299Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B299Pair00,
  z180K30ProjectiveScalarV89D3B299Pair01,
  z180K30ProjectiveScalarV89D3B299Pair02,
  z180K30ProjectiveScalarV89D3B299Pair03
]



theorem z180K30ProjectiveScalarV89D3B299Pairs_eq :
    z180K30ProjectiveScalarV89D3B299Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B299UGroup z180K30ProjectiveScalarV89D3B299VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B299Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B299Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B299Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B299Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B299Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B299Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B299Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B299Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B299Audit :
    z180K30ProjectiveScalarV89D3B299Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B299Pairs,
    z180K30ProjectiveScalarV89D3B299Pair00Refuted,
    z180K30ProjectiveScalarV89D3B299Pair01Refuted,
    z180K30ProjectiveScalarV89D3B299Pair02Refuted,
    z180K30ProjectiveScalarV89D3B299Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B299Audit

end Fuglede.Z180K30ExceptionalRawV2
