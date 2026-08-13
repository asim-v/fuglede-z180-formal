import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B301UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B301VGroup : List RawSet :=
[
  [0, 6, 12, 15, 24, 30],
  [0, 6, 12, 15, 24, 33],
  [0, 6, 12, 15, 27, 30],
  [0, 6, 12, 15, 27, 33]
]

def z180K30ProjectiveScalarV89D3B301Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 24, 30])
def z180K30ProjectiveScalarV89D3B301Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 24, 33])
def z180K30ProjectiveScalarV89D3B301Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 27, 30])
def z180K30ProjectiveScalarV89D3B301Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 15, 27, 33])

def z180K30ProjectiveScalarV89D3B301Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B301Pair00,
  z180K30ProjectiveScalarV89D3B301Pair01,
  z180K30ProjectiveScalarV89D3B301Pair02,
  z180K30ProjectiveScalarV89D3B301Pair03
]



theorem z180K30ProjectiveScalarV89D3B301Pairs_eq :
    z180K30ProjectiveScalarV89D3B301Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B301UGroup z180K30ProjectiveScalarV89D3B301VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B301Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B301Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B301Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B301Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B301Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B301Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B301Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B301Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B301Audit :
    z180K30ProjectiveScalarV89D3B301Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B301Pairs,
    z180K30ProjectiveScalarV89D3B301Pair00Refuted,
    z180K30ProjectiveScalarV89D3B301Pair01Refuted,
    z180K30ProjectiveScalarV89D3B301Pair02Refuted,
    z180K30ProjectiveScalarV89D3B301Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B301Audit

end Fuglede.Z180K30ExceptionalRawV2
