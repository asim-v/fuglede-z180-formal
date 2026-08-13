import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B250UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B250VGroup : List RawSet :=
[
  [0, 3, 6, 18, 27, 33],
  [0, 3, 6, 18, 30, 33],
  [0, 3, 6, 21, 24, 27],
  [0, 3, 6, 21, 24, 30]
]

def z180K30ProjectiveScalarV89D3B250Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 27, 33])
def z180K30ProjectiveScalarV89D3B250Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 30, 33])
def z180K30ProjectiveScalarV89D3B250Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 21, 24, 27])
def z180K30ProjectiveScalarV89D3B250Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 21, 24, 30])

def z180K30ProjectiveScalarV89D3B250Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B250Pair00,
  z180K30ProjectiveScalarV89D3B250Pair01,
  z180K30ProjectiveScalarV89D3B250Pair02,
  z180K30ProjectiveScalarV89D3B250Pair03
]



theorem z180K30ProjectiveScalarV89D3B250Pairs_eq :
    z180K30ProjectiveScalarV89D3B250Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B250UGroup z180K30ProjectiveScalarV89D3B250VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B250Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B250Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B250Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B250Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B250Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B250Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B250Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B250Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B250Audit :
    z180K30ProjectiveScalarV89D3B250Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B250Pairs,
    z180K30ProjectiveScalarV89D3B250Pair00Refuted,
    z180K30ProjectiveScalarV89D3B250Pair01Refuted,
    z180K30ProjectiveScalarV89D3B250Pair02Refuted,
    z180K30ProjectiveScalarV89D3B250Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B250Audit

end Fuglede.Z180K30ExceptionalRawV2
