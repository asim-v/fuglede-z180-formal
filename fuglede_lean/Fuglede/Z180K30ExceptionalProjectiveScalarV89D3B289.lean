import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B289UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B289VGroup : List RawSet :=
[
  [0, 6, 9, 12, 27, 30],
  [0, 6, 9, 12, 27, 33],
  [0, 6, 9, 12, 30, 33],
  [0, 6, 9, 15, 18, 21]
]

def z180K30ProjectiveScalarV89D3B289Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 27, 30])
def z180K30ProjectiveScalarV89D3B289Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 27, 33])
def z180K30ProjectiveScalarV89D3B289Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 30, 33])
def z180K30ProjectiveScalarV89D3B289Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 15, 18, 21])

def z180K30ProjectiveScalarV89D3B289Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B289Pair00,
  z180K30ProjectiveScalarV89D3B289Pair01,
  z180K30ProjectiveScalarV89D3B289Pair02,
  z180K30ProjectiveScalarV89D3B289Pair03
]



theorem z180K30ProjectiveScalarV89D3B289Pairs_eq :
    z180K30ProjectiveScalarV89D3B289Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B289UGroup z180K30ProjectiveScalarV89D3B289VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B289Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B289Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B289Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B289Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B289Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B289Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B289Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B289Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B289Audit :
    z180K30ProjectiveScalarV89D3B289Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B289Pairs,
    z180K30ProjectiveScalarV89D3B289Pair00Refuted,
    z180K30ProjectiveScalarV89D3B289Pair01Refuted,
    z180K30ProjectiveScalarV89D3B289Pair02Refuted,
    z180K30ProjectiveScalarV89D3B289Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B289Audit

end Fuglede.Z180K30ExceptionalRawV2
