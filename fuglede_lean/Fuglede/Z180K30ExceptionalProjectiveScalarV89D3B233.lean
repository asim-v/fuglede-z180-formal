import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B233UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B233VGroup : List RawSet :=
[
  [0, 3, 6, 9, 12, 27],
  [0, 3, 6, 9, 12, 30],
  [0, 3, 6, 9, 12, 33],
  [0, 3, 6, 9, 15, 18]
]

def z180K30ProjectiveScalarV89D3B233Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 12, 27])
def z180K30ProjectiveScalarV89D3B233Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 12, 30])
def z180K30ProjectiveScalarV89D3B233Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 12, 33])
def z180K30ProjectiveScalarV89D3B233Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 15, 18])

def z180K30ProjectiveScalarV89D3B233Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B233Pair00,
  z180K30ProjectiveScalarV89D3B233Pair01,
  z180K30ProjectiveScalarV89D3B233Pair02,
  z180K30ProjectiveScalarV89D3B233Pair03
]



theorem z180K30ProjectiveScalarV89D3B233Pairs_eq :
    z180K30ProjectiveScalarV89D3B233Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B233UGroup z180K30ProjectiveScalarV89D3B233VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B233Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B233Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B233Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B233Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B233Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B233Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B233Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B233Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B233Audit :
    z180K30ProjectiveScalarV89D3B233Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B233Pairs,
    z180K30ProjectiveScalarV89D3B233Pair00Refuted,
    z180K30ProjectiveScalarV89D3B233Pair01Refuted,
    z180K30ProjectiveScalarV89D3B233Pair02Refuted,
    z180K30ProjectiveScalarV89D3B233Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B233Audit

end Fuglede.Z180K30ExceptionalRawV2
