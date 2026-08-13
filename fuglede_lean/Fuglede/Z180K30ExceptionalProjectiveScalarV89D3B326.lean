import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B326UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B326VGroup : List RawSet :=
[
  [0, 9, 15, 18, 24, 30],
  [0, 9, 15, 18, 24, 33],
  [0, 9, 15, 18, 27, 30],
  [0, 9, 15, 18, 27, 33]
]

def z180K30ProjectiveScalarV89D3B326Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 18, 24, 30])
def z180K30ProjectiveScalarV89D3B326Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 18, 24, 33])
def z180K30ProjectiveScalarV89D3B326Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 18, 27, 30])
def z180K30ProjectiveScalarV89D3B326Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 18, 27, 33])

def z180K30ProjectiveScalarV89D3B326Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B326Pair00,
  z180K30ProjectiveScalarV89D3B326Pair01,
  z180K30ProjectiveScalarV89D3B326Pair02,
  z180K30ProjectiveScalarV89D3B326Pair03
]



theorem z180K30ProjectiveScalarV89D3B326Pairs_eq :
    z180K30ProjectiveScalarV89D3B326Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B326UGroup z180K30ProjectiveScalarV89D3B326VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B326Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B326Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B326Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B326Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B326Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B326Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B326Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B326Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B326Audit :
    z180K30ProjectiveScalarV89D3B326Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B326Pairs,
    z180K30ProjectiveScalarV89D3B326Pair00Refuted,
    z180K30ProjectiveScalarV89D3B326Pair01Refuted,
    z180K30ProjectiveScalarV89D3B326Pair02Refuted,
    z180K30ProjectiveScalarV89D3B326Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B326Audit

end Fuglede.Z180K30ExceptionalRawV2
