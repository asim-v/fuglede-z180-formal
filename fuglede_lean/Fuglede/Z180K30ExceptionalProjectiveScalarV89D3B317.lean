import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B317UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B317VGroup : List RawSet :=
[
  [0, 9, 12, 15, 18, 33],
  [0, 9, 12, 15, 21, 24],
  [0, 9, 12, 15, 21, 27],
  [0, 9, 12, 15, 21, 30]
]

def z180K30ProjectiveScalarV89D3B317Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 18, 33])
def z180K30ProjectiveScalarV89D3B317Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 21, 24])
def z180K30ProjectiveScalarV89D3B317Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 21, 27])
def z180K30ProjectiveScalarV89D3B317Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 21, 30])

def z180K30ProjectiveScalarV89D3B317Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B317Pair00,
  z180K30ProjectiveScalarV89D3B317Pair01,
  z180K30ProjectiveScalarV89D3B317Pair02,
  z180K30ProjectiveScalarV89D3B317Pair03
]



theorem z180K30ProjectiveScalarV89D3B317Pairs_eq :
    z180K30ProjectiveScalarV89D3B317Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B317UGroup z180K30ProjectiveScalarV89D3B317VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B317Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B317Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B317Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B317Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B317Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B317Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B317Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B317Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B317Audit :
    z180K30ProjectiveScalarV89D3B317Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B317Pairs,
    z180K30ProjectiveScalarV89D3B317Pair00Refuted,
    z180K30ProjectiveScalarV89D3B317Pair01Refuted,
    z180K30ProjectiveScalarV89D3B317Pair02Refuted,
    z180K30ProjectiveScalarV89D3B317Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B317Audit

end Fuglede.Z180K30ExceptionalRawV2
