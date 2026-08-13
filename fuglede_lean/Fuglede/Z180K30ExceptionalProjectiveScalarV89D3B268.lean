import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B268UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B268VGroup : List RawSet :=
[
  [0, 3, 12, 15, 18, 33],
  [0, 3, 12, 15, 21, 24],
  [0, 3, 12, 15, 21, 27],
  [0, 3, 12, 15, 21, 30]
]

def z180K30ProjectiveScalarV89D3B268Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 15, 18, 33])
def z180K30ProjectiveScalarV89D3B268Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 15, 21, 24])
def z180K30ProjectiveScalarV89D3B268Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 15, 21, 27])
def z180K30ProjectiveScalarV89D3B268Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 15, 21, 30])

def z180K30ProjectiveScalarV89D3B268Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B268Pair00,
  z180K30ProjectiveScalarV89D3B268Pair01,
  z180K30ProjectiveScalarV89D3B268Pair02,
  z180K30ProjectiveScalarV89D3B268Pair03
]



theorem z180K30ProjectiveScalarV89D3B268Pairs_eq :
    z180K30ProjectiveScalarV89D3B268Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B268UGroup z180K30ProjectiveScalarV89D3B268VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B268Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B268Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B268Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B268Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B268Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B268Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B268Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B268Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B268Audit :
    z180K30ProjectiveScalarV89D3B268Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B268Pairs,
    z180K30ProjectiveScalarV89D3B268Pair00Refuted,
    z180K30ProjectiveScalarV89D3B268Pair01Refuted,
    z180K30ProjectiveScalarV89D3B268Pair02Refuted,
    z180K30ProjectiveScalarV89D3B268Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B268Audit

end Fuglede.Z180K30ExceptionalRawV2
