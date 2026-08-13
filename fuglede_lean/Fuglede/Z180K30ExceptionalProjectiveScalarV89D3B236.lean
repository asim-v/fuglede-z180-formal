import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B236UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B236VGroup : List RawSet :=
[
  [0, 3, 6, 9, 18, 30],
  [0, 3, 6, 9, 18, 33],
  [0, 3, 6, 9, 21, 24],
  [0, 3, 6, 9, 21, 27]
]

def z180K30ProjectiveScalarV89D3B236Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 18, 30])
def z180K30ProjectiveScalarV89D3B236Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 18, 33])
def z180K30ProjectiveScalarV89D3B236Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 21, 24])
def z180K30ProjectiveScalarV89D3B236Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 21, 27])

def z180K30ProjectiveScalarV89D3B236Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B236Pair00,
  z180K30ProjectiveScalarV89D3B236Pair01,
  z180K30ProjectiveScalarV89D3B236Pair02,
  z180K30ProjectiveScalarV89D3B236Pair03
]



theorem z180K30ProjectiveScalarV89D3B236Pairs_eq :
    z180K30ProjectiveScalarV89D3B236Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B236UGroup z180K30ProjectiveScalarV89D3B236VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B236Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B236Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B236Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B236Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B236Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B236Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B236Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B236Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B236Audit :
    z180K30ProjectiveScalarV89D3B236Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B236Pairs,
    z180K30ProjectiveScalarV89D3B236Pair00Refuted,
    z180K30ProjectiveScalarV89D3B236Pair01Refuted,
    z180K30ProjectiveScalarV89D3B236Pair02Refuted,
    z180K30ProjectiveScalarV89D3B236Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B236Audit

end Fuglede.Z180K30ExceptionalRawV2
