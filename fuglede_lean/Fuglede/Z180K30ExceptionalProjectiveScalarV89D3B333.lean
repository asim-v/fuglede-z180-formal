import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B333UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B333VGroup : List RawSet :=
[
  [0, 9, 21, 27, 30, 33],
  [0, 9, 24, 27, 30, 33],
  [0, 12, 15, 18, 21, 24],
  [0, 12, 15, 18, 21, 27]
]

def z180K30ProjectiveScalarV89D3B333Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 21, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B333Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 24, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B333Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 18, 21, 24])
def z180K30ProjectiveScalarV89D3B333Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 18, 21, 27])

def z180K30ProjectiveScalarV89D3B333Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B333Pair00,
  z180K30ProjectiveScalarV89D3B333Pair01,
  z180K30ProjectiveScalarV89D3B333Pair02,
  z180K30ProjectiveScalarV89D3B333Pair03
]



theorem z180K30ProjectiveScalarV89D3B333Pairs_eq :
    z180K30ProjectiveScalarV89D3B333Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B333UGroup z180K30ProjectiveScalarV89D3B333VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B333Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B333Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B333Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B333Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B333Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B333Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B333Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B333Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B333Audit :
    z180K30ProjectiveScalarV89D3B333Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B333Pairs,
    z180K30ProjectiveScalarV89D3B333Pair00Refuted,
    z180K30ProjectiveScalarV89D3B333Pair01Refuted,
    z180K30ProjectiveScalarV89D3B333Pair02Refuted,
    z180K30ProjectiveScalarV89D3B333Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B333Audit

end Fuglede.Z180K30ExceptionalRawV2
