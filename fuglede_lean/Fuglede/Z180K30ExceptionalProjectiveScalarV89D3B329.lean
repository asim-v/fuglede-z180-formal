import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B329UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B329VGroup : List RawSet :=
[
  [0, 9, 15, 24, 27, 33],
  [0, 9, 15, 24, 30, 33],
  [0, 9, 15, 27, 30, 33],
  [0, 9, 18, 21, 24, 27]
]

def z180K30ProjectiveScalarV89D3B329Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 24, 27, 33])
def z180K30ProjectiveScalarV89D3B329Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 24, 30, 33])
def z180K30ProjectiveScalarV89D3B329Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B329Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 18, 21, 24, 27])

def z180K30ProjectiveScalarV89D3B329Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B329Pair00,
  z180K30ProjectiveScalarV89D3B329Pair01,
  z180K30ProjectiveScalarV89D3B329Pair02,
  z180K30ProjectiveScalarV89D3B329Pair03
]



theorem z180K30ProjectiveScalarV89D3B329Pairs_eq :
    z180K30ProjectiveScalarV89D3B329Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B329UGroup z180K30ProjectiveScalarV89D3B329VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B329Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B329Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B329Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B329Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B329Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B329Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B329Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B329Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B329Audit :
    z180K30ProjectiveScalarV89D3B329Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B329Pairs,
    z180K30ProjectiveScalarV89D3B329Pair00Refuted,
    z180K30ProjectiveScalarV89D3B329Pair01Refuted,
    z180K30ProjectiveScalarV89D3B329Pair02Refuted,
    z180K30ProjectiveScalarV89D3B329Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B329Audit

end Fuglede.Z180K30ExceptionalRawV2
