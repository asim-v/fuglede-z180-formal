import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B240UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B240VGroup : List RawSet :=
[
  [0, 3, 6, 12, 15, 30],
  [0, 3, 6, 12, 15, 33],
  [0, 3, 6, 12, 18, 21],
  [0, 3, 6, 12, 18, 24]
]

def z180K30ProjectiveScalarV89D3B240Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 12, 15, 30])
def z180K30ProjectiveScalarV89D3B240Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 12, 15, 33])
def z180K30ProjectiveScalarV89D3B240Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 12, 18, 21])
def z180K30ProjectiveScalarV89D3B240Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 12, 18, 24])

def z180K30ProjectiveScalarV89D3B240Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B240Pair00,
  z180K30ProjectiveScalarV89D3B240Pair01,
  z180K30ProjectiveScalarV89D3B240Pair02,
  z180K30ProjectiveScalarV89D3B240Pair03
]



theorem z180K30ProjectiveScalarV89D3B240Pairs_eq :
    z180K30ProjectiveScalarV89D3B240Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B240UGroup z180K30ProjectiveScalarV89D3B240VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B240Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B240Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B240Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B240Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B240Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B240Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B240Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B240Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B240Audit :
    z180K30ProjectiveScalarV89D3B240Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B240Pairs,
    z180K30ProjectiveScalarV89D3B240Pair00Refuted,
    z180K30ProjectiveScalarV89D3B240Pair01Refuted,
    z180K30ProjectiveScalarV89D3B240Pair02Refuted,
    z180K30ProjectiveScalarV89D3B240Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B240Audit

end Fuglede.Z180K30ExceptionalRawV2
