import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B253UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B253VGroup : List RawSet :=
[
  [0, 3, 9, 12, 15, 18],
  [0, 3, 9, 12, 15, 21],
  [0, 3, 9, 12, 15, 24],
  [0, 3, 9, 12, 15, 27]
]

def z180K30ProjectiveScalarV89D3B253Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 12, 15, 18])
def z180K30ProjectiveScalarV89D3B253Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 12, 15, 21])
def z180K30ProjectiveScalarV89D3B253Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 12, 15, 24])
def z180K30ProjectiveScalarV89D3B253Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 12, 15, 27])

def z180K30ProjectiveScalarV89D3B253Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B253Pair00,
  z180K30ProjectiveScalarV89D3B253Pair01,
  z180K30ProjectiveScalarV89D3B253Pair02,
  z180K30ProjectiveScalarV89D3B253Pair03
]



theorem z180K30ProjectiveScalarV89D3B253Pairs_eq :
    z180K30ProjectiveScalarV89D3B253Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B253UGroup z180K30ProjectiveScalarV89D3B253VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B253Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B253Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B253Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B253Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B253Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B253Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B253Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B253Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B253Audit :
    z180K30ProjectiveScalarV89D3B253Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B253Pairs,
    z180K30ProjectiveScalarV89D3B253Pair00Refuted,
    z180K30ProjectiveScalarV89D3B253Pair01Refuted,
    z180K30ProjectiveScalarV89D3B253Pair02Refuted,
    z180K30ProjectiveScalarV89D3B253Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B253Audit

end Fuglede.Z180K30ExceptionalRawV2
