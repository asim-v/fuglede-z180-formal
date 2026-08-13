import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B238UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B238VGroup : List RawSet :=
[
  [0, 3, 6, 9, 24, 33],
  [0, 3, 6, 9, 27, 30],
  [0, 3, 6, 9, 27, 33],
  [0, 3, 6, 9, 30, 33]
]

def z180K30ProjectiveScalarV89D3B238Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 24, 33])
def z180K30ProjectiveScalarV89D3B238Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 27, 30])
def z180K30ProjectiveScalarV89D3B238Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 27, 33])
def z180K30ProjectiveScalarV89D3B238Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 30, 33])

def z180K30ProjectiveScalarV89D3B238Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B238Pair00,
  z180K30ProjectiveScalarV89D3B238Pair01,
  z180K30ProjectiveScalarV89D3B238Pair02,
  z180K30ProjectiveScalarV89D3B238Pair03
]



theorem z180K30ProjectiveScalarV89D3B238Pairs_eq :
    z180K30ProjectiveScalarV89D3B238Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B238UGroup z180K30ProjectiveScalarV89D3B238VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B238Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B238Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B238Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B238Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B238Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B238Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B238Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B238Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B238Audit :
    z180K30ProjectiveScalarV89D3B238Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B238Pairs,
    z180K30ProjectiveScalarV89D3B238Pair00Refuted,
    z180K30ProjectiveScalarV89D3B238Pair01Refuted,
    z180K30ProjectiveScalarV89D3B238Pair02Refuted,
    z180K30ProjectiveScalarV89D3B238Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B238Audit

end Fuglede.Z180K30ExceptionalRawV2
