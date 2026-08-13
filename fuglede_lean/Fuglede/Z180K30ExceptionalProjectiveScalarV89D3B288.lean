import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B288UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B288VGroup : List RawSet :=
[
  [0, 6, 9, 12, 21, 33],
  [0, 6, 9, 12, 24, 27],
  [0, 6, 9, 12, 24, 30],
  [0, 6, 9, 12, 24, 33]
]

def z180K30ProjectiveScalarV89D3B288Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 21, 33])
def z180K30ProjectiveScalarV89D3B288Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 24, 27])
def z180K30ProjectiveScalarV89D3B288Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 24, 30])
def z180K30ProjectiveScalarV89D3B288Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 24, 33])

def z180K30ProjectiveScalarV89D3B288Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B288Pair00,
  z180K30ProjectiveScalarV89D3B288Pair01,
  z180K30ProjectiveScalarV89D3B288Pair02,
  z180K30ProjectiveScalarV89D3B288Pair03
]



theorem z180K30ProjectiveScalarV89D3B288Pairs_eq :
    z180K30ProjectiveScalarV89D3B288Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B288UGroup z180K30ProjectiveScalarV89D3B288VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B288Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B288Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B288Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B288Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B288Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B288Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B288Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B288Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B288Audit :
    z180K30ProjectiveScalarV89D3B288Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B288Pairs,
    z180K30ProjectiveScalarV89D3B288Pair00Refuted,
    z180K30ProjectiveScalarV89D3B288Pair01Refuted,
    z180K30ProjectiveScalarV89D3B288Pair02Refuted,
    z180K30ProjectiveScalarV89D3B288Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B288Audit

end Fuglede.Z180K30ExceptionalRawV2
