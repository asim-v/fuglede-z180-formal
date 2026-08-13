import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B463UGroup : List RawSet :=
[
  [0, 8, 17, 26, 27, 35],
  [0, 8, 18, 26, 27, 35],
  [0, 9, 17, 18, 26, 27],
  [0, 9, 17, 18, 26, 35],
  [0, 9, 17, 18, 27, 35],
  [0, 9, 17, 26, 27, 35],
  [0, 9, 18, 26, 27, 35],
  [0, 17, 18, 26, 27, 35]
]

def z180K30ProjectiveScalarV89D4B463VGroup : List RawSet :=
[
  [0, 4, 8, 16, 28, 32]
]

def z180K30ProjectiveScalarV89D4B463Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 4, 8, 16, 28, 32])
def z180K30ProjectiveScalarV89D4B463Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 4, 8, 16, 28, 32])
def z180K30ProjectiveScalarV89D4B463Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 4, 8, 16, 28, 32])
def z180K30ProjectiveScalarV89D4B463Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 4, 8, 16, 28, 32])
def z180K30ProjectiveScalarV89D4B463Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 4, 8, 16, 28, 32])
def z180K30ProjectiveScalarV89D4B463Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 4, 8, 16, 28, 32])
def z180K30ProjectiveScalarV89D4B463Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 4, 8, 16, 28, 32])
def z180K30ProjectiveScalarV89D4B463Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 4, 8, 16, 28, 32])

def z180K30ProjectiveScalarV89D4B463Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B463Pair00,
  z180K30ProjectiveScalarV89D4B463Pair01,
  z180K30ProjectiveScalarV89D4B463Pair02,
  z180K30ProjectiveScalarV89D4B463Pair03,
  z180K30ProjectiveScalarV89D4B463Pair04,
  z180K30ProjectiveScalarV89D4B463Pair05,
  z180K30ProjectiveScalarV89D4B463Pair06,
  z180K30ProjectiveScalarV89D4B463Pair07
]



theorem z180K30ProjectiveScalarV89D4B463Pairs_eq :
    z180K30ProjectiveScalarV89D4B463Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B463UGroup z180K30ProjectiveScalarV89D4B463VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B463Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B463Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B463Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B463Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B463Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B463Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B463Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B463Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B463Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B463Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B463Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B463Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B463Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B463Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B463Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B463Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B463Audit :
    z180K30ProjectiveScalarV89D4B463Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B463Pairs,
    z180K30ProjectiveScalarV89D4B463Pair00Refuted,
    z180K30ProjectiveScalarV89D4B463Pair01Refuted,
    z180K30ProjectiveScalarV89D4B463Pair02Refuted,
    z180K30ProjectiveScalarV89D4B463Pair03Refuted,
    z180K30ProjectiveScalarV89D4B463Pair04Refuted,
    z180K30ProjectiveScalarV89D4B463Pair05Refuted,
    z180K30ProjectiveScalarV89D4B463Pair06Refuted,
    z180K30ProjectiveScalarV89D4B463Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B463Audit

end Fuglede.Z180K30ExceptionalRawV2
