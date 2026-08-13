import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B486UGroup : List RawSet :=
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

def z180K30ProjectiveScalarV89D4B486VGroup : List RawSet :=
[
  [0, 8, 12, 16, 24, 28]
]

def z180K30ProjectiveScalarV89D4B486Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 8, 12, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B486Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 8, 12, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B486Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 8, 12, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B486Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 8, 12, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B486Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 8, 12, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B486Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 8, 12, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B486Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 8, 12, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B486Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 8, 12, 16, 24, 28])

def z180K30ProjectiveScalarV89D4B486Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B486Pair00,
  z180K30ProjectiveScalarV89D4B486Pair01,
  z180K30ProjectiveScalarV89D4B486Pair02,
  z180K30ProjectiveScalarV89D4B486Pair03,
  z180K30ProjectiveScalarV89D4B486Pair04,
  z180K30ProjectiveScalarV89D4B486Pair05,
  z180K30ProjectiveScalarV89D4B486Pair06,
  z180K30ProjectiveScalarV89D4B486Pair07
]



theorem z180K30ProjectiveScalarV89D4B486Pairs_eq :
    z180K30ProjectiveScalarV89D4B486Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B486UGroup z180K30ProjectiveScalarV89D4B486VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B486Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B486Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B486Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B486Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B486Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B486Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B486Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B486Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B486Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B486Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B486Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B486Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B486Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B486Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B486Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B486Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B486Audit :
    z180K30ProjectiveScalarV89D4B486Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B486Pairs,
    z180K30ProjectiveScalarV89D4B486Pair00Refuted,
    z180K30ProjectiveScalarV89D4B486Pair01Refuted,
    z180K30ProjectiveScalarV89D4B486Pair02Refuted,
    z180K30ProjectiveScalarV89D4B486Pair03Refuted,
    z180K30ProjectiveScalarV89D4B486Pair04Refuted,
    z180K30ProjectiveScalarV89D4B486Pair05Refuted,
    z180K30ProjectiveScalarV89D4B486Pair06Refuted,
    z180K30ProjectiveScalarV89D4B486Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B486Audit

end Fuglede.Z180K30ExceptionalRawV2
