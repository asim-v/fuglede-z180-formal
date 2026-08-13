import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B461UGroup : List RawSet :=
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

def z180K30ProjectiveScalarV89D4B461VGroup : List RawSet :=
[
  [0, 4, 8, 16, 24, 28]
]

def z180K30ProjectiveScalarV89D4B461Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 4, 8, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B461Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 4, 8, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B461Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 4, 8, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B461Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 4, 8, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B461Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 4, 8, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B461Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 4, 8, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B461Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 4, 8, 16, 24, 28])
def z180K30ProjectiveScalarV89D4B461Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 4, 8, 16, 24, 28])

def z180K30ProjectiveScalarV89D4B461Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B461Pair00,
  z180K30ProjectiveScalarV89D4B461Pair01,
  z180K30ProjectiveScalarV89D4B461Pair02,
  z180K30ProjectiveScalarV89D4B461Pair03,
  z180K30ProjectiveScalarV89D4B461Pair04,
  z180K30ProjectiveScalarV89D4B461Pair05,
  z180K30ProjectiveScalarV89D4B461Pair06,
  z180K30ProjectiveScalarV89D4B461Pair07
]



theorem z180K30ProjectiveScalarV89D4B461Pairs_eq :
    z180K30ProjectiveScalarV89D4B461Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B461UGroup z180K30ProjectiveScalarV89D4B461VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B461Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B461Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B461Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B461Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B461Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B461Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B461Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B461Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B461Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B461Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B461Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B461Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B461Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B461Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B461Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B461Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B461Audit :
    z180K30ProjectiveScalarV89D4B461Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B461Pairs,
    z180K30ProjectiveScalarV89D4B461Pair00Refuted,
    z180K30ProjectiveScalarV89D4B461Pair01Refuted,
    z180K30ProjectiveScalarV89D4B461Pair02Refuted,
    z180K30ProjectiveScalarV89D4B461Pair03Refuted,
    z180K30ProjectiveScalarV89D4B461Pair04Refuted,
    z180K30ProjectiveScalarV89D4B461Pair05Refuted,
    z180K30ProjectiveScalarV89D4B461Pair06Refuted,
    z180K30ProjectiveScalarV89D4B461Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B461Audit

end Fuglede.Z180K30ExceptionalRawV2
