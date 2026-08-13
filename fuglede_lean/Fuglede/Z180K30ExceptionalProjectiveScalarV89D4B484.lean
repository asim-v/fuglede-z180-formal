import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B484UGroup : List RawSet :=
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

def z180K30ProjectiveScalarV89D4B484VGroup : List RawSet :=
[
  [0, 8, 12, 16, 20, 28]
]

def z180K30ProjectiveScalarV89D4B484Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 8, 12, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B484Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 8, 12, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B484Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 8, 12, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B484Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 8, 12, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B484Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 8, 12, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B484Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 8, 12, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B484Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 8, 12, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B484Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 8, 12, 16, 20, 28])

def z180K30ProjectiveScalarV89D4B484Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B484Pair00,
  z180K30ProjectiveScalarV89D4B484Pair01,
  z180K30ProjectiveScalarV89D4B484Pair02,
  z180K30ProjectiveScalarV89D4B484Pair03,
  z180K30ProjectiveScalarV89D4B484Pair04,
  z180K30ProjectiveScalarV89D4B484Pair05,
  z180K30ProjectiveScalarV89D4B484Pair06,
  z180K30ProjectiveScalarV89D4B484Pair07
]



theorem z180K30ProjectiveScalarV89D4B484Pairs_eq :
    z180K30ProjectiveScalarV89D4B484Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B484UGroup z180K30ProjectiveScalarV89D4B484VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B484Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B484Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B484Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B484Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B484Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B484Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B484Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B484Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B484Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B484Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B484Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B484Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B484Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B484Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B484Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B484Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B484Audit :
    z180K30ProjectiveScalarV89D4B484Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B484Pairs,
    z180K30ProjectiveScalarV89D4B484Pair00Refuted,
    z180K30ProjectiveScalarV89D4B484Pair01Refuted,
    z180K30ProjectiveScalarV89D4B484Pair02Refuted,
    z180K30ProjectiveScalarV89D4B484Pair03Refuted,
    z180K30ProjectiveScalarV89D4B484Pair04Refuted,
    z180K30ProjectiveScalarV89D4B484Pair05Refuted,
    z180K30ProjectiveScalarV89D4B484Pair06Refuted,
    z180K30ProjectiveScalarV89D4B484Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B484Audit

end Fuglede.Z180K30ExceptionalRawV2
