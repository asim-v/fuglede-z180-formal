import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B459UGroup : List RawSet :=
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

def z180K30ProjectiveScalarV89D4B459VGroup : List RawSet :=
[
  [0, 4, 8, 16, 20, 28]
]

def z180K30ProjectiveScalarV89D4B459Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 4, 8, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B459Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 4, 8, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B459Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 4, 8, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B459Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 4, 8, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B459Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 4, 8, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B459Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 4, 8, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B459Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 4, 8, 16, 20, 28])
def z180K30ProjectiveScalarV89D4B459Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 4, 8, 16, 20, 28])

def z180K30ProjectiveScalarV89D4B459Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B459Pair00,
  z180K30ProjectiveScalarV89D4B459Pair01,
  z180K30ProjectiveScalarV89D4B459Pair02,
  z180K30ProjectiveScalarV89D4B459Pair03,
  z180K30ProjectiveScalarV89D4B459Pair04,
  z180K30ProjectiveScalarV89D4B459Pair05,
  z180K30ProjectiveScalarV89D4B459Pair06,
  z180K30ProjectiveScalarV89D4B459Pair07
]



theorem z180K30ProjectiveScalarV89D4B459Pairs_eq :
    z180K30ProjectiveScalarV89D4B459Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B459UGroup z180K30ProjectiveScalarV89D4B459VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B459Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B459Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B459Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B459Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B459Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B459Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B459Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B459Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B459Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B459Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B459Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B459Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B459Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B459Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B459Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B459Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B459Audit :
    z180K30ProjectiveScalarV89D4B459Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B459Pairs,
    z180K30ProjectiveScalarV89D4B459Pair00Refuted,
    z180K30ProjectiveScalarV89D4B459Pair01Refuted,
    z180K30ProjectiveScalarV89D4B459Pair02Refuted,
    z180K30ProjectiveScalarV89D4B459Pair03Refuted,
    z180K30ProjectiveScalarV89D4B459Pair04Refuted,
    z180K30ProjectiveScalarV89D4B459Pair05Refuted,
    z180K30ProjectiveScalarV89D4B459Pair06Refuted,
    z180K30ProjectiveScalarV89D4B459Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B459Audit

end Fuglede.Z180K30ExceptionalRawV2
