import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B468UGroup : List RawSet :=
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

def z180K30ProjectiveScalarV89D4B468VGroup : List RawSet :=
[
  [0, 4, 12, 16, 20, 24]
]

def z180K30ProjectiveScalarV89D4B468Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 4, 12, 16, 20, 24])
def z180K30ProjectiveScalarV89D4B468Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 4, 12, 16, 20, 24])
def z180K30ProjectiveScalarV89D4B468Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 4, 12, 16, 20, 24])
def z180K30ProjectiveScalarV89D4B468Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 4, 12, 16, 20, 24])
def z180K30ProjectiveScalarV89D4B468Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 4, 12, 16, 20, 24])
def z180K30ProjectiveScalarV89D4B468Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 4, 12, 16, 20, 24])
def z180K30ProjectiveScalarV89D4B468Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 4, 12, 16, 20, 24])
def z180K30ProjectiveScalarV89D4B468Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 4, 12, 16, 20, 24])

def z180K30ProjectiveScalarV89D4B468Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B468Pair00,
  z180K30ProjectiveScalarV89D4B468Pair01,
  z180K30ProjectiveScalarV89D4B468Pair02,
  z180K30ProjectiveScalarV89D4B468Pair03,
  z180K30ProjectiveScalarV89D4B468Pair04,
  z180K30ProjectiveScalarV89D4B468Pair05,
  z180K30ProjectiveScalarV89D4B468Pair06,
  z180K30ProjectiveScalarV89D4B468Pair07
]



theorem z180K30ProjectiveScalarV89D4B468Pairs_eq :
    z180K30ProjectiveScalarV89D4B468Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B468UGroup z180K30ProjectiveScalarV89D4B468VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B468Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B468Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B468Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B468Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B468Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B468Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B468Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B468Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B468Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B468Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B468Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B468Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B468Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B468Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B468Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B468Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B468Audit :
    z180K30ProjectiveScalarV89D4B468Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B468Pairs,
    z180K30ProjectiveScalarV89D4B468Pair00Refuted,
    z180K30ProjectiveScalarV89D4B468Pair01Refuted,
    z180K30ProjectiveScalarV89D4B468Pair02Refuted,
    z180K30ProjectiveScalarV89D4B468Pair03Refuted,
    z180K30ProjectiveScalarV89D4B468Pair04Refuted,
    z180K30ProjectiveScalarV89D4B468Pair05Refuted,
    z180K30ProjectiveScalarV89D4B468Pair06Refuted,
    z180K30ProjectiveScalarV89D4B468Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B468Audit

end Fuglede.Z180K30ExceptionalRawV2
