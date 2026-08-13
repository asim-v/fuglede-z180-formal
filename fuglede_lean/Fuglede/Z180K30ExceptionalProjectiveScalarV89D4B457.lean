import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B457UGroup : List RawSet :=
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

def z180K30ProjectiveScalarV89D4B457VGroup : List RawSet :=
[
  [0, 4, 8, 12, 28, 32]
]

def z180K30ProjectiveScalarV89D4B457Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 4, 8, 12, 28, 32])
def z180K30ProjectiveScalarV89D4B457Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 4, 8, 12, 28, 32])
def z180K30ProjectiveScalarV89D4B457Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 4, 8, 12, 28, 32])
def z180K30ProjectiveScalarV89D4B457Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 4, 8, 12, 28, 32])
def z180K30ProjectiveScalarV89D4B457Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 4, 8, 12, 28, 32])
def z180K30ProjectiveScalarV89D4B457Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 4, 8, 12, 28, 32])
def z180K30ProjectiveScalarV89D4B457Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 4, 8, 12, 28, 32])
def z180K30ProjectiveScalarV89D4B457Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 4, 8, 12, 28, 32])

def z180K30ProjectiveScalarV89D4B457Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B457Pair00,
  z180K30ProjectiveScalarV89D4B457Pair01,
  z180K30ProjectiveScalarV89D4B457Pair02,
  z180K30ProjectiveScalarV89D4B457Pair03,
  z180K30ProjectiveScalarV89D4B457Pair04,
  z180K30ProjectiveScalarV89D4B457Pair05,
  z180K30ProjectiveScalarV89D4B457Pair06,
  z180K30ProjectiveScalarV89D4B457Pair07
]



theorem z180K30ProjectiveScalarV89D4B457Pairs_eq :
    z180K30ProjectiveScalarV89D4B457Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B457UGroup z180K30ProjectiveScalarV89D4B457VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B457Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B457Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B457Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B457Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B457Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B457Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B457Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B457Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B457Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B457Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B457Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B457Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B457Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B457Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B457Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B457Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B457Audit :
    z180K30ProjectiveScalarV89D4B457Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B457Pairs,
    z180K30ProjectiveScalarV89D4B457Pair00Refuted,
    z180K30ProjectiveScalarV89D4B457Pair01Refuted,
    z180K30ProjectiveScalarV89D4B457Pair02Refuted,
    z180K30ProjectiveScalarV89D4B457Pair03Refuted,
    z180K30ProjectiveScalarV89D4B457Pair04Refuted,
    z180K30ProjectiveScalarV89D4B457Pair05Refuted,
    z180K30ProjectiveScalarV89D4B457Pair06Refuted,
    z180K30ProjectiveScalarV89D4B457Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B457Audit

end Fuglede.Z180K30ExceptionalRawV2
