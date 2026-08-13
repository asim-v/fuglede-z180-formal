import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B490UGroup : List RawSet :=
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

def z180K30ProjectiveScalarV89D4B490VGroup : List RawSet :=
[
  [0, 8, 12, 20, 24, 32]
]

def z180K30ProjectiveScalarV89D4B490Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 8, 12, 20, 24, 32])
def z180K30ProjectiveScalarV89D4B490Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 8, 12, 20, 24, 32])
def z180K30ProjectiveScalarV89D4B490Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 8, 12, 20, 24, 32])
def z180K30ProjectiveScalarV89D4B490Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 8, 12, 20, 24, 32])
def z180K30ProjectiveScalarV89D4B490Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 8, 12, 20, 24, 32])
def z180K30ProjectiveScalarV89D4B490Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 8, 12, 20, 24, 32])
def z180K30ProjectiveScalarV89D4B490Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 8, 12, 20, 24, 32])
def z180K30ProjectiveScalarV89D4B490Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 8, 12, 20, 24, 32])

def z180K30ProjectiveScalarV89D4B490Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B490Pair00,
  z180K30ProjectiveScalarV89D4B490Pair01,
  z180K30ProjectiveScalarV89D4B490Pair02,
  z180K30ProjectiveScalarV89D4B490Pair03,
  z180K30ProjectiveScalarV89D4B490Pair04,
  z180K30ProjectiveScalarV89D4B490Pair05,
  z180K30ProjectiveScalarV89D4B490Pair06,
  z180K30ProjectiveScalarV89D4B490Pair07
]



theorem z180K30ProjectiveScalarV89D4B490Pairs_eq :
    z180K30ProjectiveScalarV89D4B490Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B490UGroup z180K30ProjectiveScalarV89D4B490VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B490Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B490Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B490Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B490Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B490Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B490Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B490Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B490Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B490Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B490Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B490Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B490Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B490Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B490Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B490Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B490Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B490Audit :
    z180K30ProjectiveScalarV89D4B490Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B490Pairs,
    z180K30ProjectiveScalarV89D4B490Pair00Refuted,
    z180K30ProjectiveScalarV89D4B490Pair01Refuted,
    z180K30ProjectiveScalarV89D4B490Pair02Refuted,
    z180K30ProjectiveScalarV89D4B490Pair03Refuted,
    z180K30ProjectiveScalarV89D4B490Pair04Refuted,
    z180K30ProjectiveScalarV89D4B490Pair05Refuted,
    z180K30ProjectiveScalarV89D4B490Pair06Refuted,
    z180K30ProjectiveScalarV89D4B490Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B490Audit

end Fuglede.Z180K30ExceptionalRawV2
