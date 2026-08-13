import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B454UGroup : List RawSet :=
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

def z180K30ProjectiveScalarV89D4B454VGroup : List RawSet :=
[
  [0, 4, 8, 12, 20, 32]
]

def z180K30ProjectiveScalarV89D4B454Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 4, 8, 12, 20, 32])
def z180K30ProjectiveScalarV89D4B454Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 4, 8, 12, 20, 32])
def z180K30ProjectiveScalarV89D4B454Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 4, 8, 12, 20, 32])
def z180K30ProjectiveScalarV89D4B454Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 4, 8, 12, 20, 32])
def z180K30ProjectiveScalarV89D4B454Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 4, 8, 12, 20, 32])
def z180K30ProjectiveScalarV89D4B454Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 4, 8, 12, 20, 32])
def z180K30ProjectiveScalarV89D4B454Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 4, 8, 12, 20, 32])
def z180K30ProjectiveScalarV89D4B454Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 4, 8, 12, 20, 32])

def z180K30ProjectiveScalarV89D4B454Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B454Pair00,
  z180K30ProjectiveScalarV89D4B454Pair01,
  z180K30ProjectiveScalarV89D4B454Pair02,
  z180K30ProjectiveScalarV89D4B454Pair03,
  z180K30ProjectiveScalarV89D4B454Pair04,
  z180K30ProjectiveScalarV89D4B454Pair05,
  z180K30ProjectiveScalarV89D4B454Pair06,
  z180K30ProjectiveScalarV89D4B454Pair07
]



theorem z180K30ProjectiveScalarV89D4B454Pairs_eq :
    z180K30ProjectiveScalarV89D4B454Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B454UGroup z180K30ProjectiveScalarV89D4B454VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B454Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B454Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B454Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B454Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B454Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B454Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B454Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B454Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B454Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B454Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B454Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B454Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B454Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B454Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B454Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B454Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B454Audit :
    z180K30ProjectiveScalarV89D4B454Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B454Pairs,
    z180K30ProjectiveScalarV89D4B454Pair00Refuted,
    z180K30ProjectiveScalarV89D4B454Pair01Refuted,
    z180K30ProjectiveScalarV89D4B454Pair02Refuted,
    z180K30ProjectiveScalarV89D4B454Pair03Refuted,
    z180K30ProjectiveScalarV89D4B454Pair04Refuted,
    z180K30ProjectiveScalarV89D4B454Pair05Refuted,
    z180K30ProjectiveScalarV89D4B454Pair06Refuted,
    z180K30ProjectiveScalarV89D4B454Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B454Audit

end Fuglede.Z180K30ExceptionalRawV2
