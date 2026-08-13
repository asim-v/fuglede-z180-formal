import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D4B485UGroup : List RawSet :=
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

def z180K30ProjectiveScalarV89D4B485VGroup : List RawSet :=
[
  [0, 8, 12, 16, 20, 32]
]

def z180K30ProjectiveScalarV89D4B485Pair00 : RawSet × RawSet := ([0, 8, 17, 26, 27, 35], [0, 8, 12, 16, 20, 32])
def z180K30ProjectiveScalarV89D4B485Pair01 : RawSet × RawSet := ([0, 8, 18, 26, 27, 35], [0, 8, 12, 16, 20, 32])
def z180K30ProjectiveScalarV89D4B485Pair02 : RawSet × RawSet := ([0, 9, 17, 18, 26, 27], [0, 8, 12, 16, 20, 32])
def z180K30ProjectiveScalarV89D4B485Pair03 : RawSet × RawSet := ([0, 9, 17, 18, 26, 35], [0, 8, 12, 16, 20, 32])
def z180K30ProjectiveScalarV89D4B485Pair04 : RawSet × RawSet := ([0, 9, 17, 18, 27, 35], [0, 8, 12, 16, 20, 32])
def z180K30ProjectiveScalarV89D4B485Pair05 : RawSet × RawSet := ([0, 9, 17, 26, 27, 35], [0, 8, 12, 16, 20, 32])
def z180K30ProjectiveScalarV89D4B485Pair06 : RawSet × RawSet := ([0, 9, 18, 26, 27, 35], [0, 8, 12, 16, 20, 32])
def z180K30ProjectiveScalarV89D4B485Pair07 : RawSet × RawSet := ([0, 17, 18, 26, 27, 35], [0, 8, 12, 16, 20, 32])

def z180K30ProjectiveScalarV89D4B485Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D4B485Pair00,
  z180K30ProjectiveScalarV89D4B485Pair01,
  z180K30ProjectiveScalarV89D4B485Pair02,
  z180K30ProjectiveScalarV89D4B485Pair03,
  z180K30ProjectiveScalarV89D4B485Pair04,
  z180K30ProjectiveScalarV89D4B485Pair05,
  z180K30ProjectiveScalarV89D4B485Pair06,
  z180K30ProjectiveScalarV89D4B485Pair07
]



theorem z180K30ProjectiveScalarV89D4B485Pairs_eq :
    z180K30ProjectiveScalarV89D4B485Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D4B485UGroup z180K30ProjectiveScalarV89D4B485VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B485Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B485Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B485Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B485Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B485Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B485Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B485Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B485Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B485Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B485Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B485Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B485Pair05 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B485Pair06Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B485Pair06 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D4B485Pair07Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D4B485Pair07 = true := by
  decide

theorem z180K30ProjectiveScalarV89D4B485Audit :
    z180K30ProjectiveScalarV89D4B485Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D4B485Pairs,
    z180K30ProjectiveScalarV89D4B485Pair00Refuted,
    z180K30ProjectiveScalarV89D4B485Pair01Refuted,
    z180K30ProjectiveScalarV89D4B485Pair02Refuted,
    z180K30ProjectiveScalarV89D4B485Pair03Refuted,
    z180K30ProjectiveScalarV89D4B485Pair04Refuted,
    z180K30ProjectiveScalarV89D4B485Pair05Refuted,
    z180K30ProjectiveScalarV89D4B485Pair06Refuted,
    z180K30ProjectiveScalarV89D4B485Pair07Refuted]

#print axioms z180K30ProjectiveScalarV89D4B485Audit

end Fuglede.Z180K30ExceptionalRawV2
