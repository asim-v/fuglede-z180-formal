import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D6B115UGroup : List RawSet :=
[
  [0, 18, 23, 24, 29, 30],
  [0, 18, 23, 24, 29, 35],
  [0, 18, 23, 24, 30, 35],
  [0, 18, 23, 29, 30, 35],
  [0, 18, 24, 29, 30, 35],
  [0, 23, 24, 29, 30, 35]
]

def z180K30ProjectiveScalarV89D6B115VGroup : List RawSet :=
[
  [0, 6, 12, 18, 24, 30]
]

def z180K30ProjectiveScalarV89D6B115Pair00 : RawSet × RawSet := ([0, 18, 23, 24, 29, 30], [0, 6, 12, 18, 24, 30])
def z180K30ProjectiveScalarV89D6B115Pair01 : RawSet × RawSet := ([0, 18, 23, 24, 29, 35], [0, 6, 12, 18, 24, 30])
def z180K30ProjectiveScalarV89D6B115Pair02 : RawSet × RawSet := ([0, 18, 23, 24, 30, 35], [0, 6, 12, 18, 24, 30])
def z180K30ProjectiveScalarV89D6B115Pair03 : RawSet × RawSet := ([0, 18, 23, 29, 30, 35], [0, 6, 12, 18, 24, 30])
def z180K30ProjectiveScalarV89D6B115Pair04 : RawSet × RawSet := ([0, 18, 24, 29, 30, 35], [0, 6, 12, 18, 24, 30])
def z180K30ProjectiveScalarV89D6B115Pair05 : RawSet × RawSet := ([0, 23, 24, 29, 30, 35], [0, 6, 12, 18, 24, 30])

def z180K30ProjectiveScalarV89D6B115Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D6B115Pair00,
  z180K30ProjectiveScalarV89D6B115Pair01,
  z180K30ProjectiveScalarV89D6B115Pair02,
  z180K30ProjectiveScalarV89D6B115Pair03,
  z180K30ProjectiveScalarV89D6B115Pair04,
  z180K30ProjectiveScalarV89D6B115Pair05
]



theorem z180K30ProjectiveScalarV89D6B115Pairs_eq :
    z180K30ProjectiveScalarV89D6B115Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D6B115UGroup z180K30ProjectiveScalarV89D6B115VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D6B115Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D6B115Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D6B115Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D6B115Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D6B115Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D6B115Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D6B115Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D6B115Pair03 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D6B115Pair04Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D6B115Pair04 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D6B115Pair05Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D6B115Pair05 = true := by
  decide

theorem z180K30ProjectiveScalarV89D6B115Audit :
    z180K30ProjectiveScalarV89D6B115Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D6B115Pairs,
    z180K30ProjectiveScalarV89D6B115Pair00Refuted,
    z180K30ProjectiveScalarV89D6B115Pair01Refuted,
    z180K30ProjectiveScalarV89D6B115Pair02Refuted,
    z180K30ProjectiveScalarV89D6B115Pair03Refuted,
    z180K30ProjectiveScalarV89D6B115Pair04Refuted,
    z180K30ProjectiveScalarV89D6B115Pair05Refuted]

#print axioms z180K30ProjectiveScalarV89D6B115Audit

end Fuglede.Z180K30ExceptionalRawV2
