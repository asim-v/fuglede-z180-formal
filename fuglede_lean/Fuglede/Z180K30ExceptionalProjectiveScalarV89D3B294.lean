import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B294UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B294VGroup : List RawSet :=
[
  [0, 6, 9, 18, 21, 30],
  [0, 6, 9, 18, 21, 33],
  [0, 6, 9, 18, 24, 27],
  [0, 6, 9, 18, 24, 30]
]

def z180K30ProjectiveScalarV89D3B294Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 18, 21, 30])
def z180K30ProjectiveScalarV89D3B294Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 18, 21, 33])
def z180K30ProjectiveScalarV89D3B294Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 18, 24, 27])
def z180K30ProjectiveScalarV89D3B294Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 18, 24, 30])

def z180K30ProjectiveScalarV89D3B294Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B294Pair00,
  z180K30ProjectiveScalarV89D3B294Pair01,
  z180K30ProjectiveScalarV89D3B294Pair02,
  z180K30ProjectiveScalarV89D3B294Pair03
]



theorem z180K30ProjectiveScalarV89D3B294Pairs_eq :
    z180K30ProjectiveScalarV89D3B294Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B294UGroup z180K30ProjectiveScalarV89D3B294VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B294Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B294Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B294Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B294Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B294Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B294Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B294Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B294Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B294Audit :
    z180K30ProjectiveScalarV89D3B294Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B294Pairs,
    z180K30ProjectiveScalarV89D3B294Pair00Refuted,
    z180K30ProjectiveScalarV89D3B294Pair01Refuted,
    z180K30ProjectiveScalarV89D3B294Pair02Refuted,
    z180K30ProjectiveScalarV89D3B294Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B294Audit

end Fuglede.Z180K30ExceptionalRawV2
