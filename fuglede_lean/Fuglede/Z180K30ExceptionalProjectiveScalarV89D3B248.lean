import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B248UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B248VGroup : List RawSet :=
[
  [0, 3, 6, 18, 21, 24],
  [0, 3, 6, 18, 21, 27],
  [0, 3, 6, 18, 21, 30],
  [0, 3, 6, 18, 21, 33]
]

def z180K30ProjectiveScalarV89D3B248Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 21, 24])
def z180K30ProjectiveScalarV89D3B248Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 21, 27])
def z180K30ProjectiveScalarV89D3B248Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 21, 30])
def z180K30ProjectiveScalarV89D3B248Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 21, 33])

def z180K30ProjectiveScalarV89D3B248Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B248Pair00,
  z180K30ProjectiveScalarV89D3B248Pair01,
  z180K30ProjectiveScalarV89D3B248Pair02,
  z180K30ProjectiveScalarV89D3B248Pair03
]



theorem z180K30ProjectiveScalarV89D3B248Pairs_eq :
    z180K30ProjectiveScalarV89D3B248Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B248UGroup z180K30ProjectiveScalarV89D3B248VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B248Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B248Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B248Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B248Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B248Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B248Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B248Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B248Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B248Audit :
    z180K30ProjectiveScalarV89D3B248Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B248Pairs,
    z180K30ProjectiveScalarV89D3B248Pair00Refuted,
    z180K30ProjectiveScalarV89D3B248Pair01Refuted,
    z180K30ProjectiveScalarV89D3B248Pair02Refuted,
    z180K30ProjectiveScalarV89D3B248Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B248Audit

end Fuglede.Z180K30ExceptionalRawV2
