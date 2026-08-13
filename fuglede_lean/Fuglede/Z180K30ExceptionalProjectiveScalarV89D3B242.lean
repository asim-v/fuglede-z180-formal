import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B242UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B242VGroup : List RawSet :=
[
  [0, 3, 6, 12, 21, 27],
  [0, 3, 6, 12, 21, 30],
  [0, 3, 6, 12, 21, 33],
  [0, 3, 6, 12, 24, 27]
]

def z180K30ProjectiveScalarV89D3B242Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 12, 21, 27])
def z180K30ProjectiveScalarV89D3B242Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 12, 21, 30])
def z180K30ProjectiveScalarV89D3B242Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 12, 21, 33])
def z180K30ProjectiveScalarV89D3B242Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 12, 24, 27])

def z180K30ProjectiveScalarV89D3B242Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B242Pair00,
  z180K30ProjectiveScalarV89D3B242Pair01,
  z180K30ProjectiveScalarV89D3B242Pair02,
  z180K30ProjectiveScalarV89D3B242Pair03
]



theorem z180K30ProjectiveScalarV89D3B242Pairs_eq :
    z180K30ProjectiveScalarV89D3B242Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B242UGroup z180K30ProjectiveScalarV89D3B242VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B242Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B242Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B242Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B242Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B242Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B242Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B242Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B242Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B242Audit :
    z180K30ProjectiveScalarV89D3B242Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B242Pairs,
    z180K30ProjectiveScalarV89D3B242Pair00Refuted,
    z180K30ProjectiveScalarV89D3B242Pair01Refuted,
    z180K30ProjectiveScalarV89D3B242Pair02Refuted,
    z180K30ProjectiveScalarV89D3B242Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B242Audit

end Fuglede.Z180K30ExceptionalRawV2
