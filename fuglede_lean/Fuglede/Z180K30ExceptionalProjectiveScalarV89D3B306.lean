import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B306UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B306VGroup : List RawSet :=
[
  [0, 6, 12, 21, 30, 33],
  [0, 6, 12, 24, 27, 30],
  [0, 6, 12, 24, 27, 33],
  [0, 6, 12, 24, 30, 33]
]

def z180K30ProjectiveScalarV89D3B306Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 21, 30, 33])
def z180K30ProjectiveScalarV89D3B306Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 24, 27, 30])
def z180K30ProjectiveScalarV89D3B306Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 24, 27, 33])
def z180K30ProjectiveScalarV89D3B306Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 24, 30, 33])

def z180K30ProjectiveScalarV89D3B306Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B306Pair00,
  z180K30ProjectiveScalarV89D3B306Pair01,
  z180K30ProjectiveScalarV89D3B306Pair02,
  z180K30ProjectiveScalarV89D3B306Pair03
]



theorem z180K30ProjectiveScalarV89D3B306Pairs_eq :
    z180K30ProjectiveScalarV89D3B306Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B306UGroup z180K30ProjectiveScalarV89D3B306VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B306Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B306Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B306Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B306Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B306Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B306Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B306Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B306Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B306Audit :
    z180K30ProjectiveScalarV89D3B306Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B306Pairs,
    z180K30ProjectiveScalarV89D3B306Pair00Refuted,
    z180K30ProjectiveScalarV89D3B306Pair01Refuted,
    z180K30ProjectiveScalarV89D3B306Pair02Refuted,
    z180K30ProjectiveScalarV89D3B306Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B306Audit

end Fuglede.Z180K30ExceptionalRawV2
