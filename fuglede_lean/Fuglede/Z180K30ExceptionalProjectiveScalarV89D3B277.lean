import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B277UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B277VGroup : List RawSet :=
[
  [0, 3, 15, 18, 24, 30],
  [0, 3, 15, 18, 24, 33],
  [0, 3, 15, 18, 27, 30],
  [0, 3, 15, 18, 27, 33]
]

def z180K30ProjectiveScalarV89D3B277Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 15, 18, 24, 30])
def z180K30ProjectiveScalarV89D3B277Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 15, 18, 24, 33])
def z180K30ProjectiveScalarV89D3B277Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 15, 18, 27, 30])
def z180K30ProjectiveScalarV89D3B277Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 15, 18, 27, 33])

def z180K30ProjectiveScalarV89D3B277Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B277Pair00,
  z180K30ProjectiveScalarV89D3B277Pair01,
  z180K30ProjectiveScalarV89D3B277Pair02,
  z180K30ProjectiveScalarV89D3B277Pair03
]



theorem z180K30ProjectiveScalarV89D3B277Pairs_eq :
    z180K30ProjectiveScalarV89D3B277Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B277UGroup z180K30ProjectiveScalarV89D3B277VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B277Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B277Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B277Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B277Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B277Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B277Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B277Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B277Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B277Audit :
    z180K30ProjectiveScalarV89D3B277Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B277Pairs,
    z180K30ProjectiveScalarV89D3B277Pair00Refuted,
    z180K30ProjectiveScalarV89D3B277Pair01Refuted,
    z180K30ProjectiveScalarV89D3B277Pair02Refuted,
    z180K30ProjectiveScalarV89D3B277Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B277Audit

end Fuglede.Z180K30ExceptionalRawV2
