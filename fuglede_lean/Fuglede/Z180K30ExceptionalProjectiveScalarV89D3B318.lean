import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B318UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B318VGroup : List RawSet :=
[
  [0, 9, 12, 15, 21, 33],
  [0, 9, 12, 15, 24, 27],
  [0, 9, 12, 15, 24, 30],
  [0, 9, 12, 15, 24, 33]
]

def z180K30ProjectiveScalarV89D3B318Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 21, 33])
def z180K30ProjectiveScalarV89D3B318Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 24, 27])
def z180K30ProjectiveScalarV89D3B318Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 24, 30])
def z180K30ProjectiveScalarV89D3B318Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 24, 33])

def z180K30ProjectiveScalarV89D3B318Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B318Pair00,
  z180K30ProjectiveScalarV89D3B318Pair01,
  z180K30ProjectiveScalarV89D3B318Pair02,
  z180K30ProjectiveScalarV89D3B318Pair03
]



theorem z180K30ProjectiveScalarV89D3B318Pairs_eq :
    z180K30ProjectiveScalarV89D3B318Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B318UGroup z180K30ProjectiveScalarV89D3B318VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B318Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B318Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B318Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B318Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B318Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B318Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B318Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B318Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B318Audit :
    z180K30ProjectiveScalarV89D3B318Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B318Pairs,
    z180K30ProjectiveScalarV89D3B318Pair00Refuted,
    z180K30ProjectiveScalarV89D3B318Pair01Refuted,
    z180K30ProjectiveScalarV89D3B318Pair02Refuted,
    z180K30ProjectiveScalarV89D3B318Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B318Audit

end Fuglede.Z180K30ExceptionalRawV2
