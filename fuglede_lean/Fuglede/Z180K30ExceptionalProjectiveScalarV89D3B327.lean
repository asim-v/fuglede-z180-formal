import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B327UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B327VGroup : List RawSet :=
[
  [0, 9, 15, 18, 30, 33],
  [0, 9, 15, 21, 24, 27],
  [0, 9, 15, 21, 24, 30],
  [0, 9, 15, 21, 24, 33]
]

def z180K30ProjectiveScalarV89D3B327Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 18, 30, 33])
def z180K30ProjectiveScalarV89D3B327Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 21, 24, 27])
def z180K30ProjectiveScalarV89D3B327Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 21, 24, 30])
def z180K30ProjectiveScalarV89D3B327Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 15, 21, 24, 33])

def z180K30ProjectiveScalarV89D3B327Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B327Pair00,
  z180K30ProjectiveScalarV89D3B327Pair01,
  z180K30ProjectiveScalarV89D3B327Pair02,
  z180K30ProjectiveScalarV89D3B327Pair03
]



theorem z180K30ProjectiveScalarV89D3B327Pairs_eq :
    z180K30ProjectiveScalarV89D3B327Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B327UGroup z180K30ProjectiveScalarV89D3B327VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B327Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B327Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B327Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B327Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B327Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B327Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B327Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B327Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B327Audit :
    z180K30ProjectiveScalarV89D3B327Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B327Pairs,
    z180K30ProjectiveScalarV89D3B327Pair00Refuted,
    z180K30ProjectiveScalarV89D3B327Pair01Refuted,
    z180K30ProjectiveScalarV89D3B327Pair02Refuted,
    z180K30ProjectiveScalarV89D3B327Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B327Audit

end Fuglede.Z180K30ExceptionalRawV2
