import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B283UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B283VGroup : List RawSet :=
[
  [0, 3, 18, 27, 30, 33],
  [0, 3, 21, 24, 27, 30],
  [0, 3, 21, 24, 27, 33],
  [0, 3, 21, 24, 30, 33]
]

def z180K30ProjectiveScalarV89D3B283Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 18, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B283Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 21, 24, 27, 30])
def z180K30ProjectiveScalarV89D3B283Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 21, 24, 27, 33])
def z180K30ProjectiveScalarV89D3B283Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 21, 24, 30, 33])

def z180K30ProjectiveScalarV89D3B283Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B283Pair00,
  z180K30ProjectiveScalarV89D3B283Pair01,
  z180K30ProjectiveScalarV89D3B283Pair02,
  z180K30ProjectiveScalarV89D3B283Pair03
]



theorem z180K30ProjectiveScalarV89D3B283Pairs_eq :
    z180K30ProjectiveScalarV89D3B283Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B283UGroup z180K30ProjectiveScalarV89D3B283VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B283Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B283Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B283Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B283Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B283Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B283Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B283Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B283Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B283Audit :
    z180K30ProjectiveScalarV89D3B283Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B283Pairs,
    z180K30ProjectiveScalarV89D3B283Pair00Refuted,
    z180K30ProjectiveScalarV89D3B283Pair01Refuted,
    z180K30ProjectiveScalarV89D3B283Pair02Refuted,
    z180K30ProjectiveScalarV89D3B283Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B283Audit

end Fuglede.Z180K30ExceptionalRawV2
