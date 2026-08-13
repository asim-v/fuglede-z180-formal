import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B345UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B345VGroup : List RawSet :=
[
  [0, 15, 21, 24, 27, 33],
  [0, 15, 21, 24, 30, 33],
  [0, 15, 21, 27, 30, 33],
  [0, 15, 24, 27, 30, 33]
]

def z180K30ProjectiveScalarV89D3B345Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 21, 24, 27, 33])
def z180K30ProjectiveScalarV89D3B345Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 21, 24, 30, 33])
def z180K30ProjectiveScalarV89D3B345Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 21, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B345Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 24, 27, 30, 33])

def z180K30ProjectiveScalarV89D3B345Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B345Pair00,
  z180K30ProjectiveScalarV89D3B345Pair01,
  z180K30ProjectiveScalarV89D3B345Pair02,
  z180K30ProjectiveScalarV89D3B345Pair03
]



theorem z180K30ProjectiveScalarV89D3B345Pairs_eq :
    z180K30ProjectiveScalarV89D3B345Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B345UGroup z180K30ProjectiveScalarV89D3B345VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B345Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B345Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B345Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B345Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B345Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B345Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B345Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B345Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B345Audit :
    z180K30ProjectiveScalarV89D3B345Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B345Pairs,
    z180K30ProjectiveScalarV89D3B345Pair00Refuted,
    z180K30ProjectiveScalarV89D3B345Pair01Refuted,
    z180K30ProjectiveScalarV89D3B345Pair02Refuted,
    z180K30ProjectiveScalarV89D3B345Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B345Audit

end Fuglede.Z180K30ExceptionalRawV2
