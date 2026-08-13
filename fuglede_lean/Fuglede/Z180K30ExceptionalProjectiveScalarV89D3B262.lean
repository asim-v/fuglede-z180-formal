import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B262UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B262VGroup : List RawSet :=
[
  [0, 3, 9, 18, 21, 24],
  [0, 3, 9, 18, 21, 27],
  [0, 3, 9, 18, 21, 30],
  [0, 3, 9, 18, 21, 33]
]

def z180K30ProjectiveScalarV89D3B262Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 18, 21, 24])
def z180K30ProjectiveScalarV89D3B262Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 18, 21, 27])
def z180K30ProjectiveScalarV89D3B262Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 18, 21, 30])
def z180K30ProjectiveScalarV89D3B262Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 18, 21, 33])

def z180K30ProjectiveScalarV89D3B262Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B262Pair00,
  z180K30ProjectiveScalarV89D3B262Pair01,
  z180K30ProjectiveScalarV89D3B262Pair02,
  z180K30ProjectiveScalarV89D3B262Pair03
]



theorem z180K30ProjectiveScalarV89D3B262Pairs_eq :
    z180K30ProjectiveScalarV89D3B262Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B262UGroup z180K30ProjectiveScalarV89D3B262VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B262Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B262Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B262Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B262Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B262Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B262Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B262Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B262Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B262Audit :
    z180K30ProjectiveScalarV89D3B262Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B262Pairs,
    z180K30ProjectiveScalarV89D3B262Pair00Refuted,
    z180K30ProjectiveScalarV89D3B262Pair01Refuted,
    z180K30ProjectiveScalarV89D3B262Pair02Refuted,
    z180K30ProjectiveScalarV89D3B262Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B262Audit

end Fuglede.Z180K30ExceptionalRawV2
