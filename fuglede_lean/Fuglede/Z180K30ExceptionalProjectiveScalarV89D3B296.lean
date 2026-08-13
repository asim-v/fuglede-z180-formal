import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B296UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B296VGroup : List RawSet :=
[
  [0, 6, 9, 21, 24, 27],
  [0, 6, 9, 21, 24, 30],
  [0, 6, 9, 21, 24, 33],
  [0, 6, 9, 21, 27, 30]
]

def z180K30ProjectiveScalarV89D3B296Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 21, 24, 27])
def z180K30ProjectiveScalarV89D3B296Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 21, 24, 30])
def z180K30ProjectiveScalarV89D3B296Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 21, 24, 33])
def z180K30ProjectiveScalarV89D3B296Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 21, 27, 30])

def z180K30ProjectiveScalarV89D3B296Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B296Pair00,
  z180K30ProjectiveScalarV89D3B296Pair01,
  z180K30ProjectiveScalarV89D3B296Pair02,
  z180K30ProjectiveScalarV89D3B296Pair03
]



theorem z180K30ProjectiveScalarV89D3B296Pairs_eq :
    z180K30ProjectiveScalarV89D3B296Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B296UGroup z180K30ProjectiveScalarV89D3B296VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B296Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B296Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B296Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B296Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B296Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B296Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B296Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B296Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B296Audit :
    z180K30ProjectiveScalarV89D3B296Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B296Pairs,
    z180K30ProjectiveScalarV89D3B296Pair00Refuted,
    z180K30ProjectiveScalarV89D3B296Pair01Refuted,
    z180K30ProjectiveScalarV89D3B296Pair02Refuted,
    z180K30ProjectiveScalarV89D3B296Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B296Audit

end Fuglede.Z180K30ExceptionalRawV2
