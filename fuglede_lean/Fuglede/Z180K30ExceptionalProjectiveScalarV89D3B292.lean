import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B292UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B292VGroup : List RawSet :=
[
  [0, 6, 9, 15, 24, 27],
  [0, 6, 9, 15, 24, 30],
  [0, 6, 9, 15, 24, 33],
  [0, 6, 9, 15, 27, 30]
]

def z180K30ProjectiveScalarV89D3B292Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 15, 24, 27])
def z180K30ProjectiveScalarV89D3B292Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 15, 24, 30])
def z180K30ProjectiveScalarV89D3B292Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 15, 24, 33])
def z180K30ProjectiveScalarV89D3B292Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 15, 27, 30])

def z180K30ProjectiveScalarV89D3B292Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B292Pair00,
  z180K30ProjectiveScalarV89D3B292Pair01,
  z180K30ProjectiveScalarV89D3B292Pair02,
  z180K30ProjectiveScalarV89D3B292Pair03
]



theorem z180K30ProjectiveScalarV89D3B292Pairs_eq :
    z180K30ProjectiveScalarV89D3B292Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B292UGroup z180K30ProjectiveScalarV89D3B292VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B292Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B292Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B292Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B292Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B292Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B292Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B292Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B292Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B292Audit :
    z180K30ProjectiveScalarV89D3B292Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B292Pairs,
    z180K30ProjectiveScalarV89D3B292Pair00Refuted,
    z180K30ProjectiveScalarV89D3B292Pair01Refuted,
    z180K30ProjectiveScalarV89D3B292Pair02Refuted,
    z180K30ProjectiveScalarV89D3B292Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B292Audit

end Fuglede.Z180K30ExceptionalRawV2
