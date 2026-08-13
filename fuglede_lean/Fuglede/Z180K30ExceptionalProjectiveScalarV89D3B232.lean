import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B232UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B232VGroup : List RawSet :=
[
  [0, 3, 6, 9, 12, 15],
  [0, 3, 6, 9, 12, 18],
  [0, 3, 6, 9, 12, 21],
  [0, 3, 6, 9, 12, 24]
]

def z180K30ProjectiveScalarV89D3B232Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 12, 15])
def z180K30ProjectiveScalarV89D3B232Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 12, 18])
def z180K30ProjectiveScalarV89D3B232Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 12, 21])
def z180K30ProjectiveScalarV89D3B232Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 12, 24])

def z180K30ProjectiveScalarV89D3B232Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B232Pair00,
  z180K30ProjectiveScalarV89D3B232Pair01,
  z180K30ProjectiveScalarV89D3B232Pair02,
  z180K30ProjectiveScalarV89D3B232Pair03
]



theorem z180K30ProjectiveScalarV89D3B232Pairs_eq :
    z180K30ProjectiveScalarV89D3B232Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B232UGroup z180K30ProjectiveScalarV89D3B232VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B232Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B232Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B232Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B232Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B232Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B232Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B232Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B232Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B232Audit :
    z180K30ProjectiveScalarV89D3B232Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B232Pairs,
    z180K30ProjectiveScalarV89D3B232Pair00Refuted,
    z180K30ProjectiveScalarV89D3B232Pair01Refuted,
    z180K30ProjectiveScalarV89D3B232Pair02Refuted,
    z180K30ProjectiveScalarV89D3B232Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B232Audit

end Fuglede.Z180K30ExceptionalRawV2
