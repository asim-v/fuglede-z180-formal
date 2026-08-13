import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B249UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B249VGroup : List RawSet :=
[
  [0, 3, 6, 18, 24, 27],
  [0, 3, 6, 18, 24, 30],
  [0, 3, 6, 18, 24, 33],
  [0, 3, 6, 18, 27, 30]
]

def z180K30ProjectiveScalarV89D3B249Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 24, 27])
def z180K30ProjectiveScalarV89D3B249Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 24, 30])
def z180K30ProjectiveScalarV89D3B249Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 24, 33])
def z180K30ProjectiveScalarV89D3B249Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 18, 27, 30])

def z180K30ProjectiveScalarV89D3B249Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B249Pair00,
  z180K30ProjectiveScalarV89D3B249Pair01,
  z180K30ProjectiveScalarV89D3B249Pair02,
  z180K30ProjectiveScalarV89D3B249Pair03
]



theorem z180K30ProjectiveScalarV89D3B249Pairs_eq :
    z180K30ProjectiveScalarV89D3B249Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B249UGroup z180K30ProjectiveScalarV89D3B249VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B249Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B249Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B249Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B249Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B249Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B249Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B249Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B249Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B249Audit :
    z180K30ProjectiveScalarV89D3B249Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B249Pairs,
    z180K30ProjectiveScalarV89D3B249Pair00Refuted,
    z180K30ProjectiveScalarV89D3B249Pair01Refuted,
    z180K30ProjectiveScalarV89D3B249Pair02Refuted,
    z180K30ProjectiveScalarV89D3B249Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B249Audit

end Fuglede.Z180K30ExceptionalRawV2
