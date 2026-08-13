import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B321UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B321VGroup : List RawSet :=
[
  [0, 9, 12, 18, 24, 30],
  [0, 9, 12, 18, 24, 33],
  [0, 9, 12, 18, 27, 30],
  [0, 9, 12, 18, 27, 33]
]

def z180K30ProjectiveScalarV89D3B321Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 18, 24, 30])
def z180K30ProjectiveScalarV89D3B321Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 18, 24, 33])
def z180K30ProjectiveScalarV89D3B321Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 18, 27, 30])
def z180K30ProjectiveScalarV89D3B321Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 18, 27, 33])

def z180K30ProjectiveScalarV89D3B321Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B321Pair00,
  z180K30ProjectiveScalarV89D3B321Pair01,
  z180K30ProjectiveScalarV89D3B321Pair02,
  z180K30ProjectiveScalarV89D3B321Pair03
]



theorem z180K30ProjectiveScalarV89D3B321Pairs_eq :
    z180K30ProjectiveScalarV89D3B321Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B321UGroup z180K30ProjectiveScalarV89D3B321VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B321Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B321Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B321Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B321Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B321Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B321Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B321Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B321Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B321Audit :
    z180K30ProjectiveScalarV89D3B321Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B321Pairs,
    z180K30ProjectiveScalarV89D3B321Pair00Refuted,
    z180K30ProjectiveScalarV89D3B321Pair01Refuted,
    z180K30ProjectiveScalarV89D3B321Pair02Refuted,
    z180K30ProjectiveScalarV89D3B321Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B321Audit

end Fuglede.Z180K30ExceptionalRawV2
