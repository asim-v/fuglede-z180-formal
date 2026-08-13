import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B342UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B342VGroup : List RawSet :=
[
  [0, 12, 24, 27, 30, 33],
  [0, 15, 18, 21, 24, 27],
  [0, 15, 18, 21, 24, 30],
  [0, 15, 18, 21, 24, 33]
]

def z180K30ProjectiveScalarV89D3B342Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 24, 27, 30, 33])
def z180K30ProjectiveScalarV89D3B342Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 18, 21, 24, 27])
def z180K30ProjectiveScalarV89D3B342Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 18, 21, 24, 30])
def z180K30ProjectiveScalarV89D3B342Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 15, 18, 21, 24, 33])

def z180K30ProjectiveScalarV89D3B342Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B342Pair00,
  z180K30ProjectiveScalarV89D3B342Pair01,
  z180K30ProjectiveScalarV89D3B342Pair02,
  z180K30ProjectiveScalarV89D3B342Pair03
]



theorem z180K30ProjectiveScalarV89D3B342Pairs_eq :
    z180K30ProjectiveScalarV89D3B342Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B342UGroup z180K30ProjectiveScalarV89D3B342VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B342Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B342Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B342Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B342Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B342Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B342Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B342Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B342Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B342Audit :
    z180K30ProjectiveScalarV89D3B342Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B342Pairs,
    z180K30ProjectiveScalarV89D3B342Pair00Refuted,
    z180K30ProjectiveScalarV89D3B342Pair01Refuted,
    z180K30ProjectiveScalarV89D3B342Pair02Refuted,
    z180K30ProjectiveScalarV89D3B342Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B342Audit

end Fuglede.Z180K30ExceptionalRawV2
