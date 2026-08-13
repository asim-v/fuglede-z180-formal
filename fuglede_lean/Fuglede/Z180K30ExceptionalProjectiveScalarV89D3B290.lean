import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B290UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B290VGroup : List RawSet :=
[
  [0, 6, 9, 15, 18, 24],
  [0, 6, 9, 15, 18, 27],
  [0, 6, 9, 15, 18, 30],
  [0, 6, 9, 15, 18, 33]
]

def z180K30ProjectiveScalarV89D3B290Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 15, 18, 24])
def z180K30ProjectiveScalarV89D3B290Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 15, 18, 27])
def z180K30ProjectiveScalarV89D3B290Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 15, 18, 30])
def z180K30ProjectiveScalarV89D3B290Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 15, 18, 33])

def z180K30ProjectiveScalarV89D3B290Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B290Pair00,
  z180K30ProjectiveScalarV89D3B290Pair01,
  z180K30ProjectiveScalarV89D3B290Pair02,
  z180K30ProjectiveScalarV89D3B290Pair03
]



theorem z180K30ProjectiveScalarV89D3B290Pairs_eq :
    z180K30ProjectiveScalarV89D3B290Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B290UGroup z180K30ProjectiveScalarV89D3B290VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B290Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B290Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B290Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B290Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B290Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B290Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B290Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B290Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B290Audit :
    z180K30ProjectiveScalarV89D3B290Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B290Pairs,
    z180K30ProjectiveScalarV89D3B290Pair00Refuted,
    z180K30ProjectiveScalarV89D3B290Pair01Refuted,
    z180K30ProjectiveScalarV89D3B290Pair02Refuted,
    z180K30ProjectiveScalarV89D3B290Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B290Audit

end Fuglede.Z180K30ExceptionalRawV2
