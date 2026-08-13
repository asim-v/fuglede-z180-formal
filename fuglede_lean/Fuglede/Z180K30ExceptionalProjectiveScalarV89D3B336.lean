import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B336UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B336VGroup : List RawSet :=
[
  [0, 12, 15, 21, 24, 27],
  [0, 12, 15, 21, 24, 30],
  [0, 12, 15, 21, 24, 33],
  [0, 12, 15, 21, 27, 30]
]

def z180K30ProjectiveScalarV89D3B336Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 21, 24, 27])
def z180K30ProjectiveScalarV89D3B336Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 21, 24, 30])
def z180K30ProjectiveScalarV89D3B336Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 21, 24, 33])
def z180K30ProjectiveScalarV89D3B336Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 12, 15, 21, 27, 30])

def z180K30ProjectiveScalarV89D3B336Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B336Pair00,
  z180K30ProjectiveScalarV89D3B336Pair01,
  z180K30ProjectiveScalarV89D3B336Pair02,
  z180K30ProjectiveScalarV89D3B336Pair03
]



theorem z180K30ProjectiveScalarV89D3B336Pairs_eq :
    z180K30ProjectiveScalarV89D3B336Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B336UGroup z180K30ProjectiveScalarV89D3B336VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B336Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B336Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B336Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B336Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B336Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B336Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B336Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B336Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B336Audit :
    z180K30ProjectiveScalarV89D3B336Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B336Pairs,
    z180K30ProjectiveScalarV89D3B336Pair00Refuted,
    z180K30ProjectiveScalarV89D3B336Pair01Refuted,
    z180K30ProjectiveScalarV89D3B336Pair02Refuted,
    z180K30ProjectiveScalarV89D3B336Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B336Audit

end Fuglede.Z180K30ExceptionalRawV2
