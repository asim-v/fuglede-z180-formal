import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B303UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B303VGroup : List RawSet :=
[
  [0, 6, 12, 18, 21, 33],
  [0, 6, 12, 18, 24, 27],
  [0, 6, 12, 18, 24, 30],
  [0, 6, 12, 18, 24, 33]
]

def z180K30ProjectiveScalarV89D3B303Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 18, 21, 33])
def z180K30ProjectiveScalarV89D3B303Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 18, 24, 27])
def z180K30ProjectiveScalarV89D3B303Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 18, 24, 30])
def z180K30ProjectiveScalarV89D3B303Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 12, 18, 24, 33])

def z180K30ProjectiveScalarV89D3B303Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B303Pair00,
  z180K30ProjectiveScalarV89D3B303Pair01,
  z180K30ProjectiveScalarV89D3B303Pair02,
  z180K30ProjectiveScalarV89D3B303Pair03
]



theorem z180K30ProjectiveScalarV89D3B303Pairs_eq :
    z180K30ProjectiveScalarV89D3B303Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B303UGroup z180K30ProjectiveScalarV89D3B303VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B303Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B303Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B303Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B303Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B303Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B303Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B303Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B303Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B303Audit :
    z180K30ProjectiveScalarV89D3B303Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B303Pairs,
    z180K30ProjectiveScalarV89D3B303Pair00Refuted,
    z180K30ProjectiveScalarV89D3B303Pair01Refuted,
    z180K30ProjectiveScalarV89D3B303Pair02Refuted,
    z180K30ProjectiveScalarV89D3B303Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B303Audit

end Fuglede.Z180K30ExceptionalRawV2
