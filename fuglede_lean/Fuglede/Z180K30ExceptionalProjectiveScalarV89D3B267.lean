import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B267UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B267VGroup : List RawSet :=
[
  [0, 3, 12, 15, 18, 21],
  [0, 3, 12, 15, 18, 24],
  [0, 3, 12, 15, 18, 27],
  [0, 3, 12, 15, 18, 30]
]

def z180K30ProjectiveScalarV89D3B267Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 15, 18, 21])
def z180K30ProjectiveScalarV89D3B267Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 15, 18, 24])
def z180K30ProjectiveScalarV89D3B267Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 15, 18, 27])
def z180K30ProjectiveScalarV89D3B267Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 12, 15, 18, 30])

def z180K30ProjectiveScalarV89D3B267Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B267Pair00,
  z180K30ProjectiveScalarV89D3B267Pair01,
  z180K30ProjectiveScalarV89D3B267Pair02,
  z180K30ProjectiveScalarV89D3B267Pair03
]



theorem z180K30ProjectiveScalarV89D3B267Pairs_eq :
    z180K30ProjectiveScalarV89D3B267Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B267UGroup z180K30ProjectiveScalarV89D3B267VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B267Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B267Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B267Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B267Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B267Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B267Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B267Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B267Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B267Audit :
    z180K30ProjectiveScalarV89D3B267Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B267Pairs,
    z180K30ProjectiveScalarV89D3B267Pair00Refuted,
    z180K30ProjectiveScalarV89D3B267Pair01Refuted,
    z180K30ProjectiveScalarV89D3B267Pair02Refuted,
    z180K30ProjectiveScalarV89D3B267Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B267Audit

end Fuglede.Z180K30ExceptionalRawV2
