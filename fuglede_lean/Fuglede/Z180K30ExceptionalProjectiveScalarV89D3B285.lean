import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B285UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B285VGroup : List RawSet :=
[
  [0, 6, 9, 12, 15, 24],
  [0, 6, 9, 12, 15, 27],
  [0, 6, 9, 12, 15, 30],
  [0, 6, 9, 12, 15, 33]
]

def z180K30ProjectiveScalarV89D3B285Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 15, 24])
def z180K30ProjectiveScalarV89D3B285Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 15, 27])
def z180K30ProjectiveScalarV89D3B285Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 15, 30])
def z180K30ProjectiveScalarV89D3B285Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 9, 12, 15, 33])

def z180K30ProjectiveScalarV89D3B285Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B285Pair00,
  z180K30ProjectiveScalarV89D3B285Pair01,
  z180K30ProjectiveScalarV89D3B285Pair02,
  z180K30ProjectiveScalarV89D3B285Pair03
]



theorem z180K30ProjectiveScalarV89D3B285Pairs_eq :
    z180K30ProjectiveScalarV89D3B285Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B285UGroup z180K30ProjectiveScalarV89D3B285VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B285Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B285Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B285Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B285Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B285Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B285Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B285Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B285Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B285Audit :
    z180K30ProjectiveScalarV89D3B285Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B285Pairs,
    z180K30ProjectiveScalarV89D3B285Pair00Refuted,
    z180K30ProjectiveScalarV89D3B285Pair01Refuted,
    z180K30ProjectiveScalarV89D3B285Pair02Refuted,
    z180K30ProjectiveScalarV89D3B285Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B285Audit

end Fuglede.Z180K30ExceptionalRawV2
