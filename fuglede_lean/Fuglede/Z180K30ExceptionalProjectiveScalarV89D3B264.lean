import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B264UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B264VGroup : List RawSet :=
[
  [0, 3, 9, 18, 27, 33],
  [0, 3, 9, 18, 30, 33],
  [0, 3, 9, 21, 24, 27],
  [0, 3, 9, 21, 24, 30]
]

def z180K30ProjectiveScalarV89D3B264Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 18, 27, 33])
def z180K30ProjectiveScalarV89D3B264Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 18, 30, 33])
def z180K30ProjectiveScalarV89D3B264Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 21, 24, 27])
def z180K30ProjectiveScalarV89D3B264Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 9, 21, 24, 30])

def z180K30ProjectiveScalarV89D3B264Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B264Pair00,
  z180K30ProjectiveScalarV89D3B264Pair01,
  z180K30ProjectiveScalarV89D3B264Pair02,
  z180K30ProjectiveScalarV89D3B264Pair03
]



theorem z180K30ProjectiveScalarV89D3B264Pairs_eq :
    z180K30ProjectiveScalarV89D3B264Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B264UGroup z180K30ProjectiveScalarV89D3B264VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B264Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B264Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B264Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B264Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B264Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B264Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B264Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B264Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B264Audit :
    z180K30ProjectiveScalarV89D3B264Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B264Pairs,
    z180K30ProjectiveScalarV89D3B264Pair00Refuted,
    z180K30ProjectiveScalarV89D3B264Pair01Refuted,
    z180K30ProjectiveScalarV89D3B264Pair02Refuted,
    z180K30ProjectiveScalarV89D3B264Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B264Audit

end Fuglede.Z180K30ExceptionalRawV2
