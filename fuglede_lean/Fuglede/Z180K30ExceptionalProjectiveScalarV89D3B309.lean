import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B309UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B309VGroup : List RawSet :=
[
  [0, 6, 15, 18, 27, 30],
  [0, 6, 15, 18, 27, 33],
  [0, 6, 15, 18, 30, 33],
  [0, 6, 15, 21, 24, 27]
]

def z180K30ProjectiveScalarV89D3B309Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 15, 18, 27, 30])
def z180K30ProjectiveScalarV89D3B309Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 15, 18, 27, 33])
def z180K30ProjectiveScalarV89D3B309Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 15, 18, 30, 33])
def z180K30ProjectiveScalarV89D3B309Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 6, 15, 21, 24, 27])

def z180K30ProjectiveScalarV89D3B309Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B309Pair00,
  z180K30ProjectiveScalarV89D3B309Pair01,
  z180K30ProjectiveScalarV89D3B309Pair02,
  z180K30ProjectiveScalarV89D3B309Pair03
]



theorem z180K30ProjectiveScalarV89D3B309Pairs_eq :
    z180K30ProjectiveScalarV89D3B309Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B309UGroup z180K30ProjectiveScalarV89D3B309VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B309Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B309Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B309Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B309Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B309Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B309Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B309Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B309Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B309Audit :
    z180K30ProjectiveScalarV89D3B309Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B309Pairs,
    z180K30ProjectiveScalarV89D3B309Pair00Refuted,
    z180K30ProjectiveScalarV89D3B309Pair01Refuted,
    z180K30ProjectiveScalarV89D3B309Pair02Refuted,
    z180K30ProjectiveScalarV89D3B309Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B309Audit

end Fuglede.Z180K30ExceptionalRawV2
