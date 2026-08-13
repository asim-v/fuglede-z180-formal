import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B235UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B235VGroup : List RawSet :=
[
  [0, 3, 6, 9, 15, 33],
  [0, 3, 6, 9, 18, 21],
  [0, 3, 6, 9, 18, 24],
  [0, 3, 6, 9, 18, 27]
]

def z180K30ProjectiveScalarV89D3B235Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 15, 33])
def z180K30ProjectiveScalarV89D3B235Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 18, 21])
def z180K30ProjectiveScalarV89D3B235Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 18, 24])
def z180K30ProjectiveScalarV89D3B235Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 9, 18, 27])

def z180K30ProjectiveScalarV89D3B235Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B235Pair00,
  z180K30ProjectiveScalarV89D3B235Pair01,
  z180K30ProjectiveScalarV89D3B235Pair02,
  z180K30ProjectiveScalarV89D3B235Pair03
]



theorem z180K30ProjectiveScalarV89D3B235Pairs_eq :
    z180K30ProjectiveScalarV89D3B235Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B235UGroup z180K30ProjectiveScalarV89D3B235VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B235Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B235Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B235Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B235Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B235Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B235Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B235Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B235Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B235Audit :
    z180K30ProjectiveScalarV89D3B235Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B235Pairs,
    z180K30ProjectiveScalarV89D3B235Pair00Refuted,
    z180K30ProjectiveScalarV89D3B235Pair01Refuted,
    z180K30ProjectiveScalarV89D3B235Pair02Refuted,
    z180K30ProjectiveScalarV89D3B235Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B235Audit

end Fuglede.Z180K30ExceptionalRawV2
