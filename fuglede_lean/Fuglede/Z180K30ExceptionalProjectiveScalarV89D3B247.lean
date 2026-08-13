import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B247UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B247VGroup : List RawSet :=
[
  [0, 3, 6, 15, 24, 33],
  [0, 3, 6, 15, 27, 30],
  [0, 3, 6, 15, 27, 33],
  [0, 3, 6, 15, 30, 33]
]

def z180K30ProjectiveScalarV89D3B247Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 15, 24, 33])
def z180K30ProjectiveScalarV89D3B247Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 15, 27, 30])
def z180K30ProjectiveScalarV89D3B247Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 15, 27, 33])
def z180K30ProjectiveScalarV89D3B247Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 3, 6, 15, 30, 33])

def z180K30ProjectiveScalarV89D3B247Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B247Pair00,
  z180K30ProjectiveScalarV89D3B247Pair01,
  z180K30ProjectiveScalarV89D3B247Pair02,
  z180K30ProjectiveScalarV89D3B247Pair03
]



theorem z180K30ProjectiveScalarV89D3B247Pairs_eq :
    z180K30ProjectiveScalarV89D3B247Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B247UGroup z180K30ProjectiveScalarV89D3B247VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B247Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B247Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B247Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B247Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B247Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B247Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B247Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B247Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B247Audit :
    z180K30ProjectiveScalarV89D3B247Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B247Pairs,
    z180K30ProjectiveScalarV89D3B247Pair00Refuted,
    z180K30ProjectiveScalarV89D3B247Pair01Refuted,
    z180K30ProjectiveScalarV89D3B247Pair02Refuted,
    z180K30ProjectiveScalarV89D3B247Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B247Audit

end Fuglede.Z180K30ExceptionalRawV2
