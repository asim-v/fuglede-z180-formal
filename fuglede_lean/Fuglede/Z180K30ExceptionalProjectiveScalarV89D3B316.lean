import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveScalarV89D3B316UGroup : List RawSet :=
[
  [0, 11, 12, 23, 24, 35]
]

def z180K30ProjectiveScalarV89D3B316VGroup : List RawSet :=
[
  [0, 9, 12, 15, 18, 21],
  [0, 9, 12, 15, 18, 24],
  [0, 9, 12, 15, 18, 27],
  [0, 9, 12, 15, 18, 30]
]

def z180K30ProjectiveScalarV89D3B316Pair00 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 18, 21])
def z180K30ProjectiveScalarV89D3B316Pair01 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 18, 24])
def z180K30ProjectiveScalarV89D3B316Pair02 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 18, 27])
def z180K30ProjectiveScalarV89D3B316Pair03 : RawSet × RawSet := ([0, 11, 12, 23, 24, 35], [0, 9, 12, 15, 18, 30])

def z180K30ProjectiveScalarV89D3B316Pairs : List (RawSet × RawSet) :=
[
  z180K30ProjectiveScalarV89D3B316Pair00,
  z180K30ProjectiveScalarV89D3B316Pair01,
  z180K30ProjectiveScalarV89D3B316Pair02,
  z180K30ProjectiveScalarV89D3B316Pair03
]



theorem z180K30ProjectiveScalarV89D3B316Pairs_eq :
    z180K30ProjectiveScalarV89D3B316Pairs =
      normalizedProjectiveLiteralCartesianPairsV89
        z180K30ProjectiveScalarV89D3B316UGroup z180K30ProjectiveScalarV89D3B316VGroup := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B316Pair00Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B316Pair00 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B316Pair01Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B316Pair01 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B316Pair02Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B316Pair02 = true := by
  decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem z180K30ProjectiveScalarV89D3B316Pair03Refuted :
    normalizedProjectiveScalarBothRefutedB_v89 z180K30ProjectiveScalarV89D3B316Pair03 = true := by
  decide

theorem z180K30ProjectiveScalarV89D3B316Audit :
    z180K30ProjectiveScalarV89D3B316Pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true := by
  simp [z180K30ProjectiveScalarV89D3B316Pairs,
    z180K30ProjectiveScalarV89D3B316Pair00Refuted,
    z180K30ProjectiveScalarV89D3B316Pair01Refuted,
    z180K30ProjectiveScalarV89D3B316Pair02Refuted,
    z180K30ProjectiveScalarV89D3B316Pair03Refuted]

#print axioms z180K30ProjectiveScalarV89D3B316Audit

end Fuglede.Z180K30ExceptionalRawV2
