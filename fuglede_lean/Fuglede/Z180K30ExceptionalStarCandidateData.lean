import Fuglede.Z180K30ExceptionalStarCoordinateCoreV2

/-!
# Literal Gram-coordinate data for the seven non-H affine orbits

The candidate lists contain one representative for every distinct Gram
matrix occurring over the indicated column set.  The lightweight Boolean
audits below use only the one or two coefficients needed by the arithmetic
obstructions, rather than re-running the five-matrix search.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ExceptionalSixCosets : List RawSet :=
  [[0, 6, 12, 18, 24, 30], [1, 7, 13, 19, 25, 31],
   [2, 8, 14, 20, 26, 32], [3, 9, 15, 21, 27, 33],
   [4, 10, 16, 22, 28, 34], [5, 11, 17, 23, 29, 35]]

def z180K30ExceptionalOrbitTwoChoices : List RawSet :=
  [[0, 12, 15, 18, 30, 33], [0, 3, 15, 18, 21, 33],
   [0, 3, 6, 18, 21, 24], [1, 13, 16, 19, 31, 34],
   [1, 4, 16, 19, 22, 34], [1, 4, 7, 19, 22, 25],
   [10, 13, 16, 28, 31, 34], [11, 14, 17, 29, 32, 35],
   [2, 14, 17, 20, 32, 35], [2, 5, 17, 20, 23, 35],
   [2, 5, 8, 20, 23, 26], [3, 6, 9, 21, 24, 27],
   [4, 7, 10, 22, 25, 28], [5, 8, 11, 23, 26, 29],
   [6, 9, 12, 24, 27, 30], [7, 10, 13, 25, 28, 31],
   [8, 11, 14, 26, 29, 32], [9, 12, 15, 27, 30, 33]]

def z180K30ExceptionalOrbitFourChoices : List RawSet :=
  [[0, 10, 12, 22, 24, 34], [0, 2, 12, 14, 24, 26],
   [1, 11, 13, 23, 25, 35], [1, 3, 13, 15, 25, 27],
   [2, 4, 14, 16, 26, 28], [3, 5, 15, 17, 27, 29],
   [4, 6, 16, 18, 28, 30], [5, 7, 17, 19, 29, 31],
   [6, 8, 18, 20, 30, 32], [7, 9, 19, 21, 31, 33],
   [8, 10, 20, 22, 32, 34], [9, 11, 21, 23, 33, 35]]

def z180K30PmSixB (value : Int) : Bool :=
  value == 6 || value == (-6 : Int)

def z180K30PairTypeB (first second : Int) : Bool :=
  (first == 6 && second == 0) ||
  (first == (-6 : Int) && second == 6) ||
  (first == 0 && second == (-6 : Int))

def z180K30PmSixAuditB
    (choices : List RawSet) (V : RawSet) (entry coefficient : Nat) : Bool :=
  choices.all fun U =>
    z180K30PmSixB (gramCoefficientV2 (gram U V) entry coefficient)

def z180K30PairTypeAuditB
    (choices : List RawSet) (V : RawSet)
    (entry firstCoefficient secondCoefficient : Nat) : Bool :=
  choices.all fun U =>
    z180K30PairTypeB
      (gramCoefficientV2 (gram U V) entry firstCoefficient)
      (gramCoefficientV2 (gram U V) entry secondCoefficient)

set_option maxRecDepth 100000 in
theorem z180_k30_orbit_zero_pmSix_audit :
    z180K30PmSixAuditB z180K30ExceptionalSixCosets
      [0, 1, 12, 18, 24, 30] 3 0 = true := by decide

set_option maxRecDepth 100000 in
theorem z180_k30_orbit_one_pmSix_audit :
    z180K30PmSixAuditB z180K30ExceptionalSixCosets
      [0, 10, 12, 18, 24, 30] 3 0 = true := by decide

set_option maxRecDepth 100000 in
theorem z180_k30_orbit_two_pairType_audit :
    z180K30PairTypeAuditB z180K30ExceptionalOrbitTwoChoices
      [0, 10, 12, 22, 24, 34] 2 0 6 = true := by decide

set_option maxRecDepth 100000 in
theorem z180_k30_orbit_three_pmSix_audit :
    z180K30PmSixAuditB z180K30ExceptionalSixCosets
      [0, 12, 15, 18, 24, 30] 3 0 = true := by decide

set_option maxRecDepth 100000 in
theorem z180_k30_orbit_four_pmSix_audit :
    z180K30PmSixAuditB z180K30ExceptionalOrbitFourChoices
      [0, 12, 15, 18, 30, 33] 3 0 = true := by decide

set_option maxRecDepth 100000 in
theorem z180_k30_orbit_five_pmSix_audit :
    z180K30PmSixAuditB z180K30ExceptionalSixCosets
      [0, 12, 16, 18, 24, 30] 3 0 = true := by decide

set_option maxRecDepth 100000 in
theorem z180_k30_orbit_six_pmSix_audit :
    z180K30PmSixAuditB z180K30ExceptionalSixCosets
      [0, 12, 18, 21, 24, 30] 2 0 = true := by decide

#print axioms z180_k30_orbit_zero_pmSix_audit
#print axioms z180_k30_orbit_two_pairType_audit
#print axioms z180_k30_orbit_six_pmSix_audit

end Fuglede.Z180K30ExceptionalRawV2
