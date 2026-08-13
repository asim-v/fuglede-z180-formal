import Fuglede.Z180K30ExceptionalRawCoreV2
import Mathlib.Tactic

/-!
# Logical semantics of the exact K30 projective batches

The generated leaves record that the list of accepted-but-uncovered pairs is
empty.  This module turns that numerical field into the pointwise statement
needed by the exceptional catalogue proof.  It is independent of any
particular batch partition.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def pairCoveredByEightOrbitsB_v70Fix (pair : RawSet × RawSet) : Bool :=
  orbitCoveredB pair.1 && orbitCoveredB pair.2

theorem auditBatch_uncovered_zero_semantics_v70Fix
    (divisor vStart vCount pairStart pairCount : Nat)
    (hzero :
      (auditBatch divisor vStart vCount pairStart pairCount).uncovered = 0)
    (pair : RawSet × RawSet)
    (hmem : pair ∈ projectiveCandidateBatch
      divisor vStart vCount pairStart pairCount)
    (haccepted : exceptionalPairB pair.1 pair.2 = true) :
    pairCoveredByEightOrbitsB_v70Fix pair = true := by
  let candidates := projectiveCandidateBatch
    divisor vStart vCount pairStart pairCount
  let accepted := candidates.filter fun candidate =>
    exceptionalPairB candidate.1 candidate.2
  let uncovered := accepted.filter fun candidate =>
    !(orbitCoveredB candidate.1 && orbitCoveredB candidate.2)
  have huncoveredLength : uncovered.length = 0 := by
    simpa only [auditBatch, candidates, accepted, uncovered] using hzero
  by_contra hcovered
  have hcoveredFalse :
      orbitCoveredB pair.1 && orbitCoveredB pair.2 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    apply hcovered
    simpa only [pairCoveredByEightOrbitsB_v70Fix] using htrue
  have hbad :
      !(orbitCoveredB pair.1 && orbitCoveredB pair.2) = true := by
    simp only [hcoveredFalse, Bool.not_false]
  have hmemAccepted : pair ∈ accepted := by
    exact List.mem_filter.mpr ⟨hmem, haccepted⟩
  have hmemUncovered : pair ∈ uncovered := by
    exact List.mem_filter.mpr ⟨hmemAccepted, hbad⟩
  have hpositive : 0 < uncovered.length :=
    List.length_pos.mpr ⟨pair, hmemUncovered⟩
  omega

#print axioms auditBatch_uncovered_zero_semantics_v70Fix

end Fuglede.Z180K30ExceptionalRawV2
