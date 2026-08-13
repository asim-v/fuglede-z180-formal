import Fuglede.Z180K30ExceptionalStarCandidateData
import Fuglede.Z180K30ExceptionalStarArithmeticV4

/-!
# Propositional form of the exact non-H Gram-coordinate audits
-/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180K30PmSix_of_audit
    {choices : List RawSet} {V U : RawSet} {entry coefficient : Nat}
    (haudit : z180K30PmSixAuditB choices V entry coefficient = true)
    (hmem : U ∈ choices) :
    gramCoefficientV2 (gram U V) entry coefficient = 6 \/
      gramCoefficientV2 (gram U V) entry coefficient = -6 := by
  have hb := (List.all_eq_true.mp haudit) U hmem
  simpa only [z180K30PmSixB, Bool.or_eq_true, beq_iff_eq] using hb

theorem z180K30PairType_of_audit
    {choices : List RawSet} {V U : RawSet}
    {entry firstCoefficient secondCoefficient : Nat}
    (haudit : z180K30PairTypeAuditB choices V entry
      firstCoefficient secondCoefficient = true)
    (hmem : U ∈ choices) :
    (gramCoefficientV2 (gram U V) entry firstCoefficient = 6 /\
      gramCoefficientV2 (gram U V) entry secondCoefficient = 0) \/
    (gramCoefficientV2 (gram U V) entry firstCoefficient = -6 /\
      gramCoefficientV2 (gram U V) entry secondCoefficient = 6) \/
    (gramCoefficientV2 (gram U V) entry firstCoefficient = 0 /\
      gramCoefficientV2 (gram U V) entry secondCoefficient = -6) := by
  have hb := (List.all_eq_true.mp haudit) U hmem
  simpa only [z180K30PairTypeB, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] using hb

theorem z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit
    {choices : List RawSet} {V : RawSet} {entry coefficient : Nat}
    (haudit : z180K30PmSixAuditB choices V entry coefficient = true)
    (U : Fin 5 -> RawSet) (hmem : forall i, U i ∈ choices) :
    gramCoefficientV2 (gram (U 0) V) entry coefficient +
      gramCoefficientV2 (gram (U 1) V) entry coefficient +
      gramCoefficientV2 (gram (U 2) V) entry coefficient +
      gramCoefficientV2 (gram (U 3) V) entry coefficient +
      gramCoefficientV2 (gram (U 4) V) entry coefficient ≠ 0 := by
  apply Fuglede.z180_k30_five_pm_six_explicit
  · exact z180K30PmSix_of_audit haudit (hmem 0)
  · exact z180K30PmSix_of_audit haudit (hmem 1)
  · exact z180K30PmSix_of_audit haudit (hmem 2)
  · exact z180K30PmSix_of_audit haudit (hmem 3)
  · exact z180K30PmSix_of_audit haudit (hmem 4)

theorem z180_k30_no_fiveGram_coordinate_pair_sum_of_audit
    {choices : List RawSet} {V : RawSet}
    {entry firstCoefficient secondCoefficient : Nat}
    (haudit : z180K30PairTypeAuditB choices V entry
      firstCoefficient secondCoefficient = true)
    (U : Fin 5 -> RawSet) (hmem : forall i, U i ∈ choices) :
    (gramCoefficientV2 (gram (U 0) V) entry firstCoefficient +
      gramCoefficientV2 (gram (U 1) V) entry firstCoefficient +
      gramCoefficientV2 (gram (U 2) V) entry firstCoefficient +
      gramCoefficientV2 (gram (U 3) V) entry firstCoefficient +
      gramCoefficientV2 (gram (U 4) V) entry firstCoefficient ≠ 0) \/
    (gramCoefficientV2 (gram (U 0) V) entry secondCoefficient +
      gramCoefficientV2 (gram (U 1) V) entry secondCoefficient +
      gramCoefficientV2 (gram (U 2) V) entry secondCoefficient +
      gramCoefficientV2 (gram (U 3) V) entry secondCoefficient +
      gramCoefficientV2 (gram (U 4) V) entry secondCoefficient ≠ 0) := by
  apply Fuglede.z180_k30_five_gram_pair_types_explicit
  · exact z180K30PairType_of_audit haudit (hmem 0)
  · exact z180K30PairType_of_audit haudit (hmem 1)
  · exact z180K30PairType_of_audit haudit (hmem 2)
  · exact z180K30PairType_of_audit haudit (hmem 3)
  · exact z180K30PairType_of_audit haudit (hmem 4)

#print axioms z180_k30_no_fiveGram_coordinate_sum_of_pmSix_audit
#print axioms z180_k30_no_fiveGram_coordinate_pair_sum_of_audit

end Fuglede.Z180K30ExceptionalRawV2
