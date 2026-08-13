import Fuglede.Z180K30ExceptionalProjectiveNormalizationFromAuditV89
import Fuglede.Z180K30ExceptionalProjectiveProfileBridgeV97
import Mathlib.Tactic

/-!
# Scalar-audit adapter for the V97 projective certificate

This isolated module connects the unchanged V89 scalar-audit boundary to the
normalization result.  It reuses the public scalar-block semantics, so no
literal Cartesian audit or global witness replay is introduced.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem normalized_trace_of_form_v97
    {U V : RawSet} (form : NormalizedProjectiveFormV89 U V)
    (htrace : gramTraceSquare U V = scalarCoeff 936) :
    gramTraceSquare form.normalizedU form.normalizedV = scalarCoeff 936 := by
  calc
    gramTraceSquare form.normalizedU form.normalizedV =
        gramTraceSquare
          (affineSet 1 form.uShift form.normalizedU) form.normalizedV :=
      (gramTraceSquare_translate_left_v88
        form.normalizedU form.normalizedV form.uShift).symm
    _ = gramTraceSquare
          (affineSet 1 form.uShift form.normalizedU)
          (affineSet 1 form.vShift form.normalizedV) :=
      (gramTraceSquare_translate_right_v88
        (affineSet 1 form.uShift form.normalizedU)
        form.normalizedV form.vShift).symm
    _ = gramTraceSquare U
          (affineSet 1 form.vShift form.normalizedV) :=
      (gramTraceSquare_eq_of_perm_left_v88 form.uPerm
        (affineSet 1 form.vShift form.normalizedV)).symm
    _ = gramTraceSquare U V :=
      (gramTraceSquare_eq_of_perm_right_v88 U form.vPerm).symm
    _ = scalarCoeff 936 := htrace

private theorem normalized_reverse_trace_of_form_v97
    {U V : RawSet} (form : NormalizedProjectiveFormV89 U V)
    (htrace : gramTraceSquare V U = scalarCoeff 936) :
    gramTraceSquare form.normalizedV form.normalizedU = scalarCoeff 936 := by
  calc
    gramTraceSquare form.normalizedV form.normalizedU =
        gramTraceSquare
          (affineSet 1 form.vShift form.normalizedV) form.normalizedU :=
      (gramTraceSquare_translate_left_v88
        form.normalizedV form.normalizedU form.vShift).symm
    _ = gramTraceSquare
          (affineSet 1 form.vShift form.normalizedV)
          (affineSet 1 form.uShift form.normalizedU) :=
      (gramTraceSquare_translate_right_v88
        (affineSet 1 form.vShift form.normalizedV)
        form.normalizedU form.uShift).symm
    _ = gramTraceSquare V
          (affineSet 1 form.uShift form.normalizedU) :=
      (gramTraceSquare_eq_of_perm_left_v88 form.vPerm
        (affineSet 1 form.uShift form.normalizedU)).symm
    _ = gramTraceSquare V U :=
      (gramTraceSquare_eq_of_perm_right_v88 V form.uPerm).symm
    _ = scalarCoeff 936 := htrace

private theorem witness_valid_components_v97
    (witness : LiteralExceptionalPairWitnessV87)
    (hverified : literalExceptionalPairWitnessB_v87 witness = true) :
    validSixSetB witness.U = true ∧ validSixSetB witness.V = true := by
  have hpair :=
    (literalExceptionalPairWitnessB_v87_semantics witness hverified).1
  simp only [exceptionalPairB, Bool.and_eq_true, beq_iff_eq] at hpair
  exact ⟨hpair.1.1.1, hpair.1.1.2⟩

private theorem normalizationWitness_of_scalar_form_v97
    {U V : RawSet} (form : NormalizedProjectiveFormV89 U V)
    (haudit : Z180K30NormalizedProjectiveScalarAuditV89)
    (htrace : gramTraceSquare U V = scalarCoeff 936) :
    Nonempty (ProjectiveLiteralNormalizationWitnessV86 U V) := by
  have hcount := normalizedProjectiveScalarBlockCountV89_pos
    form.divisor form.supported
  rcases normalizedProjectiveForwardAudit_of_all_scalarBlocks_v89
      form.divisor (normalizedProjectiveScalarBlockCountV89 form.divisor)
      hcount (haudit form.divisor form.supported)
      form.normalizedU form.normalizedV
      form.normalizedU_mem form.normalizedV_mem
      (normalized_trace_of_form_v97 form htrace) with
    ⟨shard, hshard, witness, hwitness, hrawU, hrawV,
      _hshardDivisor, hgcd, hclasses, hverified⟩
  have hwvalid := witness_valid_components_v97 witness hverified
  have hwPermU : witness.U.Perm form.normalizedU :=
    perm_of_rawSetEqB_of_valid_v88
      hwvalid.1 form.normalizedU_valid hrawU
  have hwPermV : witness.V.Perm form.normalizedV :=
    perm_of_rawSetEqB_of_valid_v88
      hwvalid.2 form.normalizedV_valid hrawV
  exact ⟨{
    shard := shard
    shard_mem := hshard
    canonical := witness
    canonical_mem := hwitness
    canonical_divisor := hgcd
    canonical_two_classes := hclasses
    uShift := form.uShift
    vShift := form.vShift
    orientation := Or.inl ⟨
      form.uPerm.trans (hwPermU.map (affinePoint 1 form.uShift)).symm,
      form.vPerm.trans (hwPermV.map (affinePoint 1 form.vShift)).symm⟩
  }⟩

private theorem normalizationWitness_of_scalar_reversed_form_v97
    {U V : RawSet} (form : NormalizedProjectiveFormV89 V U)
    (haudit : Z180K30NormalizedProjectiveScalarAuditV89)
    (htrace : gramTraceSquare U V = scalarCoeff 936) :
    Nonempty (ProjectiveLiteralNormalizationWitnessV86 U V) := by
  have hcount := normalizedProjectiveScalarBlockCountV89_pos
    form.divisor form.supported
  rcases normalizedProjectiveReverseAudit_of_all_scalarBlocks_v89
      form.divisor (normalizedProjectiveScalarBlockCountV89 form.divisor)
      hcount (haudit form.divisor form.supported)
      form.normalizedU form.normalizedV
      form.normalizedU_mem form.normalizedV_mem
      (normalized_reverse_trace_of_form_v97 form htrace) with
    ⟨shard, hshard, witness, hwitness, hrawU, hrawV,
      _hshardDivisor, hgcd, hclasses, hverified⟩
  have hwvalid := witness_valid_components_v97 witness hverified
  have hwPermU : witness.U.Perm form.normalizedU :=
    perm_of_rawSetEqB_of_valid_v88
      hwvalid.1 form.normalizedU_valid hrawU
  have hwPermV : witness.V.Perm form.normalizedV :=
    perm_of_rawSetEqB_of_valid_v88
      hwvalid.2 form.normalizedV_valid hrawV
  exact ⟨{
    shard := shard
    shard_mem := hshard
    canonical := witness
    canonical_mem := hwitness
    canonical_divisor := hgcd
    canonical_two_classes := hclasses
    uShift := form.uShift
    vShift := form.vShift
    orientation := Or.inr ⟨
      form.vPerm.trans (hwPermV.map (affinePoint 1 form.vShift)).symm,
      form.uPerm.trans (hwPermU.map (affinePoint 1 form.uShift)).symm⟩
  }⟩

theorem z180_k30_projectiveNormalization_of_scalarAudit_v97
    (haudit : Z180K30NormalizedProjectiveScalarAuditV89) :
    Fuglede.Z180K30ExceptionalProjectiveNormalizationV86 := by
  intro U V hpair
  have hcomponents :
      validSixSetB U = true ∧ validSixSetB V = true ∧
        rankTwoProjectiveCoverB U V = true ∧
        gramTraceSquare U V = scalarCoeff 936 := by
    simp only [exceptionalPairB, Bool.and_eq_true, beq_iff_eq] at hpair
    exact ⟨hpair.1.1.1, hpair.1.1.2, hpair.1.2, hpair.2⟩
  have hcover :
      classCount U (36 / differenceGcd V) ≤ 2 ∨
        classCount V (36 / differenceGcd U) ≤ 2 := by
    simpa only [rankTwoProjectiveCoverB, Bool.or_eq_true,
      decide_eq_true_eq] using hcomponents.2.2.1
  rcases hcover with hforward | hreverse
  · rcases exists_normalizedProjectiveFormV89
      U V hcomponents.1 hcomponents.2.1 hforward with ⟨form⟩
    exact normalizationWitness_of_scalar_form_v97
      form haudit hcomponents.2.2.2
  · rcases exists_normalizedProjectiveFormV89
      V U hcomponents.2.1 hcomponents.1 hreverse with ⟨form⟩
    exact normalizationWitness_of_scalar_reversed_form_v97
      form haudit hcomponents.2.2.2

#print axioms z180_k30_projectiveNormalization_of_scalarAudit_v97

end Fuglede.Z180K30ExceptionalRawV2
