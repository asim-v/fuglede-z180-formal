import Fuglede.Z180K30ExceptionalCatalogueKernelsV83
import Fuglede.Z180K30ExceptionalLiteralWitnessAggregateV87
import Fuglede.Z180K30ExceptionalProjectiveTransportV86

/-!
# Projective normalization boundary for K30 marginal coverage

The V87 leaves certify all 1584 normalized accepted pairs with explicit
affine witnesses.  This module consumes the independent V86 transport under
list permutation and translation, records the forced divisor interface
`d ∈ {3,4,6}`, and isolates the sole remaining classification statement:
every arbitrary accepted pair has such a witness.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

structure ProjectiveLiteralNormalizationWitnessV86
    (U V : RawSet) where
  shard : CertifiedLiteralExceptionalWitnessShardV87
  shard_mem :
    shard ∈ z180K30ExceptionalLiteralWitnessShardsV87
  canonical : LiteralExceptionalPairWitnessV87
  canonical_mem : canonical ∈ shard.witnesses
  canonical_divisor : differenceGcd canonical.V = shard.divisor
  canonical_two_classes :
    classCount canonical.U (36 / shard.divisor) ≤ 2
  uShift : RawPoint
  vShift : RawPoint
  orientation :
    (U.Perm (affineSet 1 uShift canonical.U) ∧
      V.Perm (affineSet 1 vShift canonical.V)) ∨
    (U.Perm (affineSet 1 vShift canonical.V) ∧
      V.Perm (affineSet 1 uShift canonical.U))

theorem ProjectiveLiteralNormalizationWitnessV86.supported_divisor
    {U V : RawSet} (w : ProjectiveLiteralNormalizationWitnessV86 U V) :
    w.shard.divisor = 3 ∨ w.shard.divisor = 4 ∨
      w.shard.divisor = 6 :=
  w.shard.supported_divisor

theorem ProjectiveLiteralNormalizationWitnessV86.differenceGcd_cases
    {U V : RawSet} (w : ProjectiveLiteralNormalizationWitnessV86 U V) :
    differenceGcd w.canonical.V = 3 ∨
      differenceGcd w.canonical.V = 4 ∨
      differenceGcd w.canonical.V = 6 := by
  rw [w.canonical_divisor]
  exact w.supported_divisor

theorem ProjectiveLiteralNormalizationWitnessV86.canonical_mem_global
    {U V : RawSet} (w : ProjectiveLiteralNormalizationWitnessV86 U V) :
    w.canonical ∈ z180K30ExceptionalLiteralWitnessesV87 := by
  rw [z180K30ExceptionalLiteralWitnessesV87]
  exact List.mem_flatMap.mpr ⟨w.shard, w.shard_mem, w.canonical_mem⟩

theorem ProjectiveLiteralNormalizationWitnessV86.canonical_semantics
    {U V : RawSet} (w : ProjectiveLiteralNormalizationWitnessV86 U V) :
    exceptionalPairB w.canonical.U w.canonical.V = true ∧
      orbitCoveredB w.canonical.U = true ∧
      orbitCoveredB w.canonical.V = true :=
  z180_k30_exceptional_literal_witness_semantics_v87
    w.canonical w.canonical_mem_global

theorem ProjectiveLiteralNormalizationWitnessV86.orbitCovered
    {U V : RawSet} (w : ProjectiveLiteralNormalizationWitnessV86 U V) :
    orbitCoveredB U = true ∧ orbitCoveredB V = true := by
  have hcanonical := w.canonical_semantics.2
  have htranslatedU :
      orbitCoveredB (affineSet 1 w.uShift w.canonical.U) = true :=
    orbitCoveredB_translate_v86 w.canonical.U w.uShift hcanonical.1
  have htranslatedV :
      orbitCoveredB (affineSet 1 w.vShift w.canonical.V) = true :=
    orbitCoveredB_translate_v86 w.canonical.V w.vShift hcanonical.2
  rcases w.orientation with ⟨hU, hV⟩ | ⟨hU, hV⟩
  · exact ⟨(orbitCoveredB_eq_of_perm_v86 hU).trans htranslatedU,
      (orbitCoveredB_eq_of_perm_v86 hV).trans htranslatedV⟩
  · exact ⟨(orbitCoveredB_eq_of_perm_v86 hU).trans htranslatedV,
      (orbitCoveredB_eq_of_perm_v86 hV).trans htranslatedU⟩

#print axioms ProjectiveLiteralNormalizationWitnessV86.orbitCovered

end Fuglede.Z180K30ExceptionalRawV2

namespace Fuglede

open Z180K30ExceptionalRawV2

def Z180K30ExceptionalProjectiveNormalizationV86 : Prop :=
  ∀ U V : RawSet, exceptionalPairB U V = true →
    Nonempty (ProjectiveLiteralNormalizationWitnessV86 U V)

theorem z180_k30_exceptional_marginalCoverage_of_projectiveNormalization_v86
    (hnormalize : Z180K30ExceptionalProjectiveNormalizationV86) :
    Z180K30ExceptionalMarginalCoverageV83 := by
  intro U V hpair
  rcases hnormalize U V hpair with ⟨w⟩
  exact w.orbitCovered

#print axioms z180_k30_exceptional_marginalCoverage_of_projectiveNormalization_v86

end Fuglede
