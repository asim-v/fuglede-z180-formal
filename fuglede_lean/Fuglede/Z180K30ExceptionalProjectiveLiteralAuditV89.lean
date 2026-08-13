import Fuglede.Z180K30ExceptionalProjectiveNormalizedCoreV88
import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Literal finite-audit interface for normalized K30 projective pairs

Generated leaves contain only their exact pairs.  A negative entry evaluates
coefficient zero in both trace orientations.  A positive entry carries exact
V87 shard and witness indices, so no leaf scans the global witness catalogue.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def normalizedProjectiveLiteralUniqueUChoicesV89 (divisor : Nat) : List RawSet :=
  (normalizedProjectiveUChoicesV88 divisor).eraseDups

def normalizedProjectiveLiteralUniqueVChoicesV89 (divisor : Nat) : List RawSet :=
  (normalizedProjectiveVChoicesV88 divisor).eraseDups

theorem normalizedProjectiveUChoicesV88_mem_literalUnique_v89
    (divisor : Nat) (U : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor) :
    U ∈ normalizedProjectiveLiteralUniqueUChoicesV89 divisor := by
  simpa [normalizedProjectiveLiteralUniqueUChoicesV89] using hU

theorem normalizedProjectiveVChoicesV88_mem_literalUnique_v89
    (divisor : Nat) (V : RawSet)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor) :
    V ∈ normalizedProjectiveLiteralUniqueVChoicesV89 divisor := by
  simpa [normalizedProjectiveLiteralUniqueVChoicesV89] using hV

structure NormalizedProjectiveExplicitWitnessLookupV89 where
  shardIndex : Nat
  witnessIndex : Nat
deriving DecidableEq

private def emptyLiteralExceptionalPairWitnessV89 :
    LiteralExceptionalPairWitnessV87 :=
  ⟨[], [], 0, 0, 0, 0, 0, 0⟩

private def emptyCertifiedLiteralExceptionalWitnessShardV89 :
    CertifiedLiteralExceptionalWitnessShardV87 where
  divisor := 3
  supported_divisor := Or.inl rfl
  witnesses := []
  verified := rfl

/-- Check one exact V87 location.  Bounds are part of the Boolean certificate,
so successful lookup semantics never depend on the `getD` defaults. -/
def normalizedProjectiveExplicitWitnessLookupB_v89
    (divisor : Nat) (pair : RawSet × RawSet)
    (lookup : NormalizedProjectiveExplicitWitnessLookupV89) : Bool :=
  let shard := z180K30ExceptionalLiteralWitnessShardsV87.getD
    lookup.shardIndex emptyCertifiedLiteralExceptionalWitnessShardV89
  let witness := shard.witnesses.getD
    lookup.witnessIndex emptyLiteralExceptionalPairWitnessV89
  decide (lookup.shardIndex <
      z180K30ExceptionalLiteralWitnessShardsV87.length) &&
    (decide (lookup.witnessIndex < shard.witnesses.length) &&
      literalWitnessMatchesProjectivePairB_v88 divisor pair (shard, witness))

theorem normalizedProjectiveExplicitWitnessLookupB_v89_semantics
    (divisor : Nat) (pair : RawSet × RawSet)
    (lookup : NormalizedProjectiveExplicitWitnessLookupV89)
    (hlookup :
      normalizedProjectiveExplicitWitnessLookupB_v89
        divisor pair lookup = true) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  let shard := z180K30ExceptionalLiteralWitnessShardsV87.getD
    lookup.shardIndex emptyCertifiedLiteralExceptionalWitnessShardV89
  let witness := shard.witnesses.getD
    lookup.witnessIndex emptyLiteralExceptionalPairWitnessV89
  change (decide (lookup.shardIndex <
      z180K30ExceptionalLiteralWitnessShardsV87.length) &&
    (decide (lookup.witnessIndex < shard.witnesses.length) &&
      literalWitnessMatchesProjectivePairB_v88
        divisor pair (shard, witness))) = true at hlookup
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hlookup
  have hshardEq : shard =
      z180K30ExceptionalLiteralWitnessShardsV87[lookup.shardIndex] := by
    exact List.getD_eq_getElem
      z180K30ExceptionalLiteralWitnessShardsV87
      emptyCertifiedLiteralExceptionalWitnessShardV89 hlookup.1
  have hshardMem : shard ∈ z180K30ExceptionalLiteralWitnessShardsV87 := by
    rw [hshardEq]
    exact List.getElem_mem _
  have hwitnessEq : witness = shard.witnesses[lookup.witnessIndex] := by
    exact List.getD_eq_getElem shard.witnesses
      emptyLiteralExceptionalPairWitnessV89 hlookup.2.1
  have hwitnessMem : witness ∈ shard.witnesses := by
    rw [hwitnessEq]
    exact List.getElem_mem _
  have hverified := (List.all_eq_true.mp shard.verified)
    witness hwitnessMem
  have hmatches := hlookup.2.2
  simp only [literalWitnessMatchesProjectivePairB_v88,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmatches
  have hgcd : differenceGcd witness.V = shard.divisor :=
    hmatches.2.2.1.trans hmatches.1.symm
  have hclasses : classCount witness.U (36 / shard.divisor) ≤ 2 := by
    simpa only [hmatches.1] using hmatches.2.2.2
  exact ⟨shard, hshardMem, witness, hwitnessMem,
    hmatches.2.1.1, hmatches.2.1.2, hmatches.1,
    hgcd, hclasses, hverified⟩

/-- Leaf-local implication.  Negative entries stop after two scalar tests;
positive entries inspect only their explicit V87 locations. -/
def normalizedProjectiveLiteralCoveredB_v89
    (divisor : Nat)
    (lookups : List NormalizedProjectiveExplicitWitnessLookupV89)
    (pair : RawSet × RawSet) : Bool :=
  normalizedProjectiveScalarBothRefutedB_v89 pair ||
    lookups.any (normalizedProjectiveExplicitWitnessLookupB_v89 divisor pair)

theorem normalizedProjectiveLiteralAudit_of_refutations_v89
    (divisor : Nat)
    (lookups : List NormalizedProjectiveExplicitWitnessLookupV89)
    (pairs : List (RawSet × RawSet))
    (hrefuted :
      pairs.all normalizedProjectiveScalarBothRefutedB_v89 = true) :
    pairs.all
      (normalizedProjectiveLiteralCoveredB_v89 divisor lookups) = true := by
  apply List.all_eq_true.mpr
  intro pair hpair
  have hrefutedPair := (List.all_eq_true.mp hrefuted) pair hpair
  simp [normalizedProjectiveLiteralCoveredB_v89, hrefutedPair]

theorem normalizedProjectiveLiteralCoveredB_v89_forward_semantics
    (divisor : Nat)
    (lookups : List NormalizedProjectiveExplicitWitnessLookupV89)
    (pair : RawSet × RawSet)
    (hcovered :
      normalizedProjectiveLiteralCoveredB_v89 divisor lookups pair = true)
    (htrace : gramTraceSquare pair.1 pair.2 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  simp only [normalizedProjectiveLiteralCoveredB_v89,
    Bool.or_eq_true] at hcovered
  rcases hcovered with hrefuted | hwitnessed
  · have hscalar : gramTraceScalarZeroV89 pair.1 pair.2 = 936 := by
      rw [gramTraceScalarZeroV89_eq_getD, htrace]
      simp [scalarCoeff]
    simp [normalizedProjectiveScalarBothRefutedB_v89, hscalar] at hrefuted
  · rcases List.any_eq_true.mp hwitnessed with
      ⟨lookup, hlookupMem, hlookup⟩
    exact normalizedProjectiveExplicitWitnessLookupB_v89_semantics
      divisor pair lookup hlookup

theorem normalizedProjectiveLiteralCoveredB_v89_reverse_semantics
    (divisor : Nat)
    (lookups : List NormalizedProjectiveExplicitWitnessLookupV89)
    (pair : RawSet × RawSet)
    (hcovered :
      normalizedProjectiveLiteralCoveredB_v89 divisor lookups pair = true)
    (htrace : gramTraceSquare pair.2 pair.1 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  simp only [normalizedProjectiveLiteralCoveredB_v89,
    Bool.or_eq_true] at hcovered
  rcases hcovered with hrefuted | hwitnessed
  · have hscalar : gramTraceScalarZeroV89 pair.2 pair.1 = 936 := by
      rw [gramTraceScalarZeroV89_eq_getD, htrace]
      simp [scalarCoeff]
    simp [normalizedProjectiveScalarBothRefutedB_v89, hscalar] at hrefuted
  · rcases List.any_eq_true.mp hwitnessed with
      ⟨lookup, hlookupMem, hlookup⟩
    exact normalizedProjectiveExplicitWitnessLookupB_v89_semantics
      divisor pair lookup hlookup

structure CertifiedNormalizedProjectiveLiteralAuditV89 (divisor : Nat) where
  uGroups : List (List RawSet)
  vGroups : List (List RawSet)
  lookupFor : Nat → Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
  uGroups_complete :
    uGroups.flatten = normalizedProjectiveLiteralUniqueUChoicesV89 divisor
  vGroups_complete :
    vGroups.flatten = normalizedProjectiveLiteralUniqueVChoicesV89 divisor
  audited :
    ∀ uIndex, uIndex < uGroups.length →
      ∀ vIndex, vIndex < vGroups.length →
        (normalizedProjectiveLiteralCartesianPairsV89
          (uGroups.getD uIndex []) (vGroups.getD vIndex [])).all
            (normalizedProjectiveLiteralCoveredB_v89 divisor
              (lookupFor uIndex vIndex)) = true

def Z180K30NormalizedProjectiveLiteralAuditV89 : Prop :=
  ∀ divisor : Nat,
    divisor = 3 ∨ divisor = 4 ∨ divisor = 6 →
      Nonempty (CertifiedNormalizedProjectiveLiteralAuditV89 divisor)

private theorem mem_getD_of_mem_flatten_v89
    {groups : List (List RawSet)} {set : RawSet}
    (hset : set ∈ groups.flatten) :
    ∃ index, ∃ hindex : index < groups.length,
      set ∈ groups.getD index [] := by
  rw [List.mem_flatten] at hset
  rcases hset with ⟨group, hgroup, hsetGroup⟩
  rcases List.mem_iff_getElem.mp hgroup with ⟨index, hindex, hget⟩
  refine ⟨index, hindex, ?_⟩
  rw [List.getD_eq_getElem groups [] hindex, hget]
  exact hsetGroup

private theorem pair_mem_literalCartesian_v89
    {U V : RawSet} {uGroup vGroup : List RawSet}
    (hU : U ∈ uGroup) (hV : V ∈ vGroup) :
    (U, V) ∈ normalizedProjectiveLiteralCartesianPairsV89
      uGroup vGroup := by
  rw [normalizedProjectiveLiteralCartesianPairsV89]
  apply List.mem_flatMap.mpr
  refine ⟨V, hV, ?_⟩
  exact List.mem_map.mpr ⟨U, hU, rfl⟩

theorem normalizedProjectiveForwardAudit_of_literalGroups_v89
    (divisor : Nat) (audit : CertifiedNormalizedProjectiveLiteralAuditV89 divisor)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor)
    (htrace : gramTraceSquare U V = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U U = true ∧ rawSetEqB witness.V V = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  have hUFlat : U ∈ audit.uGroups.flatten := by
    rw [audit.uGroups_complete]
    exact normalizedProjectiveUChoicesV88_mem_literalUnique_v89 divisor U hU
  have hVFlat : V ∈ audit.vGroups.flatten := by
    rw [audit.vGroups_complete]
    exact normalizedProjectiveVChoicesV88_mem_literalUnique_v89 divisor V hV
  rcases mem_getD_of_mem_flatten_v89 hUFlat with
    ⟨uIndex, huIndex, hUGroup⟩
  rcases mem_getD_of_mem_flatten_v89 hVFlat with
    ⟨vIndex, hvIndex, hVGroup⟩
  have hpair := pair_mem_literalCartesian_v89 hUGroup hVGroup
  have hcovered := (List.all_eq_true.mp
    (audit.audited uIndex huIndex vIndex hvIndex)) (U, V) hpair
  exact normalizedProjectiveLiteralCoveredB_v89_forward_semantics
    divisor (audit.lookupFor uIndex vIndex)
      (U, V) hcovered htrace

theorem normalizedProjectiveReverseAudit_of_literalGroups_v89
    (divisor : Nat) (audit : CertifiedNormalizedProjectiveLiteralAuditV89 divisor)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor)
    (htrace : gramTraceSquare V U = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U U = true ∧ rawSetEqB witness.V V = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  have hUFlat : U ∈ audit.uGroups.flatten := by
    rw [audit.uGroups_complete]
    exact normalizedProjectiveUChoicesV88_mem_literalUnique_v89 divisor U hU
  have hVFlat : V ∈ audit.vGroups.flatten := by
    rw [audit.vGroups_complete]
    exact normalizedProjectiveVChoicesV88_mem_literalUnique_v89 divisor V hV
  rcases mem_getD_of_mem_flatten_v89 hUFlat with
    ⟨uIndex, huIndex, hUGroup⟩
  rcases mem_getD_of_mem_flatten_v89 hVFlat with
    ⟨vIndex, hvIndex, hVGroup⟩
  have hpair := pair_mem_literalCartesian_v89 hUGroup hVGroup
  have hcovered := (List.all_eq_true.mp
    (audit.audited uIndex huIndex vIndex hvIndex)) (U, V) hpair
  exact normalizedProjectiveLiteralCoveredB_v89_reverse_semantics
    divisor (audit.lookupFor uIndex vIndex)
      (U, V) hcovered htrace

#print axioms normalizedProjectiveExplicitWitnessLookupB_v89_semantics
#print axioms normalizedProjectiveLiteralCoveredB_v89_forward_semantics
#print axioms normalizedProjectiveLiteralCoveredB_v89_reverse_semantics
#print axioms normalizedProjectiveForwardAudit_of_literalGroups_v89
#print axioms normalizedProjectiveReverseAudit_of_literalGroups_v89

end Fuglede.Z180K30ExceptionalRawV2
