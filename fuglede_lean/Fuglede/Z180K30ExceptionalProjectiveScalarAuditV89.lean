import Fuglede.Z180K30ExceptionalProjectiveAuditBlocksV89
import Fuglede.Z180K30ExceptionalProjectiveScalarZeroV89
import Mathlib.Tactic

/-!
# Deduplicated scalar audit for normalized K30 projective pairs

The finite search only needs coefficient zero.  If the complete trace is the
target, coefficient zero is `936`; otherwise a different scalar coefficient
already refutes the target.  The only pairs surviving this test are matched
against the bilateral, translation-normalized V87 catalogue.

The candidate lists are deduplicated at the audit boundary.  Membership is
unchanged, so the abstract normalization bridge continues to use the simpler
V88 enumeration while finite leaves replay each actual pair only once.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def normalizedProjectiveUniqueUChoicesV89 (divisor : Nat) : List RawSet :=
  (normalizedProjectiveUChoicesV88 divisor).eraseDups

def normalizedProjectiveUniqueVChoicesV89 (divisor : Nat) : List RawSet :=
  (normalizedProjectiveVChoicesV88 divisor).eraseDups

theorem normalizedProjectiveUChoicesV88_mem_unique_v89
    (divisor : Nat) (U : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor) :
    U ∈ normalizedProjectiveUniqueUChoicesV89 divisor := by
  simpa [normalizedProjectiveUniqueUChoicesV89] using hU

theorem normalizedProjectiveVChoicesV88_mem_unique_v89
    (divisor : Nat) (V : RawSet)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor) :
    V ∈ normalizedProjectiveUniqueVChoicesV89 divisor := by
  simpa [normalizedProjectiveUniqueVChoicesV89] using hV

/-- Divisor-first filtering prevents a positive scalar leaf from expanding
irrelevant witness bodies.  The resulting entry still carries its certified
V87 shard, so semantics can be handed to the existing global theorem. -/
def normalizedLiteralShardWitnessesForDivisorV89 (divisor : Nat) :
    List (CertifiedLiteralExceptionalWitnessShardV87 ×
      LiteralExceptionalPairWitnessV87) :=
  (z180K30ExceptionalLiteralWitnessShardsV87.filter fun shard =>
    shard.divisor == divisor).flatMap fun shard =>
      (shard.witnesses.filter fun witness =>
        decide (0 ∈ witness.U) && decide (0 ∈ witness.V)).map fun witness =>
          (shard, witness)

def normalizedLiteralWitnessSearchForDivisorB_v89
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  (normalizedLiteralShardWitnessesForDivisorV89 divisor).any
    (literalWitnessMatchesProjectivePairB_v88 divisor pair)

theorem normalizedLiteralWitnessSearchForDivisorB_v89_semantics
    (divisor : Nat) (pair : RawSet × RawSet)
    (hsearch :
      normalizedLiteralWitnessSearchForDivisorB_v89 divisor pair = true) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  rw [normalizedLiteralWitnessSearchForDivisorB_v89] at hsearch
  rcases List.any_eq_true.mp hsearch with ⟨entry, hentry, hmatches⟩
  have hentryGlobal : entry ∈ normalizedLiteralShardWitnessesV88 := by
    rw [normalizedLiteralShardWitnessesForDivisorV89] at hentry
    rcases List.mem_flatMap.mp hentry with
      ⟨shard, hshardFiltered, hentryShard⟩
    have hshard : shard ∈ z180K30ExceptionalLiteralWitnessShardsV87 :=
      (List.mem_filter.mp hshardFiltered).1
    rw [normalizedLiteralShardWitnessesV88]
    exact List.mem_flatMap.mpr ⟨shard, hshard, hentryShard⟩
  apply normalizedLiteralWitnessSearchB_v88_semantics divisor pair
  rw [normalizedLiteralWitnessSearchB_v88]
  exact List.any_eq_true.mpr ⟨entry, hentryGlobal, hmatches⟩

/-- The implication checked by every forward scalar leaf. -/
def normalizedProjectiveScalarForwardCoveredB_v89
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  !(gramTraceScalarZeroV89 pair.1 pair.2 == 936) ||
    normalizedLiteralWitnessSearchForDivisorB_v89 divisor pair

/-- The same implication for the reversed trace orientation. -/
def normalizedProjectiveScalarReverseCoveredB_v89
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  !(gramTraceScalarZeroV89 pair.2 pair.1 == 936) ||
    normalizedLiteralWitnessSearchForDivisorB_v89 divisor pair

def normalizedProjectiveScalarBothCoveredB_v89
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  normalizedProjectiveScalarForwardCoveredB_v89 divisor pair &&
    normalizedProjectiveScalarReverseCoveredB_v89 divisor pair

theorem normalizedProjectiveScalarForwardCoveredB_v89_semantics
    (divisor : Nat) (pair : RawSet × RawSet)
    (haudit :
      normalizedProjectiveScalarForwardCoveredB_v89 divisor pair = true)
    (htrace : gramTraceSquare pair.1 pair.2 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  apply normalizedLiteralWitnessSearchForDivisorB_v89_semantics divisor pair
  have hscalar : gramTraceScalarZeroV89 pair.1 pair.2 = 936 := by
    rw [gramTraceScalarZeroV89_eq_getD, htrace]
    simp [scalarCoeff]
  simpa [normalizedProjectiveScalarForwardCoveredB_v89,
    hscalar] using haudit

theorem normalizedProjectiveScalarReverseCoveredB_v89_semantics
    (divisor : Nat) (pair : RawSet × RawSet)
    (haudit :
      normalizedProjectiveScalarReverseCoveredB_v89 divisor pair = true)
    (htrace : gramTraceSquare pair.2 pair.1 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  apply normalizedLiteralWitnessSearchForDivisorB_v89_semantics divisor pair
  have hscalar : gramTraceScalarZeroV89 pair.2 pair.1 = 936 := by
    rw [gramTraceScalarZeroV89_eq_getD, htrace]
    simp [scalarCoeff]
  simpa [normalizedProjectiveScalarReverseCoveredB_v89,
    hscalar] using haudit

def normalizedProjectiveScalarUBlockV89
    (divisor blockCount blockIndex : Nat) : List RawSet :=
  (normalizedProjectiveUniqueUChoicesV89 divisor).filter fun U =>
    normalizedProjectiveRawSetKeyV89 U % blockCount == blockIndex

def normalizedProjectiveScalarVBlockV89
    (divisor blockCount blockIndex : Nat) : List RawSet :=
  (normalizedProjectiveUniqueVChoicesV89 divisor).filter fun V =>
    normalizedProjectiveRawSetKeyV89 V % blockCount == blockIndex

def normalizedProjectivePairsByScalarGridV89
    (divisor uBlockCount uBlockIndex vBlockCount vBlockIndex : Nat) :
    List (RawSet × RawSet) :=
  (normalizedProjectiveScalarVBlockV89
      divisor vBlockCount vBlockIndex).flatMap fun V =>
    (normalizedProjectiveScalarUBlockV89
      divisor uBlockCount uBlockIndex).map fun U => (U, V)

def normalizedProjectiveScalarGridAuditB_v89
    (divisor uBlockCount uBlockIndex vBlockCount vBlockIndex : Nat) : Bool :=
  (normalizedProjectivePairsByScalarGridV89 divisor
    uBlockCount uBlockIndex vBlockCount vBlockIndex).all
      (normalizedProjectiveScalarBothCoveredB_v89 divisor)

theorem normalizedProjectivePairsV88_mem_scalarGrid_v89
    (divisor uBlockCount vBlockCount : Nat)
    (huCount : 0 < uBlockCount) (hvCount : 0 < vBlockCount)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor) :
    (U, V) ∈ normalizedProjectivePairsByScalarGridV89 divisor
      uBlockCount (normalizedProjectiveRawSetKeyV89 U % uBlockCount)
      vBlockCount (normalizedProjectiveRawSetKeyV89 V % vBlockCount) := by
  rw [normalizedProjectivePairsByScalarGridV89]
  apply List.mem_flatMap.mpr
  refine ⟨V, ?_, ?_⟩
  · rw [normalizedProjectiveScalarVBlockV89, List.mem_filter]
    exact ⟨normalizedProjectiveVChoicesV88_mem_unique_v89 divisor V hV,
      by simp [Nat.mod_lt _ hvCount]⟩
  · apply List.mem_map.mpr
    refine ⟨U, ?_, rfl⟩
    rw [normalizedProjectiveScalarUBlockV89, List.mem_filter]
    exact ⟨normalizedProjectiveUChoicesV88_mem_unique_v89 divisor U hU,
      by simp [Nat.mod_lt _ huCount]⟩

theorem normalizedProjectiveScalarGridForwardAuditB_v89_semantics
    (divisor uBlockCount uBlockIndex vBlockCount vBlockIndex : Nat)
    (haudit : normalizedProjectiveScalarGridAuditB_v89 divisor
      uBlockCount uBlockIndex vBlockCount vBlockIndex = true)
    (pair : RawSet × RawSet)
    (hpair : pair ∈ normalizedProjectivePairsByScalarGridV89 divisor
      uBlockCount uBlockIndex vBlockCount vBlockIndex)
    (htrace : gramTraceSquare pair.1 pair.2 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  have hboth := (List.all_eq_true.mp haudit) pair hpair
  simp only [normalizedProjectiveScalarBothCoveredB_v89,
    Bool.and_eq_true] at hboth
  exact normalizedProjectiveScalarForwardCoveredB_v89_semantics
    divisor pair hboth.1 htrace

theorem normalizedProjectiveScalarGridReverseAuditB_v89_semantics
    (divisor uBlockCount uBlockIndex vBlockCount vBlockIndex : Nat)
    (haudit : normalizedProjectiveScalarGridAuditB_v89 divisor
      uBlockCount uBlockIndex vBlockCount vBlockIndex = true)
    (pair : RawSet × RawSet)
    (hpair : pair ∈ normalizedProjectivePairsByScalarGridV89 divisor
      uBlockCount uBlockIndex vBlockCount vBlockIndex)
    (htrace : gramTraceSquare pair.2 pair.1 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  have hboth := (List.all_eq_true.mp haudit) pair hpair
  simp only [normalizedProjectiveScalarBothCoveredB_v89,
    Bool.and_eq_true] at hboth
  exact normalizedProjectiveScalarReverseCoveredB_v89_semantics
    divisor pair hboth.2 htrace

theorem normalizedProjectiveForwardAudit_of_all_scalarGrid_v89
    (divisor uBlockCount vBlockCount : Nat)
    (huCount : 0 < uBlockCount) (hvCount : 0 < vBlockCount)
    (haudits : ∀ uBlockIndex, uBlockIndex < uBlockCount →
      ∀ vBlockIndex, vBlockIndex < vBlockCount →
        normalizedProjectiveScalarGridAuditB_v89 divisor
          uBlockCount uBlockIndex vBlockCount vBlockIndex = true)
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
  let uBlockIndex := normalizedProjectiveRawSetKeyV89 U % uBlockCount
  let vBlockIndex := normalizedProjectiveRawSetKeyV89 V % vBlockCount
  have huIndex : uBlockIndex < uBlockCount := Nat.mod_lt _ huCount
  have hvIndex : vBlockIndex < vBlockCount := Nat.mod_lt _ hvCount
  apply normalizedProjectiveScalarGridForwardAuditB_v89_semantics
    divisor uBlockCount uBlockIndex vBlockCount vBlockIndex
    (haudits uBlockIndex huIndex vBlockIndex hvIndex) (U, V)
  · simpa only [uBlockIndex, vBlockIndex] using
      normalizedProjectivePairsV88_mem_scalarGrid_v89 divisor
        uBlockCount vBlockCount huCount hvCount U V hU hV
  · exact htrace

theorem normalizedProjectiveReverseAudit_of_all_scalarGrid_v89
    (divisor uBlockCount vBlockCount : Nat)
    (huCount : 0 < uBlockCount) (hvCount : 0 < vBlockCount)
    (haudits : ∀ uBlockIndex, uBlockIndex < uBlockCount →
      ∀ vBlockIndex, vBlockIndex < vBlockCount →
        normalizedProjectiveScalarGridAuditB_v89 divisor
          uBlockCount uBlockIndex vBlockCount vBlockIndex = true)
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
  let uBlockIndex := normalizedProjectiveRawSetKeyV89 U % uBlockCount
  let vBlockIndex := normalizedProjectiveRawSetKeyV89 V % vBlockCount
  have huIndex : uBlockIndex < uBlockCount := Nat.mod_lt _ huCount
  have hvIndex : vBlockIndex < vBlockCount := Nat.mod_lt _ hvCount
  apply normalizedProjectiveScalarGridReverseAuditB_v89_semantics
    divisor uBlockCount uBlockIndex vBlockCount vBlockIndex
    (haudits uBlockIndex huIndex vBlockIndex hvIndex) (U, V)
  · simpa only [uBlockIndex, vBlockIndex] using
      normalizedProjectivePairsV88_mem_scalarGrid_v89 divisor
        uBlockCount vBlockCount huCount hvCount U V hU hV
  · exact htrace

/-!
The final generated audit uses a one-dimensional hash of the actual pair.
Unlike a rectangular grid, this keeps all three divisors below one hundred
pairs per nonempty leaf with only 195 leaves total.  Filtering is performed
inside each `V` branch, so the full Cartesian product is never materialized.
-/

def normalizedProjectiveScalarPairKeyV89
    (pair : RawSet × RawSet) : Nat :=
  (65537 * normalizedProjectiveRawSetKeyV89 pair.1 +
    normalizedProjectiveRawSetKeyV89 pair.2) % 104729

def normalizedProjectivePairOccurrencesByScalarBlockV89
    (divisor blockCount blockIndex : Nat) : List (RawSet × RawSet) :=
  (normalizedProjectiveVChoicesV88 divisor).flatMap fun V =>
    ((normalizedProjectiveUChoicesV88 divisor).filter fun U =>
      normalizedProjectiveScalarPairKeyV89 (U, V) % blockCount ==
        blockIndex).map fun U => (U, V)

/-- Duplicates are removed only after the hash filter.  For the supported
divisors this means `eraseDups` sees at most 200 occurrences rather than the
full 4,622-entry `d = 6` U enumeration. -/
def normalizedProjectivePairsByScalarBlockV89
    (divisor blockCount blockIndex : Nat) : List (RawSet × RawSet) :=
  (normalizedProjectivePairOccurrencesByScalarBlockV89
    divisor blockCount blockIndex).eraseDups

def normalizedProjectiveScalarBlockAuditB_v89
    (divisor blockCount blockIndex : Nat) : Bool :=
  (normalizedProjectivePairsByScalarBlockV89
    divisor blockCount blockIndex).all
      (normalizedProjectiveScalarBothCoveredB_v89 divisor)

/-- Adaptive leaf count used by the complete generated certificate. -/
def normalizedProjectiveScalarBlockCountV89 (divisor : Nat) : Nat :=
  if divisor = 3 then 56 else if divisor = 4 then 111 else 28

/-- Abstract audit boundary consumed by the normalization theorem.  The
generated aggregate supplies this proposition after all 195 leaves replay. -/
def Z180K30NormalizedProjectiveScalarAuditV89 : Prop :=
  ∀ divisor : Nat,
    divisor = 3 ∨ divisor = 4 ∨ divisor = 6 →
    ∀ blockIndex : Nat,
      blockIndex < normalizedProjectiveScalarBlockCountV89 divisor →
      normalizedProjectiveScalarBlockAuditB_v89 divisor
        (normalizedProjectiveScalarBlockCountV89 divisor) blockIndex = true

theorem normalizedProjectiveScalarBlockCountV89_pos
    (divisor : Nat)
    (hsupported : divisor = 3 ∨ divisor = 4 ∨ divisor = 6) :
    0 < normalizedProjectiveScalarBlockCountV89 divisor := by
  rcases hsupported with rfl | rfl | rfl <;>
    decide

theorem normalizedProjectivePairsV88_mem_scalarBlock_v89
    (divisor blockCount : Nat) (hcount : 0 < blockCount)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor) :
    (U, V) ∈ normalizedProjectivePairsByScalarBlockV89 divisor blockCount
      (normalizedProjectiveScalarPairKeyV89 (U, V) % blockCount) := by
  rw [normalizedProjectivePairsByScalarBlockV89, List.mem_eraseDups,
    normalizedProjectivePairOccurrencesByScalarBlockV89]
  apply List.mem_flatMap.mpr
  refine ⟨V, hV, ?_⟩
  apply List.mem_map.mpr
  refine ⟨U, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨hU,
    by simp [Nat.mod_lt _ hcount]⟩

theorem normalizedProjectiveScalarBlockForwardAuditB_v89_semantics
    (divisor blockCount blockIndex : Nat)
    (haudit : normalizedProjectiveScalarBlockAuditB_v89
      divisor blockCount blockIndex = true)
    (pair : RawSet × RawSet)
    (hpair : pair ∈ normalizedProjectivePairsByScalarBlockV89
      divisor blockCount blockIndex)
    (htrace : gramTraceSquare pair.1 pair.2 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  have hboth := (List.all_eq_true.mp haudit) pair hpair
  simp only [normalizedProjectiveScalarBothCoveredB_v89,
    Bool.and_eq_true] at hboth
  exact normalizedProjectiveScalarForwardCoveredB_v89_semantics
    divisor pair hboth.1 htrace

theorem normalizedProjectiveScalarBlockReverseAuditB_v89_semantics
    (divisor blockCount blockIndex : Nat)
    (haudit : normalizedProjectiveScalarBlockAuditB_v89
      divisor blockCount blockIndex = true)
    (pair : RawSet × RawSet)
    (hpair : pair ∈ normalizedProjectivePairsByScalarBlockV89
      divisor blockCount blockIndex)
    (htrace : gramTraceSquare pair.2 pair.1 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  have hboth := (List.all_eq_true.mp haudit) pair hpair
  simp only [normalizedProjectiveScalarBothCoveredB_v89,
    Bool.and_eq_true] at hboth
  exact normalizedProjectiveScalarReverseCoveredB_v89_semantics
    divisor pair hboth.2 htrace

theorem normalizedProjectiveForwardAudit_of_all_scalarBlocks_v89
    (divisor blockCount : Nat) (hcount : 0 < blockCount)
    (haudits : ∀ blockIndex, blockIndex < blockCount →
      normalizedProjectiveScalarBlockAuditB_v89
        divisor blockCount blockIndex = true)
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
  let blockIndex :=
    normalizedProjectiveScalarPairKeyV89 (U, V) % blockCount
  have hindex : blockIndex < blockCount := Nat.mod_lt _ hcount
  exact normalizedProjectiveScalarBlockForwardAuditB_v89_semantics
    divisor blockCount blockIndex (haudits blockIndex hindex) (U, V)
      (by simpa only [blockIndex] using
        (normalizedProjectivePairsV88_mem_scalarBlock_v89
          divisor blockCount hcount U V hU hV))
      htrace

theorem normalizedProjectiveReverseAudit_of_all_scalarBlocks_v89
    (divisor blockCount : Nat) (hcount : 0 < blockCount)
    (haudits : ∀ blockIndex, blockIndex < blockCount →
      normalizedProjectiveScalarBlockAuditB_v89
        divisor blockCount blockIndex = true)
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
  let blockIndex :=
    normalizedProjectiveScalarPairKeyV89 (U, V) % blockCount
  have hindex : blockIndex < blockCount := Nat.mod_lt _ hcount
  exact normalizedProjectiveScalarBlockReverseAuditB_v89_semantics
    divisor blockCount blockIndex (haudits blockIndex hindex) (U, V)
      (by simpa only [blockIndex] using
        (normalizedProjectivePairsV88_mem_scalarBlock_v89
          divisor blockCount hcount U V hU hV))
      htrace

#print axioms normalizedProjectiveForwardAudit_of_all_scalarGrid_v89
#print axioms normalizedProjectiveReverseAudit_of_all_scalarGrid_v89
#print axioms normalizedProjectiveForwardAudit_of_all_scalarBlocks_v89
#print axioms normalizedProjectiveReverseAudit_of_all_scalarBlocks_v89

end Fuglede.Z180K30ExceptionalRawV2
