import Fuglede.Z180K30ExceptionalProjectiveNormalizedCoreV88
import Mathlib.Tactic

/-!
# Small deterministic blocks for the normalized K30 audit

The block key is used only to partition the already normalized candidates.
Every candidate belongs to the block indexed by its key modulo the declared
block count, so the aggregate proof loses no cases.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def normalizedProjectiveRawSetKeyV89 (set : RawSet) : Nat :=
  set.foldl (fun hash point => (37 * hash + point.val + 1) % 65521) 0

def normalizedProjectiveVBlockV89
    (divisor blockCount blockIndex : Nat) : List RawSet :=
  (normalizedProjectiveVChoicesV88 divisor).filter fun V =>
    normalizedProjectiveRawSetKeyV89 V % blockCount == blockIndex

def normalizedProjectiveUBlockV89
    (divisor blockCount blockIndex : Nat) : List RawSet :=
  (normalizedProjectiveUChoicesV88 divisor).filter fun U =>
    normalizedProjectiveRawSetKeyV89 U % blockCount == blockIndex

def normalizedProjectivePairsByVBlockV89
    (divisor blockCount blockIndex : Nat) : List (RawSet × RawSet) :=
  (normalizedProjectiveVBlockV89 divisor blockCount blockIndex).flatMap
    fun V => (normalizedProjectiveUChoicesV88 divisor).map fun U => (U, V)

def normalizedProjectivePairsByUBlockV89
    (divisor blockCount blockIndex : Nat) : List (RawSet × RawSet) :=
  (normalizedProjectiveVChoicesV88 divisor).flatMap fun V =>
    (normalizedProjectiveUBlockV89 divisor blockCount blockIndex).map
      fun U => (U, V)

def normalizedProjectiveUBlockAuditB_v89
    (divisor blockCount blockIndex : Nat) : Bool :=
  (normalizedProjectivePairsByUBlockV89 divisor blockCount blockIndex).all
    (normalizedProjectiveBothTracesCoveredB_v88 divisor)

theorem normalizedProjectiveVChoicesV88_mem_block_v89
    (divisor blockCount : Nat) (hcount : 0 < blockCount)
    (V : RawSet) (hV : V ∈ normalizedProjectiveVChoicesV88 divisor) :
    V ∈ normalizedProjectiveVBlockV89 divisor blockCount
      (normalizedProjectiveRawSetKeyV89 V % blockCount) := by
  rw [normalizedProjectiveVBlockV89, List.mem_filter]
  exact ⟨hV, by simp [Nat.mod_lt _ hcount]⟩

theorem normalizedProjectiveUChoicesV88_mem_block_v89
    (divisor blockCount : Nat) (hcount : 0 < blockCount)
    (U : RawSet) (hU : U ∈ normalizedProjectiveUChoicesV88 divisor) :
    U ∈ normalizedProjectiveUBlockV89 divisor blockCount
      (normalizedProjectiveRawSetKeyV89 U % blockCount) := by
  rw [normalizedProjectiveUBlockV89, List.mem_filter]
  exact ⟨hU, by simp [Nat.mod_lt _ hcount]⟩

theorem normalizedProjectivePairsV88_mem_vBlock_v89
    (divisor blockCount : Nat) (hcount : 0 < blockCount)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor) :
    (U, V) ∈ normalizedProjectivePairsByVBlockV89
      divisor blockCount (normalizedProjectiveRawSetKeyV89 V % blockCount) := by
  rw [normalizedProjectivePairsByVBlockV89]
  apply List.mem_flatMap.mpr
  exact ⟨V,
    normalizedProjectiveVChoicesV88_mem_block_v89
      divisor blockCount hcount V hV,
    List.mem_map.mpr ⟨U, hU, rfl⟩⟩

theorem normalizedProjectivePairsV88_mem_uBlock_v89
    (divisor blockCount : Nat) (hcount : 0 < blockCount)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor) :
    (U, V) ∈ normalizedProjectivePairsByUBlockV89
      divisor blockCount (normalizedProjectiveRawSetKeyV89 U % blockCount) := by
  rw [normalizedProjectivePairsByUBlockV89]
  apply List.mem_flatMap.mpr
  refine ⟨V, hV, ?_⟩
  exact List.mem_map.mpr ⟨U,
    normalizedProjectiveUChoicesV88_mem_block_v89
      divisor blockCount hcount U hU, rfl⟩

theorem normalizedProjectiveUBlockAuditB_v89_semantics
    (divisor blockCount blockIndex : Nat)
    (haudit : normalizedProjectiveUBlockAuditB_v89
      divisor blockCount blockIndex = true)
    (pair : RawSet × RawSet)
    (hpair : pair ∈ normalizedProjectivePairsByUBlockV89
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
  apply normalizedProjectiveTraceCoveredB_v88_semantics divisor pair
  · have hboth := (List.all_eq_true.mp haudit) pair hpair
    simp only [normalizedProjectiveBothTracesCoveredB_v88,
      Bool.and_eq_true] at hboth
    exact hboth.1
  · exact htrace

theorem normalizedProjectiveUBlockAuditB_v89_reverse_semantics
    (divisor blockCount blockIndex : Nat)
    (haudit : normalizedProjectiveUBlockAuditB_v89
      divisor blockCount blockIndex = true)
    (pair : RawSet × RawSet)
    (hpair : pair ∈ normalizedProjectivePairsByUBlockV89
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
  apply normalizedProjectiveReverseTraceCoveredB_v88_semantics divisor pair
  · have hboth := (List.all_eq_true.mp haudit) pair hpair
    simp only [normalizedProjectiveBothTracesCoveredB_v88,
      Bool.and_eq_true] at hboth
    exact hboth.2
  · exact htrace

theorem normalizedProjectiveAudit_of_all_uBlocks_v89
    (divisor blockCount : Nat) (hcount : 0 < blockCount)
    (haudits : ∀ blockIndex, blockIndex < blockCount →
      normalizedProjectiveUBlockAuditB_v89
        divisor blockCount blockIndex = true)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor)
    (htrace : gramTraceSquare U V = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U U = true ∧
        rawSetEqB witness.V V = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  let blockIndex := normalizedProjectiveRawSetKeyV89 U % blockCount
  have hindex : blockIndex < blockCount := Nat.mod_lt _ hcount
  exact normalizedProjectiveUBlockAuditB_v89_semantics
    divisor blockCount blockIndex (haudits blockIndex hindex) (U, V)
      (normalizedProjectivePairsV88_mem_uBlock_v89
        divisor blockCount hcount U V hU hV) htrace

theorem normalizedProjectiveReverseAudit_of_all_uBlocks_v89
    (divisor blockCount : Nat) (hcount : 0 < blockCount)
    (haudits : ∀ blockIndex, blockIndex < blockCount →
      normalizedProjectiveUBlockAuditB_v89
        divisor blockCount blockIndex = true)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor)
    (htrace : gramTraceSquare V U = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U U = true ∧
        rawSetEqB witness.V V = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  let blockIndex := normalizedProjectiveRawSetKeyV89 U % blockCount
  have hindex : blockIndex < blockCount := Nat.mod_lt _ hcount
  exact normalizedProjectiveUBlockAuditB_v89_reverse_semantics
    divisor blockCount blockIndex (haudits blockIndex hindex) (U, V)
      (normalizedProjectivePairsV88_mem_uBlock_v89
        divisor blockCount hcount U V hU hV) htrace

#print axioms normalizedProjectiveAudit_of_all_uBlocks_v89
#print axioms normalizedProjectiveReverseAudit_of_all_uBlocks_v89

end Fuglede.Z180K30ExceptionalRawV2
