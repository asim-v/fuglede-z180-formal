import Fuglede.Z180K30ExceptionalProjectiveAuditBlocksV89
import Mathlib.Tactic

/-!
# Two-dimensional blocks for the normalized K30 projective audit

The original V89 audit partitions only the two-class marginal.  In the
`d = 3` case a nonempty U block is still crossed with all 462 normalized
projective marginals.  Moreover, the coordinate-by-coordinate refutation in
V88 recomputes the complete Gram trace for every coordinate inspected.

This module is a source-only replacement interface for the finite leaves:

* hash blocks are imposed independently on U and V;
* one leaf contains only one Cartesian grid cell;
* the complete coefficient vector is computed once per orientation;
* forward and reverse orientations have separate Booleans, so a kernel leaf
  never has to replay both expensive traces at once.

The aggregation theorems below are exhaustive: every candidate is sent to
the cell determined by its two hash residues.  No positional slicing,
`choose`, `drop`, or `take` is used by the partition.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

/-- Equivalent to `normalizedProjectiveTraceCoveredB_v88`, but computes the
whole Gram trace once instead of recomputing it for as many as 12 coordinate
lookups. -/
def normalizedProjectiveTraceCoveredFastB_v89
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  !(gramTraceSquare pair.1 pair.2 == scalarCoeff 936) ||
    normalizedLiteralWitnessSearchB_v88 divisor pair

/-- Reverse-orientation companion of
`normalizedProjectiveTraceCoveredFastB_v89`. -/
def normalizedProjectiveReverseTraceCoveredFastB_v89
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  !(gramTraceSquare pair.2 pair.1 == scalarCoeff 936) ||
    normalizedLiteralWitnessSearchB_v88 divisor pair

theorem normalizedProjectiveTraceCoveredFastB_v89_semantics
    (divisor : Nat) (pair : RawSet × RawSet)
    (haudit : normalizedProjectiveTraceCoveredFastB_v89 divisor pair = true)
    (htrace : gramTraceSquare pair.1 pair.2 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  apply normalizedLiteralWitnessSearchB_v88_semantics divisor pair
  simpa [normalizedProjectiveTraceCoveredFastB_v89, htrace] using haudit

theorem normalizedProjectiveReverseTraceCoveredFastB_v89_semantics
    (divisor : Nat) (pair : RawSet × RawSet)
    (haudit :
      normalizedProjectiveReverseTraceCoveredFastB_v89 divisor pair = true)
    (htrace : gramTraceSquare pair.2 pair.1 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  apply normalizedLiteralWitnessSearchB_v88_semantics divisor pair
  simpa [normalizedProjectiveReverseTraceCoveredFastB_v89, htrace] using haudit

/-- One small Cartesian cell.  The two lists are filtered before their
product is formed. -/
def normalizedProjectivePairsByGridV89
    (divisor uBlockCount uBlockIndex vBlockCount vBlockIndex : Nat) :
    List (RawSet × RawSet) :=
  (normalizedProjectiveVBlockV89 divisor vBlockCount vBlockIndex).flatMap
    fun V =>
      (normalizedProjectiveUBlockV89 divisor uBlockCount uBlockIndex).map
        fun U => (U, V)

def normalizedProjectiveGridForwardAuditB_v89
    (divisor uBlockCount uBlockIndex vBlockCount vBlockIndex : Nat) : Bool :=
  (normalizedProjectivePairsByGridV89 divisor
    uBlockCount uBlockIndex vBlockCount vBlockIndex).all
      (normalizedProjectiveTraceCoveredFastB_v89 divisor)

def normalizedProjectiveGridReverseAuditB_v89
    (divisor uBlockCount uBlockIndex vBlockCount vBlockIndex : Nat) : Bool :=
  (normalizedProjectivePairsByGridV89 divisor
    uBlockCount uBlockIndex vBlockCount vBlockIndex).all
      (normalizedProjectiveReverseTraceCoveredFastB_v89 divisor)

theorem normalizedProjectivePairsV88_mem_grid_v89
    (divisor uBlockCount vBlockCount : Nat)
    (huCount : 0 < uBlockCount) (hvCount : 0 < vBlockCount)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor) :
    (U, V) ∈ normalizedProjectivePairsByGridV89 divisor
      uBlockCount (normalizedProjectiveRawSetKeyV89 U % uBlockCount)
      vBlockCount (normalizedProjectiveRawSetKeyV89 V % vBlockCount) := by
  rw [normalizedProjectivePairsByGridV89]
  apply List.mem_flatMap.mpr
  refine ⟨V,
    normalizedProjectiveVChoicesV88_mem_block_v89
      divisor vBlockCount hvCount V hV, ?_⟩
  exact List.mem_map.mpr ⟨U,
    normalizedProjectiveUChoicesV88_mem_block_v89
      divisor uBlockCount huCount U hU, rfl⟩

theorem normalizedProjectiveGridForwardAuditB_v89_semantics
    (divisor uBlockCount uBlockIndex vBlockCount vBlockIndex : Nat)
    (haudit : normalizedProjectiveGridForwardAuditB_v89 divisor
      uBlockCount uBlockIndex vBlockCount vBlockIndex = true)
    (pair : RawSet × RawSet)
    (hpair : pair ∈ normalizedProjectivePairsByGridV89 divisor
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
  apply normalizedProjectiveTraceCoveredFastB_v89_semantics divisor pair
  · exact (List.all_eq_true.mp haudit) pair hpair
  · exact htrace

theorem normalizedProjectiveGridReverseAuditB_v89_semantics
    (divisor uBlockCount uBlockIndex vBlockCount vBlockIndex : Nat)
    (haudit : normalizedProjectiveGridReverseAuditB_v89 divisor
      uBlockCount uBlockIndex vBlockCount vBlockIndex = true)
    (pair : RawSet × RawSet)
    (hpair : pair ∈ normalizedProjectivePairsByGridV89 divisor
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
  apply normalizedProjectiveReverseTraceCoveredFastB_v89_semantics
    divisor pair
  · exact (List.all_eq_true.mp haudit) pair hpair
  · exact htrace

theorem normalizedProjectiveForwardAudit_of_all_grid_v89
    (divisor uBlockCount vBlockCount : Nat)
    (huCount : 0 < uBlockCount) (hvCount : 0 < vBlockCount)
    (haudits : ∀ uBlockIndex, uBlockIndex < uBlockCount →
      ∀ vBlockIndex, vBlockIndex < vBlockCount →
        normalizedProjectiveGridForwardAuditB_v89 divisor
          uBlockCount uBlockIndex vBlockCount vBlockIndex = true)
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
  let uBlockIndex := normalizedProjectiveRawSetKeyV89 U % uBlockCount
  let vBlockIndex := normalizedProjectiveRawSetKeyV89 V % vBlockCount
  have huIndex : uBlockIndex < uBlockCount := Nat.mod_lt _ huCount
  have hvIndex : vBlockIndex < vBlockCount := Nat.mod_lt _ hvCount
  apply normalizedProjectiveGridForwardAuditB_v89_semantics
    divisor uBlockCount uBlockIndex vBlockCount vBlockIndex
    (haudits uBlockIndex huIndex vBlockIndex hvIndex) (U, V)
  · simpa only [uBlockIndex, vBlockIndex] using
      normalizedProjectivePairsV88_mem_grid_v89 divisor
        uBlockCount vBlockCount huCount hvCount U V hU hV
  · exact htrace

theorem normalizedProjectiveReverseAudit_of_all_grid_v89
    (divisor uBlockCount vBlockCount : Nat)
    (huCount : 0 < uBlockCount) (hvCount : 0 < vBlockCount)
    (haudits : ∀ uBlockIndex, uBlockIndex < uBlockCount →
      ∀ vBlockIndex, vBlockIndex < vBlockCount →
        normalizedProjectiveGridReverseAuditB_v89 divisor
          uBlockCount uBlockIndex vBlockCount vBlockIndex = true)
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
  let uBlockIndex := normalizedProjectiveRawSetKeyV89 U % uBlockCount
  let vBlockIndex := normalizedProjectiveRawSetKeyV89 V % vBlockCount
  have huIndex : uBlockIndex < uBlockCount := Nat.mod_lt _ huCount
  have hvIndex : vBlockIndex < vBlockCount := Nat.mod_lt _ hvCount
  apply normalizedProjectiveGridReverseAuditB_v89_semantics
    divisor uBlockCount uBlockIndex vBlockCount vBlockIndex
    (haudits uBlockIndex huIndex vBlockIndex hvIndex) (U, V)
  · simpa only [uBlockIndex, vBlockIndex] using
      normalizedProjectivePairsV88_mem_grid_v89 divisor
        uBlockCount vBlockCount huCount hvCount U V hU hV
  · exact htrace

#print axioms normalizedProjectiveForwardAudit_of_all_grid_v89
#print axioms normalizedProjectiveReverseAudit_of_all_grid_v89

end Fuglede.Z180K30ExceptionalRawV2
