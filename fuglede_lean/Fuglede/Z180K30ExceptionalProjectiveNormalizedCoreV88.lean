import Fuglede.Z180K30ExceptionalLiteralWitnessAggregateV87
import Mathlib.Tactic

/-!
# Translation-normalized projective candidates for K30

Both marginals are translated independently so that they contain zero.  If
the projective side has difference gcd `d`, it is then a six-subset of the
nonzero multiples of `d`, together with zero.  The other side is a six-subset
of two residue classes modulo `36 / d`, again with zero distinguished.

This reduces the exact finite audit from 159516 ordered normal forms to a
small translation-normalized search.  The literal search itself is restricted
to the 222 V87 records whose two marginals contain zero.  No `drop` is used in
these definitions.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def normalizedProjectiveVChoicesV88 (divisor : Nat) : List RawSet :=
  (List.sublistsLen 6 (baseForDivisor divisor)).filter fun set =>
    decide (0 ∈ set)

def normalizedProjectiveClassSelectionsV88
    (divisor : Nat) : List (List Nat) :=
  ((List.range (36 / divisor)).map fun residue => [residue]) ++
    (List.range (36 / divisor)).flatMap fun first =>
      (List.range (36 / divisor)).map fun second => [first, second]

def normalizedProjectiveClassDomainV88
    (divisor : Nat) (selection : List Nat) : List RawPoint :=
  rawUniverse.filter fun point =>
    selection.any fun residue =>
      point.val % (36 / divisor) == residue

def normalizedProjectiveUChoicesForSelectionV88
    (divisor : Nat) (selection : List Nat) : List RawSet :=
  (List.sublistsLen 6
    (normalizedProjectiveClassDomainV88 divisor selection)).filter
      fun set => decide (0 ∈ set)

def normalizedProjectiveUChoicesV88 (divisor : Nat) : List RawSet :=
  (normalizedProjectiveClassSelectionsV88 divisor).flatMap
    (normalizedProjectiveUChoicesForSelectionV88 divisor)

def normalizedProjectivePairsV88
    (divisor : Nat) : List (RawSet × RawSet) :=
  (normalizedProjectiveVChoicesV88 divisor).flatMap fun V =>
    (normalizedProjectiveUChoicesV88 divisor).map fun U => (U, V)

def normalizedLiteralShardWitnessesV88 :
    List (CertifiedLiteralExceptionalWitnessShardV87 ×
      LiteralExceptionalPairWitnessV87) :=
  z180K30ExceptionalLiteralWitnessShardsV87.flatMap fun shard =>
    (shard.witnesses.filter fun witness =>
      decide (0 ∈ witness.U) && decide (0 ∈ witness.V)).map fun witness =>
        (shard, witness)

def literalWitnessMatchesProjectivePairB_v88
    (divisor : Nat)
    (pair : RawSet × RawSet)
    (entry : CertifiedLiteralExceptionalWitnessShardV87 ×
      LiteralExceptionalPairWitnessV87) : Bool :=
  (entry.1.divisor == divisor) &&
    ((rawSetEqB entry.2.U pair.1 && rawSetEqB entry.2.V pair.2) &&
      ((differenceGcd entry.2.V == divisor) &&
        decide (classCount entry.2.U (36 / divisor) ≤ 2)))

def normalizedLiteralWitnessSearchB_v88
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  normalizedLiteralShardWitnessesV88.any
    (literalWitnessMatchesProjectivePairB_v88 divisor pair)

def normalizedProjectiveTraceRefutedB_v88
    (pair : RawSet × RawSet) : Bool :=
  (List.range 12).any fun coordinate =>
    !((gramTraceSquare pair.1 pair.2).getD coordinate 0 ==
      (scalarCoeff 936).getD coordinate 0)

/-- Rejected candidates stop at their first mismatching cyclotomic
coefficient.  Only the 264 trace-positive normal forms search the explicit
witness list.  This is extensionally the same implication as comparing the
whole coefficient vector, but is much cheaper for the kernel to replay. -/
def normalizedProjectiveTraceCoveredB_v88
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  normalizedProjectiveTraceRefutedB_v88 pair ||
    normalizedLiteralWitnessSearchB_v88 divisor pair

/-- The second projective-cover orientation keeps the catalogue ordered as
`(two-class side, projective side)` but checks the trace in the opposite
order.  Auditing this implication directly avoids adding an algebraic
symmetry assumption to the normalization bridge. -/
def normalizedProjectiveReverseTraceCoveredB_v88
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  normalizedProjectiveTraceRefutedB_v88 (pair.2, pair.1) ||
    normalizedLiteralWitnessSearchB_v88 divisor pair

def normalizedProjectiveBothTracesCoveredB_v88
    (divisor : Nat) (pair : RawSet × RawSet) : Bool :=
  normalizedProjectiveTraceCoveredB_v88 divisor pair &&
    normalizedProjectiveReverseTraceCoveredB_v88 divisor pair

theorem normalizedLiteralWitnessSearchB_v88_semantics
    (divisor : Nat) (pair : RawSet × RawSet)
    (hsearch : normalizedLiteralWitnessSearchB_v88 divisor pair = true) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  rw [normalizedLiteralWitnessSearchB_v88] at hsearch
  rcases List.any_eq_true.mp hsearch with
    ⟨entry, hentry, hmatches⟩
  rw [normalizedLiteralShardWitnessesV88] at hentry
  rcases List.mem_flatMap.mp hentry with
    ⟨shard, hshard, hentryShard⟩
  rcases List.mem_map.mp hentryShard with
    ⟨witness, hwitnessFiltered, hentryEq⟩
  cases hentryEq
  have hwitnessShard : witness ∈ shard.witnesses :=
    (List.mem_filter.mp hwitnessFiltered).1
  have hraw := (List.all_eq_true.mp shard.verified)
    witness hwitnessShard
  simp only [literalWitnessMatchesProjectivePairB_v88,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hmatches
  have hgcd : differenceGcd witness.V = shard.divisor :=
    hmatches.2.2.1.trans hmatches.1.symm
  have hclasses : classCount witness.U (36 / shard.divisor) ≤ 2 := by
    simpa only [hmatches.1] using hmatches.2.2.2
  exact ⟨shard, hshard, witness, hwitnessShard,
    hmatches.2.1.1, hmatches.2.1.2, hmatches.1,
    hgcd, hclasses, hraw⟩

theorem normalizedProjectiveTraceCoveredB_v88_semantics
    (divisor : Nat) (pair : RawSet × RawSet)
    (haudit : normalizedProjectiveTraceCoveredB_v88 divisor pair = true)
    (htrace : gramTraceSquare pair.1 pair.2 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  have hsearch : normalizedLiteralWitnessSearchB_v88 divisor pair = true := by
    have hrefuted : normalizedProjectiveTraceRefutedB_v88 pair = false := by
      simp [normalizedProjectiveTraceRefutedB_v88, htrace]
    simpa [normalizedProjectiveTraceCoveredB_v88, hrefuted] using haudit
  exact normalizedLiteralWitnessSearchB_v88_semantics divisor pair hsearch

theorem normalizedProjectiveReverseTraceCoveredB_v88_semantics
    (divisor : Nat) (pair : RawSet × RawSet)
    (haudit : normalizedProjectiveReverseTraceCoveredB_v88 divisor pair = true)
    (htrace : gramTraceSquare pair.2 pair.1 = scalarCoeff 936) :
    ∃ shard ∈ z180K30ExceptionalLiteralWitnessShardsV87,
      ∃ witness ∈ shard.witnesses,
        rawSetEqB witness.U pair.1 = true ∧
        rawSetEqB witness.V pair.2 = true ∧
        shard.divisor = divisor ∧
        differenceGcd witness.V = shard.divisor ∧
        classCount witness.U (36 / shard.divisor) ≤ 2 ∧
        literalExceptionalPairWitnessB_v87 witness = true := by
  have hsearch : normalizedLiteralWitnessSearchB_v88 divisor pair = true := by
    have hrefuted :
        normalizedProjectiveTraceRefutedB_v88 (pair.2, pair.1) = false := by
      simp [normalizedProjectiveTraceRefutedB_v88, htrace]
    simpa [normalizedProjectiveReverseTraceCoveredB_v88, hrefuted] using haudit
  exact normalizedLiteralWitnessSearchB_v88_semantics divisor pair hsearch

#print axioms normalizedProjectiveTraceCoveredB_v88_semantics
#print axioms normalizedProjectiveReverseTraceCoveredB_v88_semantics

end Fuglede.Z180K30ExceptionalRawV2
