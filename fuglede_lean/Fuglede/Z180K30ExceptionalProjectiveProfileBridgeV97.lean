import Fuglede.Z180K30ExceptionalProjectiveProfileCoreV97
import Mathlib.Tactic

/-!
# Semantic bridge from V97 profiles to the V89 scalar-audit boundary

The generated V97 DAG supplies profile membership, divisibility, 213 covered
cells, and exact witness locations.  This module turns those certificates into
the existing `Z180K30NormalizedProjectiveScalarAuditV89` proposition without
replaying the old pair leaves.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem mem_projectiveProfileMembersV97
    {profiles : List ProjectiveProfileClassV97} {U : RawSet}
    (hU : U ∈ projectiveProfileMembersV97 profiles) :
    ∃ uIndex, ∃ huIndex : uIndex < profiles.length,
      ∃ uMemberIndex,
        ∃ huMemberIndex : uMemberIndex <
          (profiles.getD uIndex ⟨[], []⟩).members.length,
          (profiles.getD uIndex ⟨[], []⟩).members.getD
            uMemberIndex [] = U := by
  rw [projectiveProfileMembersV97, List.mem_flatMap] at hU
  rcases hU with ⟨profileClass, hclass, hU⟩
  rcases List.mem_iff_getElem.mp hclass with ⟨uIndex, huIndex, hgetClass⟩
  subst profileClass
  rcases List.mem_iff_getElem.mp hU with
    ⟨uMemberIndex, huMemberIndex, hgetMember⟩
  refine ⟨uIndex, huIndex, uMemberIndex, ?_, ?_⟩
  · rw [List.getD_eq_getElem profiles ⟨[], []⟩ huIndex]
    exact huMemberIndex
  · rw [List.getD_eq_getElem profiles ⟨[], []⟩ huIndex]
    rw [List.getD_eq_getElem _ _ huMemberIndex]
    exact hgetMember

private theorem mem_projectiveVProfileMembersV97
    {profiles : List ProjectiveVProfileClassV97} {V : RawSet}
    (hV : V ∈ projectiveVProfileMembersV97 profiles) :
    ∃ vIndex, ∃ hvIndex : vIndex < profiles.length,
      ∃ vMemberIndex,
        ∃ hvMemberIndex : vMemberIndex <
          (profiles.getD vIndex ⟨[], []⟩).members.length,
          (profiles.getD vIndex ⟨[], []⟩).members.getD
            vMemberIndex [] = V := by
  rw [projectiveVProfileMembersV97, List.mem_flatMap] at hV
  rcases hV with ⟨profileClass, hclass, hV⟩
  rcases List.mem_iff_getElem.mp hclass with ⟨vIndex, hvIndex, hgetClass⟩
  subst profileClass
  rcases List.mem_iff_getElem.mp hV with
    ⟨vMemberIndex, hvMemberIndex, hgetMember⟩
  refine ⟨vIndex, hvIndex, vMemberIndex, ?_, ?_⟩
  · rw [List.getD_eq_getElem profiles ⟨[], []⟩ hvIndex]
    exact hvMemberIndex
  · rw [List.getD_eq_getElem profiles ⟨[], []⟩ hvIndex]
    rw [List.getD_eq_getElem _ _ hvMemberIndex]
    exact hgetMember

private theorem projectiveUProfile_eq_of_valid_v97
    (divisor : Nat) (profiles : List ProjectiveProfileClassV97)
    (hvalid : projectiveUProfilesValidB_v97 divisor profiles = true)
    (uIndex : Nat) (huIndex : uIndex < profiles.length)
    (U : RawSet)
    (hU : U ∈ (profiles.getD uIndex ⟨[], []⟩).members) :
    projectiveUProfileV97 divisor U =
      (profiles.getD uIndex ⟨[], []⟩).profile := by
  rw [projectiveUProfilesValidB_v97] at hvalid
  have hclassMem : profiles.getD uIndex ⟨[], []⟩ ∈ profiles := by
    rw [List.getD_eq_getElem profiles ⟨[], []⟩ huIndex]
    exact List.getElem_mem _
  have hclass := (List.all_eq_true.mp hvalid)
    (profiles.getD uIndex ⟨[], []⟩) hclassMem
  exact beq_iff_eq.mp ((List.all_eq_true.mp hclass) U hU)

private theorem projectiveVProfile_eq_of_valid_v97
    (divisor : Nat) (profiles : List ProjectiveVProfileClassV97)
    (hvalid : projectiveVProfilesValidB_v97 divisor profiles = true)
    (vIndex : Nat) (hvIndex : vIndex < profiles.length)
    (V : RawSet)
    (hV : V ∈ (profiles.getD vIndex ⟨[], []⟩).members) :
    projectiveVProfileV97 divisor V =
      (profiles.getD vIndex ⟨[], []⟩).profile := by
  rw [projectiveVProfilesValidB_v97] at hvalid
  have hclassMem : profiles.getD vIndex ⟨[], []⟩ ∈ profiles := by
    rw [List.getD_eq_getElem profiles ⟨[], []⟩ hvIndex]
    exact List.getElem_mem _
  have hclass := (List.all_eq_true.mp hvalid)
    (profiles.getD vIndex ⟨[], []⟩) hclassMem
  exact beq_iff_eq.mp ((List.all_eq_true.mp hclass) V hV)

private theorem projectiveSideDivisible_of_profiles_v97
    (divisor : Nat) (profiles : List ProjectiveVProfileClassV97)
    (hvalid : projectiveVProfilesDivisibleB_v97 divisor profiles = true)
    (vIndex : Nat) (hvIndex : vIndex < profiles.length)
    (V : RawSet)
    (hV : V ∈ (profiles.getD vIndex ⟨[], []⟩).members) :
    projectiveSideDivisibleV97 divisor V := by
  rw [projectiveVProfilesDivisibleB_v97] at hvalid
  have hclassMem : profiles.getD vIndex ⟨[], []⟩ ∈ profiles := by
    rw [List.getD_eq_getElem profiles ⟨[], []⟩ hvIndex]
    exact List.getElem_mem _
  have hclass := (List.all_eq_true.mp hvalid)
    (profiles.getD vIndex ⟨[], []⟩) hclassMem
  have hset := (List.all_eq_true.mp hclass) V hV
  simpa [projectiveSideDivisibleB_v97, projectiveSideDivisibleV97,
    List.all_eq_true, decide_eq_true_eq] using hset

private theorem projectiveProfileMemberWitnessed_search_v97
    (divisor : Nat)
    (uProfiles : List ProjectiveProfileClassV97)
    (vProfiles : List ProjectiveVProfileClassV97)
    (lookups : List ProjectiveProfileWitnessLookupV97)
    (uIndex vIndex uMemberIndex vMemberIndex : Nat)
    (hwitnessed : projectiveProfileMemberWitnessedB_v97 divisor
      uProfiles vProfiles lookups uIndex vIndex
      uMemberIndex vMemberIndex = true) :
    normalizedLiteralWitnessSearchForDivisorB_v89 divisor
      ((uProfiles.getD uIndex ⟨[], []⟩).members.getD uMemberIndex [],
       (vProfiles.getD vIndex ⟨[], []⟩).members.getD
        vMemberIndex []) = true := by
  rw [projectiveProfileMemberWitnessedB_v97] at hwitnessed
  rcases List.any_eq_true.mp hwitnessed with
    ⟨lookup, _hlookupMem, hlookup⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hlookup
  have huIndex := hlookup.1.1.1.1
  have hvIndex := hlookup.1.1.1.2
  have huMember := hlookup.1.1.2
  have hvMember := hlookup.1.2
  have hlookupB := hlookup.2
  rw [← huIndex, ← hvIndex, ← huMember, ← hvMember]
  let U := (uProfiles.getD lookup.uProfileIndex ⟨[], []⟩).members.getD
    lookup.uMemberIndex []
  let V := (vProfiles.getD lookup.vProfileIndex ⟨[], []⟩).members.getD
    lookup.vMemberIndex []
  let shard := z180K30ExceptionalLiteralWitnessShardsV87.getD
    lookup.shardIndex projectiveProfileEmptyWitnessShardV97
  let witness := shard.witnesses.getD
    lookup.witnessIndex projectiveProfileEmptyWitnessV97
  change (decide (lookup.shardIndex <
      z180K30ExceptionalLiteralWitnessShardsV87.length) &&
    (decide (lookup.witnessIndex < shard.witnesses.length) &&
      ((decide (0 ∈ witness.U) && decide (0 ∈ witness.V)) &&
        literalWitnessMatchesProjectivePairB_v88
          divisor (U, V) (shard, witness)))) = true at hlookupB
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hlookupB
  have hshardEq : shard =
      z180K30ExceptionalLiteralWitnessShardsV87[lookup.shardIndex] :=
    List.getD_eq_getElem _ _ hlookupB.1
  have hshardMem : shard ∈ z180K30ExceptionalLiteralWitnessShardsV87 := by
    rw [hshardEq]
    exact List.getElem_mem _
  have hwitnessEq : witness =
      shard.witnesses[lookup.witnessIndex] :=
    List.getD_eq_getElem _ _ hlookupB.2.1
  have hwitnessMem : witness ∈ shard.witnesses := by
    rw [hwitnessEq]
    exact List.getElem_mem _
  have hmatchBool := hlookupB.2.2.2
  have hmatches := hmatchBool
  simp only [literalWitnessMatchesProjectivePairB_v88,
    Bool.and_eq_true, beq_iff_eq] at hmatches
  rw [normalizedLiteralWitnessSearchForDivisorB_v89]
  apply List.any_eq_true.mpr
  refine ⟨(shard, witness), ?_, hmatchBool⟩
  rw [normalizedLiteralShardWitnessesForDivisorV89]
  apply List.mem_flatMap.mpr
  refine ⟨shard, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨hshardMem, beq_iff_eq.mpr hmatches.1⟩
  · apply List.mem_map.mpr
    refine ⟨witness, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨hwitnessMem, by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hlookupB.2.2.1⟩

private theorem profile_cell_covered_v97
    (divisor : Nat)
    (audit : CertifiedNormalizedProjectiveProfileAuditV97 divisor)
    (uIndex : Nat) (huIndex : uIndex < audit.uProfiles.length)
    (vIndex : Nat) (hvIndex : vIndex < audit.vProfiles.length) :
    projectiveProfileCellCoveredB_v97 divisor
      audit.uProfiles audit.vProfiles (audit.lookupFor uIndex vIndex)
      uIndex vIndex = true := by
  have hcovered := audit.cells_covered
  rw [projectiveProfileAllCellsCoveredB_v97] at hcovered
  have huRange : uIndex ∈ List.range audit.uProfiles.length :=
    List.mem_range.mpr huIndex
  have huAll := (List.all_eq_true.mp hcovered) uIndex huRange
  exact (List.all_eq_true.mp huAll) vIndex (List.mem_range.mpr hvIndex)

theorem normalizedProjectiveScalarBothCovered_of_profileAudit_v97
    (divisor : Nat) (hdivisor : 0 < divisor)
    (audit : CertifiedNormalizedProjectiveProfileAuditV97 divisor)
    (U V : RawSet)
    (hU : U ∈ normalizedProjectiveUChoicesV88 divisor)
    (hV : V ∈ normalizedProjectiveVChoicesV88 divisor) :
    normalizedProjectiveScalarBothCoveredB_v89 divisor (U, V) = true := by
  have hUUnique : U ∈ normalizedProjectiveUniqueUChoicesV89 divisor :=
    normalizedProjectiveUChoicesV88_mem_unique_v89 divisor U hU
  have hVUnique : V ∈ normalizedProjectiveUniqueVChoicesV89 divisor :=
    normalizedProjectiveVChoicesV88_mem_unique_v89 divisor V hV
  have hUMembers : U ∈ projectiveProfileMembersV97 audit.uProfiles := by
    exact (List.Perm.mem_iff audit.uMembers_complete).mpr hUUnique
  have hVMembers : V ∈ projectiveVProfileMembersV97 audit.vProfiles := by
    exact (List.Perm.mem_iff audit.vMembers_complete).mpr hVUnique
  rcases mem_projectiveProfileMembersV97 hUMembers with
    ⟨uIndex, huIndex, uMemberIndex, huMemberIndex, hUGet⟩
  rcases mem_projectiveVProfileMembersV97 hVMembers with
    ⟨vIndex, hvIndex, vMemberIndex, hvMemberIndex, hVGet⟩
  have hUMem : U ∈
      (audit.uProfiles.getD uIndex ⟨[], []⟩).members := by
    rw [← hUGet]
    rw [List.getD_eq_getElem _ _ huMemberIndex]
    exact List.getElem_mem _
  have hVMem : V ∈
      (audit.vProfiles.getD vIndex ⟨[], []⟩).members := by
    rw [← hVGet]
    rw [List.getD_eq_getElem _ _ hvMemberIndex]
    exact List.getElem_mem _
  have hUProfile := projectiveUProfile_eq_of_valid_v97 divisor
    audit.uProfiles audit.uProfiles_valid uIndex huIndex U hUMem
  have hVProfile := projectiveVProfile_eq_of_valid_v97 divisor
    audit.vProfiles audit.vProfiles_valid vIndex hvIndex V hVMem
  have hVDivisible := projectiveSideDivisible_of_profiles_v97 divisor
    audit.vProfiles audit.vProfiles_divisible vIndex hvIndex V hVMem
  have hscalar : gramTraceScalarZeroV89 U V =
      projectiveProfileCellV97 audit.uProfiles audit.vProfiles
        uIndex vIndex := by
    calc
      gramTraceScalarZeroV89 U V =
          projectiveProfileDotV97
            (projectiveUProfileV97 divisor U)
            (projectiveVProfileV97 divisor V) :=
        gramTraceScalarZeroV89_eq_projectiveProfileDot_v97
          divisor hdivisor U V hVDivisible
      _ = projectiveProfileCellV97 audit.uProfiles audit.vProfiles
          uIndex vIndex := by
        simp only [projectiveProfileCellV97, hUProfile, hVProfile]
  have hcell := profile_cell_covered_v97 divisor audit
    uIndex huIndex vIndex hvIndex
  simp only [projectiveProfileCellCoveredB_v97, Bool.or_eq_true] at hcell
  rcases hcell with hrefuted | hwitnessed
  · have hcellNe : projectiveProfileCellV97
        audit.uProfiles audit.vProfiles uIndex vIndex ≠ 936 := by
      intro heq
      simp [projectiveProfileCellRefutedB_v97, heq] at hrefuted
    have hforwardNe : gramTraceScalarZeroV89 U V ≠ 936 := by
      rw [hscalar]
      exact hcellNe
    have hreverseNe : gramTraceScalarZeroV89 V U ≠ 936 := by
      rw [gramTraceScalarZeroV89_comm_v97]
      exact hforwardNe
    simp only [normalizedProjectiveScalarBothCoveredB_v89,
      Bool.and_eq_true]
    constructor
    · simp [normalizedProjectiveScalarForwardCoveredB_v89, hforwardNe]
    · simp [normalizedProjectiveScalarReverseCoveredB_v89, hreverseNe]
  · have huMemberRange : uMemberIndex ∈ List.range
        (audit.uProfiles.getD uIndex ⟨[], []⟩).members.length :=
      List.mem_range.mpr huMemberIndex
    have huAll := (List.all_eq_true.mp hwitnessed)
      uMemberIndex huMemberRange
    have hvMemberRange : vMemberIndex ∈ List.range
        (audit.vProfiles.getD vIndex ⟨[], []⟩).members.length :=
      List.mem_range.mpr hvMemberIndex
    have hmember := (List.all_eq_true.mp huAll)
      vMemberIndex hvMemberRange
    have hsearch := projectiveProfileMemberWitnessed_search_v97
      divisor audit.uProfiles audit.vProfiles
      (audit.lookupFor uIndex vIndex) uIndex vIndex
      uMemberIndex vMemberIndex hmember
    rw [hUGet, hVGet] at hsearch
    simp only [normalizedProjectiveScalarBothCoveredB_v89,
      Bool.and_eq_true]
    constructor
    · simp [normalizedProjectiveScalarForwardCoveredB_v89, hsearch]
    · simp [normalizedProjectiveScalarReverseCoveredB_v89, hsearch]

private theorem scalarBlock_pair_members_v97
    (divisor blockCount blockIndex : Nat) (pair : RawSet × RawSet)
    (hpair : pair ∈ normalizedProjectivePairsByScalarBlockV89
      divisor blockCount blockIndex) :
    pair.1 ∈ normalizedProjectiveUChoicesV88 divisor ∧
      pair.2 ∈ normalizedProjectiveVChoicesV88 divisor := by
  rw [normalizedProjectivePairsByScalarBlockV89,
    List.mem_eraseDups,
    normalizedProjectivePairOccurrencesByScalarBlockV89] at hpair
  rcases List.mem_flatMap.mp hpair with ⟨V, hV, hpair⟩
  rcases List.mem_map.mp hpair with ⟨U, hUFiltered, hpairEq⟩
  have hU := (List.mem_filter.mp hUFiltered).1
  cases hpairEq
  exact ⟨hU, hV⟩

theorem normalizedProjectiveProfileAudit_to_scalarAudit_v97
    (haudit : Z180K30NormalizedProjectiveProfileAuditV97) :
    Z180K30NormalizedProjectiveScalarAuditV89 := by
  intro divisor hsupported blockIndex hblockIndex
  have hdivisor : 0 < divisor := by
    rcases hsupported with rfl | rfl | rfl <;> decide
  rcases haudit divisor hsupported with ⟨audit⟩
  rw [normalizedProjectiveScalarBlockAuditB_v89]
  apply List.all_eq_true.mpr
  intro pair hpair
  have hmarginals := scalarBlock_pair_members_v97 divisor
    (normalizedProjectiveScalarBlockCountV89 divisor) blockIndex pair hpair
  exact normalizedProjectiveScalarBothCovered_of_profileAudit_v97
    divisor hdivisor audit pair.1 pair.2 hmarginals.1 hmarginals.2

#print axioms normalizedProjectiveScalarBothCovered_of_profileAudit_v97
#print axioms normalizedProjectiveProfileAudit_to_scalarAudit_v97

end Fuglede.Z180K30ExceptionalRawV2
