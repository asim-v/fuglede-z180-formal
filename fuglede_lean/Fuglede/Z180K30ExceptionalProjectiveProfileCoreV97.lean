import Fuglede.Z180K30ExceptionalProjectiveHistogramCoreV97
import Fuglede.Z180K30ExceptionalProjectiveLiteralAuditV89
import Fuglede.Z180K30ExceptionalProjectiveScalarAuditV89
import Mathlib.Tactic

/-!
# Profile interface for the compressed K30 projective audit

For a supported divisor `d`, normalized projective-side differences are
multiples of `d`.  A U profile stores scalar responses at those multiples; a V
profile is the sorted ordered-difference list, hence a canonical histogram.
Their evaluation is the exact scalar coefficient.  Generated certificates use
literal profile groups and exact V87 locations; no global pair enumeration is
performed here.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

abbrev ProjectiveUProfileV97 := List Int
abbrev ProjectiveVProfileV97 := List Nat

def projectiveUProfileV97 (divisor : Nat) (U : RawSet) :
    ProjectiveUProfileV97 :=
  (List.range 36).map fun projectiveDifference =>
    if projectiveDifference % divisor == 0 then
      (orderedDifferencesV97 U |>.map fun difference =>
        zetaScalarZeroV89 (difference * projectiveDifference)).sum
    else 0

def projectiveVProfileV97 (divisor : Nat) (V : RawSet) :
    ProjectiveVProfileV97 :=
  (orderedDifferencesV97 V).mergeSort
    (fun left right => decide (left ≤ right))

/-- Kernel-friendly certificate for a literal V profile.  Generated proofs
check only a 36-entry permutation and the literal's sortedness; they never
reduce `mergeSort`. -/
theorem projectiveVProfileV97_eq_of_perm_sorted
    (divisor : Nat) (V : RawSet) (profile : List Nat)
    (hperm : (orderedDifferencesV97 V).Perm profile)
    (hsorted : profile.SortedLE) :
    projectiveVProfileV97 divisor V = profile := by
  unfold projectiveVProfileV97
  exact List.Perm.eq_of_sortedLE List.sortedLE_mergeSort hsorted
    ((List.mergeSort_perm _ _).trans hperm)

def projectiveProfileDotV97
    (uProfile : ProjectiveUProfileV97)
    (vProfile : ProjectiveVProfileV97) : Int :=
  (vProfile.map fun difference => uProfile.getD difference 0).sum

def projectiveSideDivisibleV97 (divisor : Nat) (V : RawSet) : Prop :=
  ∀ difference ∈ orderedDifferencesV97 V, divisor ∣ difference

private theorem sum_map_sum_swap_profile_v97
    (left right : List Nat) (f : Nat → Nat → Int) :
    (left.map fun x => (right.map fun y => f x y).sum).sum =
      (right.map fun y => (left.map fun x => f x y).sum).sum := by
  induction left with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [List.sum_map_add]
      /-
      have hadd :
          (right.map fun y => f head y).sum +
              (right.map fun y =>
                (tail.map fun x => f x y).sum).sum =
            (right.map fun y =>
              f head y + (tail.map fun x => f x y).sum).sum := by
        induction right with
        | nil => simp
        | cons next rest ihRight =>
            simp only [List.map_cons, List.sum_cons] at ihRight ⊢
            omega
      exact hadd
      -/

theorem orderedDifferencesV97_lt
    (set : RawSet) (difference : Nat)
    (hdifference : difference ∈ orderedDifferencesV97 set) :
    difference < 36 := by
  rw [orderedDifferencesV97, List.mem_flatMap] at hdifference
  rcases hdifference with ⟨left, _hleft, hdifference⟩
  rw [List.mem_map] at hdifference
  rcases hdifference with ⟨right, _hright, rfl⟩
  exact Nat.mod_lt _ (by decide)

private theorem projectiveUProfileV97_getD
    (divisor : Nat) (U : RawSet) (difference : Nat)
    (hdifference : difference < 36) (hdivisible : divisor ∣ difference) :
    (projectiveUProfileV97 divisor U).getD difference 0 =
      (orderedDifferencesV97 U |>.map fun outer =>
        zetaScalarZeroV89 (outer * difference)).sum := by
  rw [List.getD_eq_getElem _ _ (by
    simpa [projectiveUProfileV97] using hdifference)]
  simp [projectiveUProfileV97, hdifference,
    Nat.mod_eq_zero_of_dvd hdivisible]

/-!
The compression lemma is deliberately isolated behind the precise divisibility
hypothesis.  The V profile is a sorted ordered-difference list: sorting makes
it a canonical histogram while `List.Perm.sum_eq` proves that no scalar term
is changed.
-/

theorem gramTraceScalarZeroV89_eq_projectiveProfileDot_v97
    (divisor : Nat) (hdivisor : 0 < divisor)
    (U V : RawSet)
    (hV : projectiveSideDivisibleV97 divisor V) :
    gramTraceScalarZeroV89 U V =
      projectiveProfileDotV97
        (projectiveUProfileV97 divisor U)
        (projectiveVProfileV97 divisor V) := by
  rw [gramTraceScalarZeroV89_eq_orderedDifferenceBilinear_v97]
  unfold orderedDifferenceBilinearV97 projectiveProfileDotV97
    projectiveVProfileV97
  rw [sum_map_sum_swap_profile_v97]
  let response : Nat → Int := fun difference =>
    (orderedDifferencesV97 U |>.map fun outer =>
      zetaScalarZeroV89 (outer * difference)).sum
  have hpointwise : ∀ difference ∈ orderedDifferencesV97 V,
      (projectiveUProfileV97 divisor U).getD difference 0 =
        response difference := by
    intro difference hdifference
    exact projectiveUProfileV97_getD divisor U difference
      (orderedDifferencesV97_lt V difference hdifference)
      (hV difference hdifference)
  have hperm := List.mergeSort_perm
    (orderedDifferencesV97 V) (fun left right => decide (left ≤ right))
  calc
    ((orderedDifferencesV97 V).map response).sum =
        ((projectiveVProfileV97 divisor V).map response).sum := by
      exact (hperm.map response).sum_eq.symm
    _ = ((projectiveVProfileV97 divisor V).map fun difference =>
          (projectiveUProfileV97 divisor U).getD difference 0).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro difference hdifference
      exact (projectiveUProfileV97_getD divisor U difference
        (orderedDifferencesV97_lt V difference
          ((List.Perm.mem_iff hperm).mp hdifference))
        (hV difference ((List.Perm.mem_iff hperm).mp hdifference))).symm

structure ProjectiveProfileClassV97 where
  profile : List Int
  members : List RawSet

structure ProjectiveVProfileClassV97 where
  profile : List Nat
  members : List RawSet

structure ProjectiveProfileWitnessLookupV97 where
  uProfileIndex : Nat
  vProfileIndex : Nat
  uMemberIndex : Nat
  vMemberIndex : Nat
  shardIndex : Nat
  witnessIndex : Nat
deriving DecidableEq

def projectiveProfileEmptyWitnessV97 :
    LiteralExceptionalPairWitnessV87 :=
  ⟨[], [], 0, 0, 0, 0, 0, 0⟩

def projectiveProfileEmptyWitnessShardV97 :
    CertifiedLiteralExceptionalWitnessShardV87 where
  divisor := 3
  supported_divisor := Or.inl rfl
  witnesses := []
  verified := rfl

def projectiveProfileCellV97
    (uProfiles : List ProjectiveProfileClassV97)
    (vProfiles : List ProjectiveVProfileClassV97)
    (uIndex vIndex : Nat) : Int :=
  projectiveProfileDotV97
    (uProfiles.getD uIndex ⟨[], []⟩).profile
    (vProfiles.getD vIndex ⟨[], []⟩).profile

def projectiveProfileCellRefutedB_v97
    (uProfiles : List ProjectiveProfileClassV97)
    (vProfiles : List ProjectiveVProfileClassV97)
    (uIndex vIndex : Nat) : Bool :=
  !(projectiveProfileCellV97 uProfiles vProfiles uIndex vIndex == 936)

def projectiveProfileLookupB_v97
    (divisor : Nat)
    (uProfiles : List ProjectiveProfileClassV97)
    (vProfiles : List ProjectiveVProfileClassV97)
    (lookup : ProjectiveProfileWitnessLookupV97) : Bool :=
  let U := (uProfiles.getD lookup.uProfileIndex ⟨[], []⟩).members.getD
    lookup.uMemberIndex []
  let V := (vProfiles.getD lookup.vProfileIndex ⟨[], []⟩).members.getD
    lookup.vMemberIndex []
  let shard := z180K30ExceptionalLiteralWitnessShardsV87.getD
    lookup.shardIndex projectiveProfileEmptyWitnessShardV97
  let witness := shard.witnesses.getD
    lookup.witnessIndex projectiveProfileEmptyWitnessV97
  decide (lookup.shardIndex <
      z180K30ExceptionalLiteralWitnessShardsV87.length) &&
    (decide (lookup.witnessIndex < shard.witnesses.length) &&
      ((decide (0 ∈ witness.U) && decide (0 ∈ witness.V)) &&
        literalWitnessMatchesProjectivePairB_v88
          divisor (U, V) (shard, witness)))

def projectiveProfileMemberWitnessedB_v97
    (divisor : Nat)
    (uProfiles : List ProjectiveProfileClassV97)
    (vProfiles : List ProjectiveVProfileClassV97)
    (lookups : List ProjectiveProfileWitnessLookupV97)
    (uIndex vIndex uMemberIndex vMemberIndex : Nat) : Bool :=
  lookups.any fun lookup =>
    lookup.uProfileIndex == uIndex &&
    lookup.vProfileIndex == vIndex &&
    lookup.uMemberIndex == uMemberIndex &&
    lookup.vMemberIndex == vMemberIndex &&
    projectiveProfileLookupB_v97 divisor uProfiles vProfiles lookup

def projectiveProfileCellCoveredB_v97
    (divisor : Nat)
    (uProfiles : List ProjectiveProfileClassV97)
    (vProfiles : List ProjectiveVProfileClassV97)
    (lookups : List ProjectiveProfileWitnessLookupV97)
    (uIndex vIndex : Nat) : Bool :=
  projectiveProfileCellRefutedB_v97 uProfiles vProfiles uIndex vIndex ||
    (List.range
      (uProfiles.getD uIndex ⟨[], []⟩).members.length).all
      (fun uMemberIndex =>
        (List.range
          (vProfiles.getD vIndex ⟨[], []⟩).members.length).all
          (fun vMemberIndex =>
            projectiveProfileMemberWitnessedB_v97 divisor
              uProfiles vProfiles lookups uIndex vIndex
              uMemberIndex vMemberIndex))

def projectiveProfileAllCellsCoveredB_v97
    (divisor : Nat)
    (uProfiles : List ProjectiveProfileClassV97)
    (vProfiles : List ProjectiveVProfileClassV97)
    (lookupFor : Nat → Nat →
      List ProjectiveProfileWitnessLookupV97) : Bool :=
  (List.range uProfiles.length).all fun uIndex =>
    (List.range vProfiles.length).all fun vIndex =>
      projectiveProfileCellCoveredB_v97 divisor uProfiles vProfiles
        (lookupFor uIndex vIndex) uIndex vIndex

def projectiveUProfilesValidB_v97
    (divisor : Nat) (profiles : List ProjectiveProfileClassV97) : Bool :=
  profiles.all fun profileClass =>
    profileClass.members.all fun U =>
      projectiveUProfileV97 divisor U == profileClass.profile

def projectiveVProfilesValidB_v97
    (divisor : Nat) (profiles : List ProjectiveVProfileClassV97) : Bool :=
  profiles.all fun profileClass =>
    profileClass.members.all fun V =>
      projectiveVProfileV97 divisor V == profileClass.profile

def projectiveSideDivisibleB_v97 (divisor : Nat) (V : RawSet) : Bool :=
  (orderedDifferencesV97 V).all fun difference =>
    decide (divisor ∣ difference)

def projectiveVProfilesDivisibleB_v97
    (divisor : Nat) (profiles : List ProjectiveVProfileClassV97) : Bool :=
  profiles.all fun profileClass =>
    profileClass.members.all (projectiveSideDivisibleB_v97 divisor)

def projectiveProfileMembersV97
    (profiles : List ProjectiveProfileClassV97) : List RawSet :=
  profiles.flatMap ProjectiveProfileClassV97.members

def projectiveVProfileMembersV97
    (profiles : List ProjectiveVProfileClassV97) : List RawSet :=
  profiles.flatMap ProjectiveVProfileClassV97.members

structure CertifiedNormalizedProjectiveProfileAuditV97 (divisor : Nat) where
  uProfiles : List ProjectiveProfileClassV97
  vProfiles : List ProjectiveVProfileClassV97
  lookupFor : Nat → Nat → List ProjectiveProfileWitnessLookupV97
  uMembers_complete :
    (projectiveProfileMembersV97 uProfiles).Perm
      (normalizedProjectiveUniqueUChoicesV89 divisor)
  vMembers_complete :
    (projectiveVProfileMembersV97 vProfiles).Perm
      (normalizedProjectiveUniqueVChoicesV89 divisor)
  uProfiles_valid : projectiveUProfilesValidB_v97 divisor uProfiles = true
  vProfiles_valid : projectiveVProfilesValidB_v97 divisor vProfiles = true
  vProfiles_divisible :
    projectiveVProfilesDivisibleB_v97 divisor vProfiles = true
  cells_covered :
    projectiveProfileAllCellsCoveredB_v97
      divisor uProfiles vProfiles lookupFor = true

def Z180K30NormalizedProjectiveProfileAuditV97 : Prop :=
  ∀ divisor : Nat,
    divisor = 3 ∨ divisor = 4 ∨ divisor = 6 →
      Nonempty (CertifiedNormalizedProjectiveProfileAuditV97 divisor)

#print axioms gramTraceScalarZeroV89_eq_projectiveProfileDot_v97

end Fuglede.Z180K30ExceptionalRawV2
