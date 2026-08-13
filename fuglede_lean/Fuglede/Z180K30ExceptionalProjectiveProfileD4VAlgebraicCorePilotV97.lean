import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4VBase
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sublists

/-! Isolated bounded structural D4-V completeness pilot. -/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem eraseDups_eq_self_of_nodup_d4v_pilot
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall {values : List alpha}, values.Nodup -> values.eraseDups = values
  | [], _ => rfl
  | head :: tail, hnodup => by
      have hhead : head ∉ tail := (List.nodup_cons.mp hnodup).1
      have htail : tail.Nodup := (List.nodup_cons.mp hnodup).2
      have hfilter :
          tail.filter (fun item => !item == head) = tail := by
        apply List.filter_eq_self.mpr
        intro item hitem
        have hne : item ≠ head := by
          intro hequal
          exact hhead (hequal ▸ hitem)
        simp [hne]
      rw [List.eraseDups_cons, hfilter,
        eraseDups_eq_self_of_nodup_d4v_pilot htail]

private theorem filter_sublists_without_point_d4v_pilot
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (domain : List alpha) (length : Nat)
    (hpoint : point ∉ domain) :
    (List.sublistsLen length domain).filter
      (fun values => decide (point ∈ values)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro values hvalues hcontains
  have hmember : point ∈ values := of_decide_eq_true hcontains
  have hsublist := (List.mem_sublistsLen.mp hvalues).1
  exact hpoint (hsublist.subset hmember)

private theorem filter_cons_point_d4v_pilot
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (values : List (List alpha)) :
    (values.map (List.cons point)).filter
      (fun set => decide (point ∈ set)) =
        values.map (List.cons point) := by
  apply List.filter_eq_self.mpr
  intro set hset
  obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hset
  exact decide_eq_true (List.mem_cons_self)

def z180K30ProjectiveD4VPositiveTailPilotV97 : RawSet :=
  [4, 8, 12, 16, 20, 24, 28, 32]

def z180K30ProjectiveD4VCombPilotV97
    (frame domain : RawSet) (length : Nat) : List RawSet :=
  (List.sublistsLen length domain).map fun suffix => frame ++ suffix

theorem z180_k30_projective_d4_v_comb_succ_cons_pilot_v97
    (frame : RawSet) (head : RawPoint) (tail : RawSet) (length : Nat) :
    z180K30ProjectiveD4VCombPilotV97 frame (head :: tail) (length + 1) =
      z180K30ProjectiveD4VCombPilotV97 frame tail (length + 1) ++
        z180K30ProjectiveD4VCombPilotV97
          (frame ++ [head]) tail length := by
  simp only [z180K30ProjectiveD4VCombPilotV97,
    List.sublistsLen_succ_cons, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro suffix _
  change frame ++ head :: suffix = frame ++ [head] ++ suffix
  rw [List.append_assoc, List.singleton_append]

def z180K30ProjectiveD4VCanonicalIndicesPilotV97 : List Nat :=
  [5, 17, 29, 41, 28, 16, 15, 35, 53, 52, 34, 27, 51, 55, 50, 40, 49, 48, 26, 33, 14, 4, 13, 25, 39, 24, 12, 32, 47, 46, 23, 45, 54, 38, 44, 22, 3, 11, 21, 37, 10, 31, 43, 20, 42, 36, 2, 9, 19, 8, 30, 18, 1, 7, 6, 0]

def z180K30ProjectiveD4VSourceAtPilotV97 (index : Nat) : RawSet :=
  z180K30ProjectiveCompletenessV97D4VSourceGrouped.getD index []

def z180K30ProjectiveD4VCanonicalIndexedPilotV97 : List RawSet :=
  z180K30ProjectiveD4VCanonicalIndicesPilotV97.map
    z180K30ProjectiveD4VSourceAtPilotV97

theorem z180_k30_projective_d4_v_source_length_pilot_v97 :
    z180K30ProjectiveCompletenessV97D4VSourceGrouped.length = 56 := by
  rfl

private theorem map_range_getD_eq_self_d4v_pilot
    {alpha : Type} (values : List alpha) (fallback : alpha) :
    (List.range values.length).map (fun index =>
      values.getD index fallback) = values := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem values fallback hright

theorem z180_k30_projective_d4_v_source_range_pilot_v97 :
    (List.range 56).map z180K30ProjectiveD4VSourceAtPilotV97 =
      z180K30ProjectiveCompletenessV97D4VSourceGrouped := by
  rw [← z180_k30_projective_d4_v_source_length_pilot_v97]
  exact map_range_getD_eq_self_d4v_pilot
    z180K30ProjectiveCompletenessV97D4VSourceGrouped []

theorem z180_k30_projective_d4_v_index_perm_pilot_v97 :
    (List.range 56).Perm z180K30ProjectiveD4VCanonicalIndicesPilotV97 := by
  decide

theorem z180_k30_projective_d4_v_source_perm_indexed_pilot_v97 :
    z180K30ProjectiveCompletenessV97D4VSourceGrouped.Perm
      z180K30ProjectiveD4VCanonicalIndexedPilotV97 := by
  have h := z180_k30_projective_d4_v_index_perm_pilot_v97.map
    z180K30ProjectiveD4VSourceAtPilotV97
  rw [z180_k30_projective_d4_v_source_range_pilot_v97] at h
  exact h

theorem z180_k30_projective_d4_v_choices_sublists_pilot_v97 :
    normalizedProjectiveVChoicesV88 4 =
      z180K30ProjectiveD4VCombPilotV97 [0]
        z180K30ProjectiveD4VPositiveTailPilotV97 5 := by
  unfold normalizedProjectiveVChoicesV88
  have hbase : baseForDivisor 4 =
      (0 : RawPoint) :: z180K30ProjectiveD4VPositiveTailPilotV97 := by decide
  rw [hbase, List.sublistsLen_succ_cons, List.filter_append]
  rw [filter_sublists_without_point_d4v_pilot
    (0 : RawPoint) z180K30ProjectiveD4VPositiveTailPilotV97 6 (by decide)]
  rw [List.nil_append]
  exact filter_cons_point_d4v_pilot (0 : RawPoint)
    (List.sublistsLen 5 z180K30ProjectiveD4VPositiveTailPilotV97)

theorem z180_k30_projective_d4_v_unique_sublists_pilot_v97 :
    normalizedProjectiveUniqueVChoicesV89 4 =
      z180K30ProjectiveD4VCombPilotV97 [0]
        z180K30ProjectiveD4VPositiveTailPilotV97 5 := by
  unfold normalizedProjectiveUniqueVChoicesV89
  rw [z180_k30_projective_d4_v_choices_sublists_pilot_v97]
  apply eraseDups_eq_self_of_nodup_d4v_pilot
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide

end Fuglede.Z180K30ExceptionalRawV2
