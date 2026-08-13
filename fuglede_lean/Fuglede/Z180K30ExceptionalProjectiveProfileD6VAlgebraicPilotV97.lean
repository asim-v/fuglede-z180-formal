import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6VBase
import Mathlib.Data.List.Sublists

/-! Source-only algebraic D6-V completeness pilot. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6VPilotV97 : RawSet := [0, 6, 12, 18, 24, 30]

private theorem z180_k30_projective_d6_v_filter_without_zero_pilot_v97
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

private theorem z180_k30_projective_d6_v_filter_cons_zero_pilot_v97
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (values : List (List alpha)) :
    (values.map (List.cons point)).filter
      (fun set => decide (point ∈ set)) = values.map (List.cons point) := by
  apply List.filter_eq_self.mpr
  intro set hset
  obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hset
  exact decide_eq_true List.mem_cons_self

theorem z180_k30_projective_d6_v_choices_singleton_pilot_v97 :
    normalizedProjectiveVChoicesV88 6 = [z180K30ProjectiveD6VPilotV97] := by
  unfold normalizedProjectiveVChoicesV88
  have hbase : baseForDivisor 6 = [0, 6, 12, 18, 24, 30] := by decide
  rw [hbase, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d6_v_filter_without_zero_pilot_v97
    (0 : RawPoint) [6, 12, 18, 24, 30] 6 (by decide)]
  rw [List.nil_append]
  simpa [z180K30ProjectiveD6VPilotV97] using
    z180_k30_projective_d6_v_filter_cons_zero_pilot_v97
      (0 : RawPoint) (List.sublistsLen 5 [6, 12, 18, 24, 30])

theorem z180_k30_projective_d6_v_unique_singleton_pilot_v97 :
    normalizedProjectiveUniqueVChoicesV89 6 = [z180K30ProjectiveD6VPilotV97] := by
  unfold normalizedProjectiveUniqueVChoicesV89
  rw [z180_k30_projective_d6_v_choices_singleton_pilot_v97]
  rw [List.eraseDups_cons]
  rfl

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_v_source_singleton_pilot_v97 :
    z180K30ProjectiveCompletenessV97D6VSourceGrouped =
      [z180K30ProjectiveD6VPilotV97] := by
  decide

theorem z180_k30_projective_d6_v_complete_algebraic_pilot_v97 :
    z180K30ProjectiveCompletenessV97D6VSourceGrouped.Perm
      (normalizedProjectiveUniqueVChoicesV89 6) := by
  rw [z180_k30_projective_d6_v_source_singleton_pilot_v97,
    z180_k30_projective_d6_v_unique_singleton_pilot_v97]

#print axioms z180_k30_projective_d6_v_complete_algebraic_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
