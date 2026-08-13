import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermPilotV97
import Mathlib.Data.List.Sublists

/-!
Algebraic second half of the D3-V completeness pilot.  It removes the
deduplication and zero-membership filter by generic list lemmas, leaving the
tail-first `sublistsLen` enumeration.  The sole definitional bridge evaluates
only list constructors and indices: it performs no `BEq`, filtering, or
permutation search over `RawSet` values.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem eraseDups_eq_self_of_nodup_v97
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    ∀ {values : List alpha}, values.Nodup → values.eraseDups = values
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
        eraseDups_eq_self_of_nodup_v97 htail]

private theorem filter_sublists_without_point_v97
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

private theorem filter_cons_point_v97
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (values : List (List alpha)) :
    (values.map (List.cons point)).filter
      (fun set => decide (point ∈ set)) =
        values.map (List.cons point) := by
  apply List.filter_eq_self.mpr
  intro set hset
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp hset
  exact decide_eq_true (List.mem_cons_self)

def z180K30ProjectiveD3VPositiveTailPilotV97 : List RawPoint :=
  [3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33]

theorem z180_k30_projective_d3_v_base_pilot_v97 :
    baseForDivisor 3 =
      (0 : RawPoint) :: z180K30ProjectiveD3VPositiveTailPilotV97 := by
  decide

theorem z180_k30_projective_d3_v_choices_sublists_pilot_v97 :
    normalizedProjectiveVChoicesV88 3 =
      (List.sublistsLen 5 z180K30ProjectiveD3VPositiveTailPilotV97).map
        (List.cons (0 : RawPoint)) := by
  unfold normalizedProjectiveVChoicesV88
  rw [z180_k30_projective_d3_v_base_pilot_v97,
    List.sublistsLen_succ_cons, List.filter_append]
  rw [filter_sublists_without_point_v97
    (0 : RawPoint) z180K30ProjectiveD3VPositiveTailPilotV97 6 (by decide)]
  rw [List.nil_append]
  exact filter_cons_point_v97 (0 : RawPoint)
    (List.sublistsLen 5 z180K30ProjectiveD3VPositiveTailPilotV97)

theorem z180_k30_projective_d3_v_unique_sublists_pilot_v97 :
    normalizedProjectiveUniqueVChoicesV89 3 =
      (List.sublistsLen 5 z180K30ProjectiveD3VPositiveTailPilotV97).map
        (List.cons (0 : RawPoint)) := by
  unfold normalizedProjectiveUniqueVChoicesV89
  rw [z180_k30_projective_d3_v_choices_sublists_pilot_v97]
  apply eraseDups_eq_self_of_nodup_v97
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_indexed_sublists_pilot_v97 :
    z180K30ProjectiveD3VCanonicalIndexedPilotV97 =
      (List.sublistsLen 5 z180K30ProjectiveD3VPositiveTailPilotV97).map
        (List.cons (0 : RawPoint)) := by
  rfl

theorem z180_k30_projective_d3_v_complete_algebraic_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3VSourceGrouped.Perm
      (normalizedProjectiveUniqueVChoicesV89 3) := by
  exact z180_k30_projective_d3_v_source_perm_indexed_pilot_v97.trans
    (List.Perm.of_eq
      (z180_k30_projective_d3_v_indexed_sublists_pilot_v97.trans
        z180_k30_projective_d3_v_unique_sublists_pilot_v97.symm))

#print axioms z180_k30_projective_d3_v_unique_sublists_pilot_v97
#print axioms z180_k30_projective_d3_v_indexed_sublists_pilot_v97
#print axioms z180_k30_projective_d3_v_complete_algebraic_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
