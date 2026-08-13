import Fuglede.Z180K30ExceptionalProjectiveProfileCoreV97
import Mathlib.Data.List.GetD

/-! Generic reconstruction of a list from its in-range `getD` values. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem range_map_getD_v97 {α : Type*} (fallback : α) :
    ∀ values : List α,
      (List.range values.length).map (fun index => values.getD index fallback) =
        values
  | values => by
      apply List.ext_getElem
      · simp
      · intro index hleft hright
        simp only [List.length_map, List.length_range] at hleft
        simp only [List.getElem_map, List.getElem_range]
        exact List.getD_eq_getElem values fallback hleft

theorem perm_of_index_perm_v97 {α : Type*} (fallback : α)
    (values : List α) (indices : List Nat)
    (hindices : (List.range values.length).Perm indices) :
    values.Perm (indices.map fun index => values.getD index fallback) := by
  have hmapped := hindices.map fun index => values.getD index fallback
  rw [range_map_getD_v97 fallback values] at hmapped
  exact hmapped

#print axioms perm_of_index_perm_v97

end Fuglede.Z180K30ExceptionalRawV2
