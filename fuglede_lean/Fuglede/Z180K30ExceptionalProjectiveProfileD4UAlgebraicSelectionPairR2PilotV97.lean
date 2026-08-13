import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! Algebraic D4-U selection row PairR2; no full candidate list is reduced. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d4_u_selection_p2_0_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [2, 0] =
      z180K30ProjectiveD4UBlockR02PilotV97 := by
  unfold z180K30ProjectiveD4UBlockR02PilotV97
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 [2, 0] =
      (0 : RawPoint) :: z180K30ProjectiveD4UTailR02PilotV97 := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD4UTailR02PilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 z180K30ProjectiveD4UTailR02PilotV97)

theorem z180_k30_projective_d4_u_selection_p2_1_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [2, 1] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 4 [2, 1]) 6
      (by decide)

theorem z180_k30_projective_d4_u_selection_p2_2_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [2, 2] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  rw [List.sublistsLen_of_length_lt (by decide)]
  rfl

theorem z180_k30_projective_d4_u_selection_p2_3_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [2, 3] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 4 [2, 3]) 6
      (by decide)

theorem z180_k30_projective_d4_u_selection_p2_4_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [2, 4] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 4 [2, 4]) 6
      (by decide)

theorem z180_k30_projective_d4_u_selection_p2_5_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [2, 5] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 4 [2, 5]) 6
      (by decide)

theorem z180_k30_projective_d4_u_selection_p2_6_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [2, 6] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 4 [2, 6]) 6
      (by decide)

theorem z180_k30_projective_d4_u_selection_p2_7_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [2, 7] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 4 [2, 7]) 6
      (by decide)

theorem z180_k30_projective_d4_u_selection_p2_8_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [2, 8] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 4 [2, 8]) 6
      (by decide)

end Fuglede.Z180K30ExceptionalRawV2
