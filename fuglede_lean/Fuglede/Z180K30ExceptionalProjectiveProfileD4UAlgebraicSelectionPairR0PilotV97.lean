import Fuglede.Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97

/-! Algebraic D4-U selection row PairR0; no full candidate list is reduced. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d4_u_selection_p0_0_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [0, 0] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  rw [List.sublistsLen_of_length_lt (by decide)]
  rfl

theorem z180_k30_projective_d4_u_selection_p0_1_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [0, 1] =
      z180K30ProjectiveD4UBlockR01PilotV97 := by
  unfold z180K30ProjectiveD4UBlockR01PilotV97
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 [0, 1] =
      (0 : RawPoint) :: z180K30ProjectiveD4UTailR01PilotV97 := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD4UTailR01PilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 z180K30ProjectiveD4UTailR01PilotV97)

theorem z180_k30_projective_d4_u_selection_p0_2_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [0, 2] =
      z180K30ProjectiveD4UBlockR02PilotV97 := by
  unfold z180K30ProjectiveD4UBlockR02PilotV97
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 [0, 2] =
      (0 : RawPoint) :: z180K30ProjectiveD4UTailR02PilotV97 := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD4UTailR02PilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 z180K30ProjectiveD4UTailR02PilotV97)

theorem z180_k30_projective_d4_u_selection_p0_3_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [0, 3] =
      z180K30ProjectiveD4UBlockR03PilotV97 := by
  unfold z180K30ProjectiveD4UBlockR03PilotV97
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 [0, 3] =
      (0 : RawPoint) :: z180K30ProjectiveD4UTailR03PilotV97 := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD4UTailR03PilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 z180K30ProjectiveD4UTailR03PilotV97)

theorem z180_k30_projective_d4_u_selection_p0_4_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [0, 4] =
      z180K30ProjectiveD4UBlockR04PilotV97 := by
  unfold z180K30ProjectiveD4UBlockR04PilotV97
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 [0, 4] =
      (0 : RawPoint) :: z180K30ProjectiveD4UTailR04PilotV97 := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD4UTailR04PilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 z180K30ProjectiveD4UTailR04PilotV97)

theorem z180_k30_projective_d4_u_selection_p0_5_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [0, 5] =
      z180K30ProjectiveD4UBlockR05PilotV97 := by
  unfold z180K30ProjectiveD4UBlockR05PilotV97
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 [0, 5] =
      (0 : RawPoint) :: z180K30ProjectiveD4UTailR05PilotV97 := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD4UTailR05PilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 z180K30ProjectiveD4UTailR05PilotV97)

theorem z180_k30_projective_d4_u_selection_p0_6_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [0, 6] =
      z180K30ProjectiveD4UBlockR06PilotV97 := by
  unfold z180K30ProjectiveD4UBlockR06PilotV97
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 [0, 6] =
      (0 : RawPoint) :: z180K30ProjectiveD4UTailR06PilotV97 := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD4UTailR06PilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 z180K30ProjectiveD4UTailR06PilotV97)

theorem z180_k30_projective_d4_u_selection_p0_7_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [0, 7] =
      z180K30ProjectiveD4UBlockR07PilotV97 := by
  unfold z180K30ProjectiveD4UBlockR07PilotV97
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 [0, 7] =
      (0 : RawPoint) :: z180K30ProjectiveD4UTailR07PilotV97 := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD4UTailR07PilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 z180K30ProjectiveD4UTailR07PilotV97)

theorem z180_k30_projective_d4_u_selection_p0_8_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 4 [0, 8] =
      z180K30ProjectiveD4UBlockR08PilotV97 := by
  unfold z180K30ProjectiveD4UBlockR08PilotV97
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 [0, 8] =
      (0 : RawPoint) :: z180K30ProjectiveD4UTailR08PilotV97 := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD4UTailR08PilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 z180K30ProjectiveD4UTailR08PilotV97)

end Fuglede.Z180K30ExceptionalRawV2
