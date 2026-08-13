import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicIndexPermPilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow07PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow08PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow09PilotV97

/-!
Structural D6-U aggregate.  Every RawSet equality certificate is imported
from one leaf of size at most ten; aggregation and duplicate elimination are
proved generically.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UIndexChunksPilotV97 : List (List Nat) :=
  [ z180K30ProjectiveD6UIndexRow00PilotV97,
    z180K30ProjectiveD6UIndexRow01PilotV97,
    z180K30ProjectiveD6UIndexRow02PilotV97,
    z180K30ProjectiveD6UIndexRow03PilotV97,
    z180K30ProjectiveD6UIndexRow04PilotV97,
    z180K30ProjectiveD6UIndexRow05PilotV97,
    z180K30ProjectiveD6UIndexRow06PilotV97,
    z180K30ProjectiveD6UIndexRow07PilotV97,
    z180K30ProjectiveD6UIndexRow08PilotV97,
    z180K30ProjectiveD6UIndexRow09PilotV97].flatten

def z180K30ProjectiveD6USourceChunksPilotV97 : List (List RawSet) :=
  [ z180K30ProjectiveD6USourceRow00PilotV97,
    z180K30ProjectiveD6USourceRow01PilotV97,
    z180K30ProjectiveD6USourceRow02PilotV97,
    z180K30ProjectiveD6USourceRow03PilotV97,
    z180K30ProjectiveD6USourceRow04PilotV97,
    z180K30ProjectiveD6USourceRow05PilotV97,
    z180K30ProjectiveD6USourceRow06PilotV97,
    z180K30ProjectiveD6USourceRow07PilotV97,
    z180K30ProjectiveD6USourceRow08PilotV97,
    z180K30ProjectiveD6USourceRow09PilotV97].flatten

def z180K30ProjectiveD6UTargetChunksPilotV97 : List (List RawSet) :=
  [ z180K30ProjectiveD6UTargetRow00PilotV97,
    z180K30ProjectiveD6UTargetRow01PilotV97,
    z180K30ProjectiveD6UTargetRow02PilotV97,
    z180K30ProjectiveD6UTargetRow03PilotV97,
    z180K30ProjectiveD6UTargetRow04PilotV97,
    z180K30ProjectiveD6UTargetRow05PilotV97,
    z180K30ProjectiveD6UTargetRow06PilotV97,
    z180K30ProjectiveD6UTargetRow07PilotV97,
    z180K30ProjectiveD6UTargetRow08PilotV97,
    z180K30ProjectiveD6UTargetRow09PilotV97].flatten

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_index_chunks_flatten_pilot_v97 :
    z180K30ProjectiveD6UIndexChunksPilotV97.flatten =
      z180K30ProjectiveD6UCanonicalIndicesPilotV97 := by
  rfl

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_index_chunks_map_pilot_v97 :
    (z180K30ProjectiveD6UIndexChunksPilotV97.map fun indices =>
      indices.map z180K30ProjectiveD6USourceAtPilotV97) =
        z180K30ProjectiveD6USourceChunksPilotV97 := by
  unfold z180K30ProjectiveD6UIndexChunksPilotV97
  unfold z180K30ProjectiveD6USourceChunksPilotV97
  rw [List.map_flatten]
  apply congrArg (fun rows : List (List (List RawSet)) => rows.flatten)
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_00_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_01_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_02_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_03_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_04_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_05_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_06_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_07_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_08_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_index_source_row_09_pilot_v97
  · rfl

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_source_target_chunks_pilot_v97 :
    z180K30ProjectiveD6USourceChunksPilotV97 =
      z180K30ProjectiveD6UTargetChunksPilotV97 := by
  unfold z180K30ProjectiveD6USourceChunksPilotV97
  unfold z180K30ProjectiveD6UTargetChunksPilotV97
  apply congrArg (fun rows : List (List (List RawSet)) => rows.flatten)
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_00_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_01_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_02_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_03_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_04_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_05_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_06_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_07_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_08_pilot_v97
  apply congrArg₂ List.cons
  · exact z180_k30_projective_d6_u_source_target_row_09_pilot_v97
  · rfl

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_target_chunks_tree_pilot_v97 :
    z180K30ProjectiveD6UTargetChunksPilotV97 =
      [z180K30ProjectiveD6UAPilotV97] ::
        (z180K30ProjectiveD6UCombChunksPilotV97 6 [0] z180K30ProjectiveD6UTailR1PilotV97 5 ++
      z180K30ProjectiveD6UCombChunksPilotV97 6 [0] z180K30ProjectiveD6UTailR2PilotV97 5 ++
      z180K30ProjectiveD6UCombChunksPilotV97 6 [0] z180K30ProjectiveD6UTailR3PilotV97 5 ++
      z180K30ProjectiveD6UCombChunksPilotV97 6 [0] z180K30ProjectiveD6UTailR4PilotV97 5 ++
      z180K30ProjectiveD6UCombChunksPilotV97 6 [0] z180K30ProjectiveD6UTailR5PilotV97 5) := by
  rfl

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_target_chunks_flatten_pilot_v97 :
    z180K30ProjectiveD6UTargetChunksPilotV97.flatten =
      z180K30ProjectiveD6UCanonicalPilotV97 := by
  rw [z180_k30_projective_d6_u_target_chunks_tree_pilot_v97]
  simp only [List.flatten_cons, List.flatten_append,
    z180_k30_projective_d6_u_comb_chunks_flatten_pilot_v97]
  rfl

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_indexed_canonical_pilot_v97 :
    z180K30ProjectiveD6UCanonicalIndexedPilotV97 =
      z180K30ProjectiveD6UCanonicalPilotV97 := by
  unfold z180K30ProjectiveD6UCanonicalIndexedPilotV97
  rw [← z180_k30_projective_d6_u_index_chunks_flatten_pilot_v97,
    List.map_flatten, z180_k30_projective_d6_u_index_chunks_map_pilot_v97,
    z180_k30_projective_d6_u_source_target_chunks_pilot_v97,
    z180_k30_projective_d6_u_target_chunks_flatten_pilot_v97]

theorem z180_k30_projective_d6_u_source_perm_canonical_pilot_v97 :
    z180K30ProjectiveCompletenessV97D6USourceGrouped.Perm
      z180K30ProjectiveD6UCanonicalPilotV97 := by
  exact z180_k30_projective_d6_u_source_perm_indexed_pilot_v97.trans
    (List.Perm.of_eq z180_k30_projective_d6_u_indexed_canonical_pilot_v97)

private theorem z180_k30_projective_d6_u_filter_without_zero_pilot_v97
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

private theorem z180_k30_projective_d6_u_filter_cons_zero_pilot_v97
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (values : List (List alpha)) :
    (values.map (List.cons point)).filter
      (fun set => decide (point ∈ set)) = values.map (List.cons point) := by
  apply List.filter_eq_self.mpr
  intro set hset
  obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hset
  exact decide_eq_true List.mem_cons_self

private theorem z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    (selection : List Nat) (tail : RawSet)
    (hdomain : normalizedProjectiveClassDomainV88 6 selection =
      (0 : RawPoint) :: tail)
    (hzero : (0 : RawPoint) ∉ tail) :
    normalizedProjectiveUChoicesForSelectionV88 6 selection =
      z180K30ProjectiveD6UCombPilotV97 [0] tail 5 := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) tail 6 hzero]
  rw [List.nil_append]
  exact z180_k30_projective_d6_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 tail)

theorem z180_k30_projective_d6_u_selection_s0_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [0] =
      [z180K30ProjectiveD6UAPilotV97] := by
  decide

theorem z180_k30_projective_d6_u_selection_s1_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [1] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [1]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_s2_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [2] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [2]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_s3_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [3] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [3]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_s4_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [4] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [4]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_s5_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [5] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [5]) 6
      (by decide)


theorem z180_k30_projective_d6_u_selection_p0_0_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [0, 0] =
      [z180K30ProjectiveD6UAPilotV97] := by
  decide

theorem z180_k30_projective_d6_u_selection_p0_1_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [0, 1] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR1PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [0, 1] z180K30ProjectiveD6UTailR1PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p0_2_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [0, 2] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR2PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [0, 2] z180K30ProjectiveD6UTailR2PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p0_3_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [0, 3] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR3PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [0, 3] z180K30ProjectiveD6UTailR3PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p0_4_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [0, 4] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR4PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [0, 4] z180K30ProjectiveD6UTailR4PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p0_5_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [0, 5] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR5PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [0, 5] z180K30ProjectiveD6UTailR5PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p1_0_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [1, 0] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR1PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [1, 0] z180K30ProjectiveD6UTailR1PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p1_1_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [1, 1] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [1, 1]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p1_2_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [1, 2] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [1, 2]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p1_3_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [1, 3] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [1, 3]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p1_4_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [1, 4] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [1, 4]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p1_5_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [1, 5] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [1, 5]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p2_0_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [2, 0] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR2PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [2, 0] z180K30ProjectiveD6UTailR2PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p2_1_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [2, 1] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [2, 1]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p2_2_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [2, 2] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [2, 2]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p2_3_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [2, 3] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [2, 3]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p2_4_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [2, 4] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [2, 4]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p2_5_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [2, 5] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [2, 5]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p3_0_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [3, 0] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR3PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [3, 0] z180K30ProjectiveD6UTailR3PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p3_1_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [3, 1] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [3, 1]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p3_2_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [3, 2] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [3, 2]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p3_3_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [3, 3] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [3, 3]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p3_4_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [3, 4] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [3, 4]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p3_5_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [3, 5] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [3, 5]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p4_0_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [4, 0] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR4PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [4, 0] z180K30ProjectiveD6UTailR4PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p4_1_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [4, 1] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [4, 1]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p4_2_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [4, 2] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [4, 2]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p4_3_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [4, 3] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [4, 3]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p4_4_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [4, 4] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [4, 4]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p4_5_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [4, 5] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [4, 5]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p5_0_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [5, 0] =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR5PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    [5, 0] z180K30ProjectiveD6UTailR5PilotV97 (by decide) (by decide)

theorem z180_k30_projective_d6_u_selection_p5_1_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [5, 1] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [5, 1]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p5_2_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [5, 2] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [5, 2]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p5_3_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [5, 3] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [5, 3]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p5_4_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [5, 4] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [5, 4]) 6
      (by decide)

theorem z180_k30_projective_d6_u_selection_p5_5_pilot_v97 :
    normalizedProjectiveUChoicesForSelectionV88 6 [5, 5] = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 [5, 5]) 6
      (by decide)


theorem z180_k30_projective_d6_u_selections_literal_pilot_v97 :
    normalizedProjectiveClassSelectionsV88 6 =
      [[0], [1], [2], [3], [4], [5],
       [0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [0, 5],
       [1, 0], [1, 1], [1, 2], [1, 3], [1, 4], [1, 5],
       [2, 0], [2, 1], [2, 2], [2, 3], [2, 4], [2, 5],
       [3, 0], [3, 1], [3, 2], [3, 3], [3, 4], [3, 5],
       [4, 0], [4, 1], [4, 2], [4, 3], [4, 4], [4, 5],
       [5, 0], [5, 1], [5, 2], [5, 3], [5, 4], [5, 5]] := by
  decide

theorem z180_k30_projective_d6_u_choices_expanded_pilot_v97 :
    normalizedProjectiveUChoicesV88 6 =
      [z180K30ProjectiveD6UAPilotV97] ++
      [z180K30ProjectiveD6UAPilotV97] ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR1PilotV97 5 ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR2PilotV97 5 ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR3PilotV97 5 ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR4PilotV97 5 ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR5PilotV97 5 ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR1PilotV97 5 ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR2PilotV97 5 ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR3PilotV97 5 ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR4PilotV97 5 ++
      z180K30ProjectiveD6UCombPilotV97 [0] z180K30ProjectiveD6UTailR5PilotV97 5 := by
  unfold normalizedProjectiveUChoicesV88
  rw [z180_k30_projective_d6_u_selections_literal_pilot_v97]
  simp only [List.flatMap_cons, List.flatMap_nil,
    z180_k30_projective_d6_u_selection_s0_pilot_v97,
    z180_k30_projective_d6_u_selection_s1_pilot_v97,
    z180_k30_projective_d6_u_selection_s2_pilot_v97,
    z180_k30_projective_d6_u_selection_s3_pilot_v97,
    z180_k30_projective_d6_u_selection_s4_pilot_v97,
    z180_k30_projective_d6_u_selection_s5_pilot_v97,
    z180_k30_projective_d6_u_selection_p0_0_pilot_v97,
    z180_k30_projective_d6_u_selection_p0_1_pilot_v97,
    z180_k30_projective_d6_u_selection_p0_2_pilot_v97,
    z180_k30_projective_d6_u_selection_p0_3_pilot_v97,
    z180_k30_projective_d6_u_selection_p0_4_pilot_v97,
    z180_k30_projective_d6_u_selection_p0_5_pilot_v97,
    z180_k30_projective_d6_u_selection_p1_0_pilot_v97,
    z180_k30_projective_d6_u_selection_p1_1_pilot_v97,
    z180_k30_projective_d6_u_selection_p1_2_pilot_v97,
    z180_k30_projective_d6_u_selection_p1_3_pilot_v97,
    z180_k30_projective_d6_u_selection_p1_4_pilot_v97,
    z180_k30_projective_d6_u_selection_p1_5_pilot_v97,
    z180_k30_projective_d6_u_selection_p2_0_pilot_v97,
    z180_k30_projective_d6_u_selection_p2_1_pilot_v97,
    z180_k30_projective_d6_u_selection_p2_2_pilot_v97,
    z180_k30_projective_d6_u_selection_p2_3_pilot_v97,
    z180_k30_projective_d6_u_selection_p2_4_pilot_v97,
    z180_k30_projective_d6_u_selection_p2_5_pilot_v97,
    z180_k30_projective_d6_u_selection_p3_0_pilot_v97,
    z180_k30_projective_d6_u_selection_p3_1_pilot_v97,
    z180_k30_projective_d6_u_selection_p3_2_pilot_v97,
    z180_k30_projective_d6_u_selection_p3_3_pilot_v97,
    z180_k30_projective_d6_u_selection_p3_4_pilot_v97,
    z180_k30_projective_d6_u_selection_p3_5_pilot_v97,
    z180_k30_projective_d6_u_selection_p4_0_pilot_v97,
    z180_k30_projective_d6_u_selection_p4_1_pilot_v97,
    z180_k30_projective_d6_u_selection_p4_2_pilot_v97,
    z180_k30_projective_d6_u_selection_p4_3_pilot_v97,
    z180_k30_projective_d6_u_selection_p4_4_pilot_v97,
    z180_k30_projective_d6_u_selection_p4_5_pilot_v97,
    z180_k30_projective_d6_u_selection_p5_0_pilot_v97,
    z180_k30_projective_d6_u_selection_p5_1_pilot_v97,
    z180_k30_projective_d6_u_selection_p5_2_pilot_v97,
    z180_k30_projective_d6_u_selection_p5_3_pilot_v97,
    z180_k30_projective_d6_u_selection_p5_4_pilot_v97,
    z180_k30_projective_d6_u_selection_p5_5_pilot_v97, List.nil_append, List.append_nil, List.append_assoc]

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_choices_raw_blocks_pilot_v97 :
    normalizedProjectiveUChoicesV88 6 =
      z180K30ProjectiveD6UAPilotV97 ::
        z180K30ProjectiveD6URawBlocksTwicePilotV97.flatten := by
  rw [z180_k30_projective_d6_u_choices_expanded_pilot_v97]
  rfl

theorem z180_k30_projective_d6_u_block_r1_nodup_pilot_v97 :
    z180K30ProjectiveD6UBlockR1PilotV97.Nodup := by
  unfold z180K30ProjectiveD6UBlockR1PilotV97
  unfold z180K30ProjectiveD6URawBlockR1PilotV97
  unfold z180K30ProjectiveD6UCombPilotV97
  apply List.Nodup.filter
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide

theorem z180_k30_projective_d6_u_block_r1_marker_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR1PilotV97) :
    ∃ point ∈ value, point.val % 6 = 1 := by
  unfold z180K30ProjectiveD6UBlockR1PilotV97 at hvalue
  rcases List.mem_filter.mp hvalue with ⟨hraw, hne⟩
  unfold z180K30ProjectiveD6URawBlockR1PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  by_contra hmarker
  push_neg at hmarker
  have hsub := (List.mem_sublistsLen.mp hsuffix).1
  have hlength : suffix.length = 5 :=
    (List.mem_sublistsLen.mp hsuffix).2
  have hfilterSuffix :
      suffix.filter (fun point => point.val % 6 != 1) = suffix := by
    apply List.filter_eq_self.mpr
    intro point hpoint
    have hneResidue : point.val % 6 ≠ 1 :=
      hmarker point (by simp [hpoint])
    simpa using hneResidue
  have hfilterTail :
      z180K30ProjectiveD6UTailR1PilotV97.filter
          (fun point => point.val % 6 != 1) =
        [6, 12, 18, 24, 30] := by
    decide
  have hsubZero : List.Sublist suffix ([6, 12, 18, 24, 30] : RawSet) := by
    rw [← hfilterSuffix, ← hfilterTail]
    exact hsub.filter _
  have hsuffixZero : suffix = ([6, 12, 18, 24, 30] : RawSet) :=
    hsubZero.eq_of_length (by simpa using hlength)
  simp [hsuffixZero, z180K30ProjectiveD6UAPilotV97] at hne

theorem z180_k30_projective_d6_u_block_r1_residues_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR1PilotV97)
    (point : RawPoint) (hpoint : point ∈ value) :
    point.val % 6 = 0 ∨ point.val % 6 = 1 := by
  unfold z180K30ProjectiveD6UBlockR1PilotV97 at hvalue
  have hraw := (List.mem_filter.mp hvalue).1
  unfold z180K30ProjectiveD6URawBlockR1PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  simp only [List.singleton_append, List.mem_cons] at hpoint
  rcases hpoint with hzero | hsuffixPoint
  · subst point
    simp
  · have htailPoint : point ∈ z180K30ProjectiveD6UTailR1PilotV97 :=
      (List.mem_sublistsLen.mp hsuffix).1.subset hsuffixPoint
    have hclassify : ∀ candidate : RawPoint,
        candidate ∈ z180K30ProjectiveD6UTailR1PilotV97 →
          candidate.val % 6 = 0 ∨ candidate.val % 6 = 1 := by
      decide
    exact hclassify point htailPoint

theorem z180_k30_projective_d6_u_block_r2_nodup_pilot_v97 :
    z180K30ProjectiveD6UBlockR2PilotV97.Nodup := by
  unfold z180K30ProjectiveD6UBlockR2PilotV97
  unfold z180K30ProjectiveD6URawBlockR2PilotV97
  unfold z180K30ProjectiveD6UCombPilotV97
  apply List.Nodup.filter
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide

theorem z180_k30_projective_d6_u_block_r2_marker_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR2PilotV97) :
    ∃ point ∈ value, point.val % 6 = 2 := by
  unfold z180K30ProjectiveD6UBlockR2PilotV97 at hvalue
  rcases List.mem_filter.mp hvalue with ⟨hraw, hne⟩
  unfold z180K30ProjectiveD6URawBlockR2PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  by_contra hmarker
  push_neg at hmarker
  have hsub := (List.mem_sublistsLen.mp hsuffix).1
  have hlength : suffix.length = 5 :=
    (List.mem_sublistsLen.mp hsuffix).2
  have hfilterSuffix :
      suffix.filter (fun point => point.val % 6 != 2) = suffix := by
    apply List.filter_eq_self.mpr
    intro point hpoint
    have hneResidue : point.val % 6 ≠ 2 :=
      hmarker point (by simp [hpoint])
    simpa using hneResidue
  have hfilterTail :
      z180K30ProjectiveD6UTailR2PilotV97.filter
          (fun point => point.val % 6 != 2) =
        [6, 12, 18, 24, 30] := by
    decide
  have hsubZero : List.Sublist suffix ([6, 12, 18, 24, 30] : RawSet) := by
    rw [← hfilterSuffix, ← hfilterTail]
    exact hsub.filter _
  have hsuffixZero : suffix = ([6, 12, 18, 24, 30] : RawSet) :=
    hsubZero.eq_of_length (by simpa using hlength)
  simp [hsuffixZero, z180K30ProjectiveD6UAPilotV97] at hne

theorem z180_k30_projective_d6_u_block_r2_residues_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR2PilotV97)
    (point : RawPoint) (hpoint : point ∈ value) :
    point.val % 6 = 0 ∨ point.val % 6 = 2 := by
  unfold z180K30ProjectiveD6UBlockR2PilotV97 at hvalue
  have hraw := (List.mem_filter.mp hvalue).1
  unfold z180K30ProjectiveD6URawBlockR2PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  simp only [List.singleton_append, List.mem_cons] at hpoint
  rcases hpoint with hzero | hsuffixPoint
  · subst point
    simp
  · have htailPoint : point ∈ z180K30ProjectiveD6UTailR2PilotV97 :=
      (List.mem_sublistsLen.mp hsuffix).1.subset hsuffixPoint
    have hclassify : ∀ candidate : RawPoint,
        candidate ∈ z180K30ProjectiveD6UTailR2PilotV97 →
          candidate.val % 6 = 0 ∨ candidate.val % 6 = 2 := by
      decide
    exact hclassify point htailPoint

theorem z180_k30_projective_d6_u_block_r3_nodup_pilot_v97 :
    z180K30ProjectiveD6UBlockR3PilotV97.Nodup := by
  unfold z180K30ProjectiveD6UBlockR3PilotV97
  unfold z180K30ProjectiveD6URawBlockR3PilotV97
  unfold z180K30ProjectiveD6UCombPilotV97
  apply List.Nodup.filter
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide

theorem z180_k30_projective_d6_u_block_r3_marker_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR3PilotV97) :
    ∃ point ∈ value, point.val % 6 = 3 := by
  unfold z180K30ProjectiveD6UBlockR3PilotV97 at hvalue
  rcases List.mem_filter.mp hvalue with ⟨hraw, hne⟩
  unfold z180K30ProjectiveD6URawBlockR3PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  by_contra hmarker
  push_neg at hmarker
  have hsub := (List.mem_sublistsLen.mp hsuffix).1
  have hlength : suffix.length = 5 :=
    (List.mem_sublistsLen.mp hsuffix).2
  have hfilterSuffix :
      suffix.filter (fun point => point.val % 6 != 3) = suffix := by
    apply List.filter_eq_self.mpr
    intro point hpoint
    have hneResidue : point.val % 6 ≠ 3 :=
      hmarker point (by simp [hpoint])
    simpa using hneResidue
  have hfilterTail :
      z180K30ProjectiveD6UTailR3PilotV97.filter
          (fun point => point.val % 6 != 3) =
        [6, 12, 18, 24, 30] := by
    decide
  have hsubZero : List.Sublist suffix ([6, 12, 18, 24, 30] : RawSet) := by
    rw [← hfilterSuffix, ← hfilterTail]
    exact hsub.filter _
  have hsuffixZero : suffix = ([6, 12, 18, 24, 30] : RawSet) :=
    hsubZero.eq_of_length (by simpa using hlength)
  simp [hsuffixZero, z180K30ProjectiveD6UAPilotV97] at hne

theorem z180_k30_projective_d6_u_block_r3_residues_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR3PilotV97)
    (point : RawPoint) (hpoint : point ∈ value) :
    point.val % 6 = 0 ∨ point.val % 6 = 3 := by
  unfold z180K30ProjectiveD6UBlockR3PilotV97 at hvalue
  have hraw := (List.mem_filter.mp hvalue).1
  unfold z180K30ProjectiveD6URawBlockR3PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  simp only [List.singleton_append, List.mem_cons] at hpoint
  rcases hpoint with hzero | hsuffixPoint
  · subst point
    simp
  · have htailPoint : point ∈ z180K30ProjectiveD6UTailR3PilotV97 :=
      (List.mem_sublistsLen.mp hsuffix).1.subset hsuffixPoint
    have hclassify : ∀ candidate : RawPoint,
        candidate ∈ z180K30ProjectiveD6UTailR3PilotV97 →
          candidate.val % 6 = 0 ∨ candidate.val % 6 = 3 := by
      decide
    exact hclassify point htailPoint

theorem z180_k30_projective_d6_u_block_r4_nodup_pilot_v97 :
    z180K30ProjectiveD6UBlockR4PilotV97.Nodup := by
  unfold z180K30ProjectiveD6UBlockR4PilotV97
  unfold z180K30ProjectiveD6URawBlockR4PilotV97
  unfold z180K30ProjectiveD6UCombPilotV97
  apply List.Nodup.filter
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide

theorem z180_k30_projective_d6_u_block_r4_marker_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR4PilotV97) :
    ∃ point ∈ value, point.val % 6 = 4 := by
  unfold z180K30ProjectiveD6UBlockR4PilotV97 at hvalue
  rcases List.mem_filter.mp hvalue with ⟨hraw, hne⟩
  unfold z180K30ProjectiveD6URawBlockR4PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  by_contra hmarker
  push_neg at hmarker
  have hsub := (List.mem_sublistsLen.mp hsuffix).1
  have hlength : suffix.length = 5 :=
    (List.mem_sublistsLen.mp hsuffix).2
  have hfilterSuffix :
      suffix.filter (fun point => point.val % 6 != 4) = suffix := by
    apply List.filter_eq_self.mpr
    intro point hpoint
    have hneResidue : point.val % 6 ≠ 4 :=
      hmarker point (by simp [hpoint])
    simpa using hneResidue
  have hfilterTail :
      z180K30ProjectiveD6UTailR4PilotV97.filter
          (fun point => point.val % 6 != 4) =
        [6, 12, 18, 24, 30] := by
    decide
  have hsubZero : List.Sublist suffix ([6, 12, 18, 24, 30] : RawSet) := by
    rw [← hfilterSuffix, ← hfilterTail]
    exact hsub.filter _
  have hsuffixZero : suffix = ([6, 12, 18, 24, 30] : RawSet) :=
    hsubZero.eq_of_length (by simpa using hlength)
  simp [hsuffixZero, z180K30ProjectiveD6UAPilotV97] at hne

theorem z180_k30_projective_d6_u_block_r4_residues_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR4PilotV97)
    (point : RawPoint) (hpoint : point ∈ value) :
    point.val % 6 = 0 ∨ point.val % 6 = 4 := by
  unfold z180K30ProjectiveD6UBlockR4PilotV97 at hvalue
  have hraw := (List.mem_filter.mp hvalue).1
  unfold z180K30ProjectiveD6URawBlockR4PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  simp only [List.singleton_append, List.mem_cons] at hpoint
  rcases hpoint with hzero | hsuffixPoint
  · subst point
    simp
  · have htailPoint : point ∈ z180K30ProjectiveD6UTailR4PilotV97 :=
      (List.mem_sublistsLen.mp hsuffix).1.subset hsuffixPoint
    have hclassify : ∀ candidate : RawPoint,
        candidate ∈ z180K30ProjectiveD6UTailR4PilotV97 →
          candidate.val % 6 = 0 ∨ candidate.val % 6 = 4 := by
      decide
    exact hclassify point htailPoint

theorem z180_k30_projective_d6_u_block_r5_nodup_pilot_v97 :
    z180K30ProjectiveD6UBlockR5PilotV97.Nodup := by
  unfold z180K30ProjectiveD6UBlockR5PilotV97
  unfold z180K30ProjectiveD6URawBlockR5PilotV97
  unfold z180K30ProjectiveD6UCombPilotV97
  apply List.Nodup.filter
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide

theorem z180_k30_projective_d6_u_block_r5_marker_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR5PilotV97) :
    ∃ point ∈ value, point.val % 6 = 5 := by
  unfold z180K30ProjectiveD6UBlockR5PilotV97 at hvalue
  rcases List.mem_filter.mp hvalue with ⟨hraw, hne⟩
  unfold z180K30ProjectiveD6URawBlockR5PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  by_contra hmarker
  push_neg at hmarker
  have hsub := (List.mem_sublistsLen.mp hsuffix).1
  have hlength : suffix.length = 5 :=
    (List.mem_sublistsLen.mp hsuffix).2
  have hfilterSuffix :
      suffix.filter (fun point => point.val % 6 != 5) = suffix := by
    apply List.filter_eq_self.mpr
    intro point hpoint
    have hneResidue : point.val % 6 ≠ 5 :=
      hmarker point (by simp [hpoint])
    simpa using hneResidue
  have hfilterTail :
      z180K30ProjectiveD6UTailR5PilotV97.filter
          (fun point => point.val % 6 != 5) =
        [6, 12, 18, 24, 30] := by
    decide
  have hsubZero : List.Sublist suffix ([6, 12, 18, 24, 30] : RawSet) := by
    rw [← hfilterSuffix, ← hfilterTail]
    exact hsub.filter _
  have hsuffixZero : suffix = ([6, 12, 18, 24, 30] : RawSet) :=
    hsubZero.eq_of_length (by simpa using hlength)
  simp [hsuffixZero, z180K30ProjectiveD6UAPilotV97] at hne

theorem z180_k30_projective_d6_u_block_r5_residues_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR5PilotV97)
    (point : RawPoint) (hpoint : point ∈ value) :
    point.val % 6 = 0 ∨ point.val % 6 = 5 := by
  unfold z180K30ProjectiveD6UBlockR5PilotV97 at hvalue
  have hraw := (List.mem_filter.mp hvalue).1
  unfold z180K30ProjectiveD6URawBlockR5PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  simp only [List.singleton_append, List.mem_cons] at hpoint
  rcases hpoint with hzero | hsuffixPoint
  · subst point
    simp
  · have htailPoint : point ∈ z180K30ProjectiveD6UTailR5PilotV97 :=
      (List.mem_sublistsLen.mp hsuffix).1.subset hsuffixPoint
    have hclassify : ∀ candidate : RawPoint,
        candidate ∈ z180K30ProjectiveD6UTailR5PilotV97 →
          candidate.val % 6 = 0 ∨ candidate.val % 6 = 5 := by
      decide
    exact hclassify point htailPoint

theorem z180_k30_projective_d6_u_blocks_r1_r2_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR1PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR2PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r1_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r2_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega

theorem z180_k30_projective_d6_u_blocks_r1_r3_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR1PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR3PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r1_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r3_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega

theorem z180_k30_projective_d6_u_blocks_r1_r4_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR1PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR4PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r1_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r4_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega

theorem z180_k30_projective_d6_u_blocks_r1_r5_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR1PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR5PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r1_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r5_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega

theorem z180_k30_projective_d6_u_blocks_r2_r3_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR2PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR3PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r2_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r3_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega

theorem z180_k30_projective_d6_u_blocks_r2_r4_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR2PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR4PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r2_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r4_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega

theorem z180_k30_projective_d6_u_blocks_r2_r5_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR2PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR5PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r2_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r5_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega

theorem z180_k30_projective_d6_u_blocks_r3_r4_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR3PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR4PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r3_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r4_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega

theorem z180_k30_projective_d6_u_blocks_r3_r5_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR3PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR5PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r3_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r5_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega

theorem z180_k30_projective_d6_u_blocks_r4_r5_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR4PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR5PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r4_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r5_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega


private theorem z180_k30_projective_d6_u_erase_cons_flatten_pilot_v97
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (head : alpha) (blocks : List (List alpha)) :
    (head :: blocks.flatten).eraseDups =
      head :: (blocks.map fun block =>
        block.filter (fun value => value != head)).flatten.eraseDups := by
  rw [List.eraseDups_cons, List.filter_flatten]
  have hmap :
      (blocks.map fun block => block.filter (fun value => !value == head)) =
        blocks.map fun block => block.filter (fun value => value != head) := by
    apply List.map_congr_left
    intro block hblock
    apply List.filter_congr
    intro value hvalue
    change (!(value == head)) = (!(value == head))
    rfl
  rw [hmap]

private theorem z180_k30_projective_d6_u_erase_nodup_pilot_v97
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    ∀ {values : List alpha}, values.Nodup → values.eraseDups = values
  | [], _ => rfl
  | head :: tail, hnodup => by
      have hhead : head ∉ tail := (List.nodup_cons.mp hnodup).1
      have htail : tail.Nodup := (List.nodup_cons.mp hnodup).2
      have hfilter : tail.filter (fun item => !item == head) = tail := by
        apply List.filter_eq_self.mpr
        intro item hitem
        have hne : item ≠ head := by
          intro hequal
          exact hhead (hequal ▸ hitem)
        simp [hne]
      rw [List.eraseDups_cons, hfilter,
        z180_k30_projective_d6_u_erase_nodup_pilot_v97 htail]

private theorem z180_k30_projective_d6_u_removeAll_self_pilot_v97
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] (values : List alpha) :
    values.removeAll values = [] := by
  unfold List.removeAll
  apply List.filter_eq_nil_iff.mpr
  intro item hitem hkeep
  have helem : values.elem item = true := List.elem_eq_true_of_mem hitem
  have hfalse : values.elem item = false :=
    Bool.eq_false_of_not_eq_true' hkeep
  rw [helem] at hfalse
  cases hfalse

private theorem z180_k30_projective_d6_u_erase_double_pilot_v97
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (values : List alpha) (hnodup : values.Nodup) :
    (values ++ values).eraseDups = values := by
  rw [List.eraseDups_append,
    z180_k30_projective_d6_u_erase_nodup_pilot_v97 hnodup,
    z180_k30_projective_d6_u_removeAll_self_pilot_v97,
    List.eraseDups_nil, List.append_nil]

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_filtered_raw_blocks_twice_pilot_v97 :
    (z180K30ProjectiveD6URawBlocksTwicePilotV97.map fun block =>
      block.filter (fun value =>
        value != z180K30ProjectiveD6UAPilotV97)).flatten =
      z180K30ProjectiveD6UCanonicalTailPilotV97 ++
        z180K30ProjectiveD6UCanonicalTailPilotV97 := by
  rfl

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_canonical_tail_nodup_pilot_v97 :
    z180K30ProjectiveD6UCanonicalTailPilotV97.Nodup := by
  unfold z180K30ProjectiveD6UCanonicalTailPilotV97
  have h45 := z180_k30_projective_d6_u_block_r4_nodup_pilot_v97.append
    z180_k30_projective_d6_u_block_r5_nodup_pilot_v97
    z180_k30_projective_d6_u_blocks_r4_r5_disjoint_pilot_v97
  have h345 := z180_k30_projective_d6_u_block_r3_nodup_pilot_v97.append h45
    (List.disjoint_append_right.mpr
      ⟨z180_k30_projective_d6_u_blocks_r3_r4_disjoint_pilot_v97,
       z180_k30_projective_d6_u_blocks_r3_r5_disjoint_pilot_v97⟩)
  have h2345 := z180_k30_projective_d6_u_block_r2_nodup_pilot_v97.append h345
    (List.disjoint_append_right.mpr
      ⟨z180_k30_projective_d6_u_blocks_r2_r3_disjoint_pilot_v97,
       List.disjoint_append_right.mpr
        ⟨z180_k30_projective_d6_u_blocks_r2_r4_disjoint_pilot_v97,
         z180_k30_projective_d6_u_blocks_r2_r5_disjoint_pilot_v97⟩⟩)
  exact z180_k30_projective_d6_u_block_r1_nodup_pilot_v97.append h2345
    (List.disjoint_append_right.mpr
      ⟨z180_k30_projective_d6_u_blocks_r1_r2_disjoint_pilot_v97,
       List.disjoint_append_right.mpr
        ⟨z180_k30_projective_d6_u_blocks_r1_r3_disjoint_pilot_v97,
         List.disjoint_append_right.mpr
          ⟨z180_k30_projective_d6_u_blocks_r1_r4_disjoint_pilot_v97,
           z180_k30_projective_d6_u_blocks_r1_r5_disjoint_pilot_v97⟩⟩⟩)

private theorem z180_k30_projective_d6_u_not_mem_filter_self_pilot_v97
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (head : alpha) (values : List alpha) :
    head ∉ values.filter (fun value => value != head) := by
  intro hmember
  have hkeep := (List.mem_filter.mp hmember).2
  simpa using hkeep

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_canonical_nodup_pilot_v97 :
    z180K30ProjectiveD6UCanonicalPilotV97.Nodup := by
  unfold z180K30ProjectiveD6UCanonicalPilotV97
  rw [List.nodup_cons]
  constructor
  · have h1 : z180K30ProjectiveD6UAPilotV97 ∉
        z180K30ProjectiveD6UBlockR1PilotV97 := by
      unfold z180K30ProjectiveD6UBlockR1PilotV97
      exact z180_k30_projective_d6_u_not_mem_filter_self_pilot_v97 _ _
    have h2 : z180K30ProjectiveD6UAPilotV97 ∉
        z180K30ProjectiveD6UBlockR2PilotV97 := by
      unfold z180K30ProjectiveD6UBlockR2PilotV97
      exact z180_k30_projective_d6_u_not_mem_filter_self_pilot_v97 _ _
    have h3 : z180K30ProjectiveD6UAPilotV97 ∉
        z180K30ProjectiveD6UBlockR3PilotV97 := by
      unfold z180K30ProjectiveD6UBlockR3PilotV97
      exact z180_k30_projective_d6_u_not_mem_filter_self_pilot_v97 _ _
    have h4 : z180K30ProjectiveD6UAPilotV97 ∉
        z180K30ProjectiveD6UBlockR4PilotV97 := by
      unfold z180K30ProjectiveD6UBlockR4PilotV97
      exact z180_k30_projective_d6_u_not_mem_filter_self_pilot_v97 _ _
    have h5 : z180K30ProjectiveD6UAPilotV97 ∉
        z180K30ProjectiveD6UBlockR5PilotV97 := by
      unfold z180K30ProjectiveD6UBlockR5PilotV97
      exact z180_k30_projective_d6_u_not_mem_filter_self_pilot_v97 _ _
    simp only [z180K30ProjectiveD6UCanonicalTailPilotV97,
      List.mem_append, not_or]
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact z180_k30_projective_d6_u_canonical_tail_nodup_pilot_v97

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_unique_canonical_pilot_v97 :
    normalizedProjectiveUniqueUChoicesV89 6 =
      z180K30ProjectiveD6UCanonicalPilotV97 := by
  unfold normalizedProjectiveUniqueUChoicesV89
  rw [z180_k30_projective_d6_u_choices_raw_blocks_pilot_v97,
    z180_k30_projective_d6_u_erase_cons_flatten_pilot_v97,
    z180_k30_projective_d6_u_filtered_raw_blocks_twice_pilot_v97,
    z180_k30_projective_d6_u_erase_double_pilot_v97
      z180K30ProjectiveD6UCanonicalTailPilotV97
      z180_k30_projective_d6_u_canonical_tail_nodup_pilot_v97]
  rfl

theorem z180_k30_projective_d6_u_complete_algebraic_pilot_v97 :
    z180K30ProjectiveCompletenessV97D6USourceGrouped.Perm
      (normalizedProjectiveUniqueUChoicesV89 6) := by
  exact z180_k30_projective_d6_u_source_perm_canonical_pilot_v97.trans
    (List.Perm.of_eq z180_k30_projective_d6_u_unique_canonical_pilot_v97.symm)

#print axioms z180_k30_projective_d6_u_complete_algebraic_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
