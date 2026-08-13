import Fuglede.Z180K30ExceptionalProjectiveProfileD4VAlgebraicLeaf00PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4VAlgebraicLeaf01PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4VAlgebraicLeaf02PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4VAlgebraicLeaf03PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4VAlgebraicLeaf04PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4VAlgebraicLeaf05PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4VAlgebraicLeaf06PilotV97
import Fuglede.Z180K30ExceptionalProjectiveProfileD4VAlgebraicLeaf07PilotV97

/-! Aggregate of eight bounded D4-V algebraic bridge leaves. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4VCanonicalIndexChunksPilotV97 : List (List Nat) :=
  [[5],
    [17, 29, 41, 28, 16],
    [15, 35, 53, 52, 34],
    [27, 51, 55, 50, 40, 49, 48, 26, 33, 14],
    [4, 13, 25, 39, 24],
    [12, 32, 47, 46, 23, 45, 54, 38, 44, 22],
    [3, 11, 21, 37, 10, 31, 43, 20, 42, 36],
    [2, 9, 19, 8, 30, 18, 1, 7, 6, 0]]

theorem z180_k30_projective_d4_v_index_chunks_flatten_pilot_v97 :
    z180K30ProjectiveD4VCanonicalIndexChunksPilotV97.flatten =
      z180K30ProjectiveD4VCanonicalIndicesPilotV97 := by
  rfl

theorem z180_k30_projective_d4_v_chunk_targets_flatten_pilot_v97 :
    [
      z180K30ProjectiveD4VCombPilotV97 [0] [16, 20, 24, 28, 32] 5,
      z180K30ProjectiveD4VCombPilotV97 [0, 12] [16, 20, 24, 28, 32] 4,
      z180K30ProjectiveD4VCombPilotV97 [0, 8] [16, 20, 24, 28, 32] 4,
      z180K30ProjectiveD4VCombPilotV97 [0, 8, 12] [16, 20, 24, 28, 32] 3,
      z180K30ProjectiveD4VCombPilotV97 [0, 4] [16, 20, 24, 28, 32] 4,
      z180K30ProjectiveD4VCombPilotV97 [0, 4, 12] [16, 20, 24, 28, 32] 3,
      z180K30ProjectiveD4VCombPilotV97 [0, 4, 8] [16, 20, 24, 28, 32] 3,
      z180K30ProjectiveD4VCombPilotV97 [0, 4, 8, 12] [16, 20, 24, 28, 32] 2
    ].flatten =
      z180K30ProjectiveD4VCombPilotV97 [0]
        z180K30ProjectiveD4VPositiveTailPilotV97 5 := by
  rfl

theorem z180_k30_projective_d4_v_chunk_bridges_pilot_v97 :
    (z180K30ProjectiveD4VCanonicalIndexChunksPilotV97.map fun indices =>
      indices.map z180K30ProjectiveD4VSourceAtPilotV97) = [
      z180K30ProjectiveD4VCombPilotV97 [0] [16, 20, 24, 28, 32] 5,
      z180K30ProjectiveD4VCombPilotV97 [0, 12] [16, 20, 24, 28, 32] 4,
      z180K30ProjectiveD4VCombPilotV97 [0, 8] [16, 20, 24, 28, 32] 4,
      z180K30ProjectiveD4VCombPilotV97 [0, 8, 12] [16, 20, 24, 28, 32] 3,
      z180K30ProjectiveD4VCombPilotV97 [0, 4] [16, 20, 24, 28, 32] 4,
      z180K30ProjectiveD4VCombPilotV97 [0, 4, 12] [16, 20, 24, 28, 32] 3,
      z180K30ProjectiveD4VCombPilotV97 [0, 4, 8] [16, 20, 24, 28, 32] 3,
      z180K30ProjectiveD4VCombPilotV97 [0, 4, 8, 12] [16, 20, 24, 28, 32] 2
    ] := by
  unfold z180K30ProjectiveD4VCanonicalIndexChunksPilotV97
  congr 1

theorem z180_k30_projective_d4_v_indexed_sublists_chunked_pilot_v97 :
    z180K30ProjectiveD4VCanonicalIndexedPilotV97 =
      z180K30ProjectiveD4VCombPilotV97 [0]
        z180K30ProjectiveD4VPositiveTailPilotV97 5 := by
  unfold z180K30ProjectiveD4VCanonicalIndexedPilotV97
  rw [← z180_k30_projective_d4_v_index_chunks_flatten_pilot_v97,
    List.map_flatten, z180_k30_projective_d4_v_chunk_bridges_pilot_v97,
    z180_k30_projective_d4_v_chunk_targets_flatten_pilot_v97]

theorem z180_k30_projective_d4_v_complete_algebraic_pilot_v97 :
    z180K30ProjectiveCompletenessV97D4VSourceGrouped.Perm
      (normalizedProjectiveUniqueVChoicesV89 4) := by
  exact z180_k30_projective_d4_v_source_perm_indexed_pilot_v97.trans
    (List.Perm.of_eq
      (z180_k30_projective_d4_v_indexed_sublists_chunked_pilot_v97.trans
        z180_k30_projective_d4_v_unique_sublists_pilot_v97.symm))

#print axioms z180_k30_projective_d4_v_complete_algebraic_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
