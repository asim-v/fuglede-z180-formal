import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermBasePilotV97
import Mathlib.Data.List.Sublists

/-!
Structural combination-tree fallback for the divisor-three V enumeration.
After six splitting levels, every leaf contains at most ten `RawSet` values.
The tree itself is a structural replay of `List.sublistsLen_succ_cons`.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombPilotV97
    (prefix domain : RawSet) (length : Nat) : List RawSet :=
  (List.sublistsLen length domain).map fun suffix => prefix ++ suffix

theorem z180_k30_projective_d3_v_comb_succ_cons_pilot_v97
    (prefix : RawSet) (head : RawPoint) (tail : RawSet) (length : Nat) :
    z180K30ProjectiveD3VCombPilotV97 prefix (head :: tail) (length + 1) =
      z180K30ProjectiveD3VCombPilotV97 prefix tail (length + 1) ++
        z180K30ProjectiveD3VCombPilotV97
          (prefix ++ [head]) tail length := by
  simp only [z180K30ProjectiveD3VCombPilotV97,
    List.sublistsLen_succ_cons, List.map_append, List.map_map,
    Function.comp_apply, List.append_assoc, List.singleton_append]

def z180K30ProjectiveD3VCombChunksPilotV97 :
    Nat -> RawSet -> RawSet -> Nat -> List (List RawSet)
  | 0, prefix, domain, length =>
      [z180K30ProjectiveD3VCombPilotV97 prefix domain length]
  | _ + 1, prefix, domain, 0 =>
      [z180K30ProjectiveD3VCombPilotV97 prefix domain 0]
  | _ + 1, prefix, [], length + 1 =>
      [z180K30ProjectiveD3VCombPilotV97 prefix [] (length + 1)]
  | fuel + 1, prefix, head :: tail, length + 1 =>
      z180K30ProjectiveD3VCombChunksPilotV97
          fuel prefix tail (length + 1) ++
        z180K30ProjectiveD3VCombChunksPilotV97
          fuel (prefix ++ [head]) tail length

theorem z180_k30_projective_d3_v_comb_chunks_flatten_pilot_v97 :
    forall fuel prefix domain length,
      (z180K30ProjectiveD3VCombChunksPilotV97
        fuel prefix domain length).flatten =
        z180K30ProjectiveD3VCombPilotV97 prefix domain length
  | 0, prefix, domain, length => by
      simp [z180K30ProjectiveD3VCombChunksPilotV97]
  | _ + 1, prefix, domain, 0 => by
      simp [z180K30ProjectiveD3VCombChunksPilotV97]
  | fuel + 1, prefix, [], length + 1 => by
      simp [z180K30ProjectiveD3VCombChunksPilotV97]
  | fuel + 1, prefix, head :: tail, length + 1 => by
      rw [z180K30ProjectiveD3VCombChunksPilotV97, List.flatten_append,
        z180_k30_projective_d3_v_comb_chunks_flatten_pilot_v97,
        z180_k30_projective_d3_v_comb_chunks_flatten_pilot_v97,
        z180_k30_projective_d3_v_comb_succ_cons_pilot_v97]

def z180K30ProjectiveD3VPositiveTailCombPilotV97 : RawSet :=
  [3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33]

def z180K30ProjectiveD3VCombChunkTreePilotV97 : List (List RawSet) :=
  z180K30ProjectiveD3VCombChunksPilotV97 6 [0]
    z180K30ProjectiveD3VPositiveTailCombPilotV97 5

theorem z180_k30_projective_d3_v_comb_chunk_tree_flatten_pilot_v97 :
    z180K30ProjectiveD3VCombChunkTreePilotV97.flatten =
      (List.sublistsLen 5
        z180K30ProjectiveD3VPositiveTailCombPilotV97).map
          (List.cons (0 : RawPoint)) := by
  rw [z180K30ProjectiveD3VCombChunkTreePilotV97,
    z180_k30_projective_d3_v_comb_chunks_flatten_pilot_v97]
  rfl

end Fuglede.Z180K30ExceptionalRawV2
