#!/usr/bin/env python3
"""Generate an isolated, bounded structural completeness pilot for D4-V."""

from __future__ import annotations

import hashlib
import importlib.util
from collections import OrderedDict
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_DIR = SCRIPT_DIR.parent
LEAN_DIR = REPO_DIR / "fuglede_lean" / "Fuglede"
ACTIVE_GENERATOR = SCRIPT_DIR / "generate_z180_k30_projective_profile_audit_v97.py"
SOURCE_BASE = "Z180K30ExceptionalProjectiveProfileCompletenessV97D4VBase"
PREFIX = "Z180K30ExceptionalProjectiveProfileD4VAlgebraic"
CHUNK_SIZES = (1, 5, 5, 10, 5, 10, 10, 10)


def load_generator():
    spec = importlib.util.spec_from_file_location("profile_v97_generator", ACTIVE_GENERATOR)
    if spec is None or spec.loader is None:
        raise SystemExit("FAIL CLOSED: cannot load active V97 generator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def lean_sublists_len(length: int, values: list[int]) -> list[tuple[int, ...]]:
    if length == 0:
        return [()]
    if not values:
        return []
    head, tail = values[0], values[1:]
    return (
        lean_sublists_len(length, tail) +
        [(head, *suffix) for suffix in lean_sublists_len(length - 1, tail)]
    )


def split_comb_chunks(
    fuel: int, prefix: tuple[int, ...], domain: tuple[int, ...], length: int
) -> list[tuple[tuple[int, ...], tuple[int, ...], int, list[tuple[int, ...]]]]:
    values = [prefix + suffix for suffix in lean_sublists_len(length, list(domain))]
    if fuel == 0 or length == 0 or (not domain and length > 0):
        return [(prefix, domain, length, values)]
    head, tail = domain[0], domain[1:]
    return (
        split_comb_chunks(fuel - 1, prefix, tail, length) +
        split_comb_chunks(fuel - 1, prefix + (head,), tail, length - 1)
    )


def model():
    generator = load_generator()
    _, canonical_itertools = generator.normalized_choices(4)
    groups: OrderedDict[tuple[int, ...], list[tuple[int, ...]]] = OrderedDict()
    for values in canonical_itertools:
        groups.setdefault(generator.v_profile(4, values), []).append(values)
    source_values = [values for members in groups.values() for values in members]
    source_index = {values: index for index, values in enumerate(source_values)}
    tail = tuple(range(4, 36, 4))
    canonical = [(0, *suffix) for suffix in lean_sublists_len(5, list(tail))]
    chunks = split_comb_chunks(3, (0,), tail, 5)
    if [len(chunk[3]) for chunk in chunks] != list(CHUNK_SIZES):
        raise SystemExit("FAIL CLOSED: D4-V structural chunk census drift")
    if [values for chunk in chunks for values in chunk[3]] != canonical:
        raise SystemExit("FAIL CLOSED: D4-V structural flatten drift")
    indices = [source_index[values] for values in canonical]
    if len(indices) != 56 or sorted(indices) != list(range(56)):
        raise SystemExit("FAIL CLOSED: D4-V index permutation drift")
    index_chunks = []
    for prefix, domain, length, values in chunks:
        index_chunks.append((prefix, domain, length, [source_index[value] for value in values]))
    return tail, indices, index_chunks


def lean_list(values) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def core_source(tail: tuple[int, ...], indices: list[int]) -> str:
    return f"""import Fuglede.{SOURCE_BASE}
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sublists

/-! Isolated bounded structural D4-V completeness pilot. -/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem eraseDups_eq_self_of_nodup_d4v_pilot
    {{alpha : Type}} [BEq alpha] [LawfulBEq alpha] :
    forall {{values : List alpha}}, values.Nodup -> values.eraseDups = values
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
    {{alpha : Type}} [DecidableEq alpha]
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
    {{alpha : Type}} [DecidableEq alpha]
    (point : alpha) (values : List (List alpha)) :
    (values.map (List.cons point)).filter
      (fun set => decide (point ∈ set)) =
        values.map (List.cons point) := by
  apply List.filter_eq_self.mpr
  intro set hset
  obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hset
  exact decide_eq_true (List.mem_cons_self)

def z180K30ProjectiveD4VPositiveTailPilotV97 : RawSet :=
  {lean_list(tail)}

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
  {lean_list(indices)}

def z180K30ProjectiveD4VSourceAtPilotV97 (index : Nat) : RawSet :=
  z180K30ProjectiveCompletenessV97D4VSourceGrouped.getD index []

def z180K30ProjectiveD4VCanonicalIndexedPilotV97 : List RawSet :=
  z180K30ProjectiveD4VCanonicalIndicesPilotV97.map
    z180K30ProjectiveD4VSourceAtPilotV97

theorem z180_k30_projective_d4_v_source_length_pilot_v97 :
    z180K30ProjectiveCompletenessV97D4VSourceGrouped.length = 56 := by
  rfl

private theorem map_range_getD_eq_self_d4v_pilot
    {{alpha : Type}} (values : List alpha) (fallback : alpha) :
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
"""


def leaf_stem(index: int) -> str:
    return f"{PREFIX}Leaf{index:02d}PilotV97"


def leaf_theorem(index: int) -> str:
    return f"z180_k30_projective_d4_v_algebraic_leaf_{index:02d}_pilot_v97"


def leaf_source(index: int, chunk) -> str:
    prefix, domain, length, indices = chunk
    return f"""import Fuglede.{PREFIX}CorePilotV97

/-! D4-V bounded algebraic bridge leaf {index}, size {len(indices)}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem {leaf_theorem(index)} :
    {lean_list(indices)}.map z180K30ProjectiveD4VSourceAtPilotV97 =
      z180K30ProjectiveD4VCombPilotV97
        {lean_list(prefix)} {lean_list(domain)} {length} := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def aggregate_source(index_chunks) -> str:
    imports = "\n".join(
        f"import Fuglede.{leaf_stem(index)}" for index in range(len(index_chunks))
    )
    chunks = ",\n    ".join(lean_list(chunk[3]) for chunk in index_chunks)
    recurrence = "\n    ".join(
        f"rw [z180_k30_projective_d4_v_comb_succ_cons_pilot_v97]"
        for _ in range(3)
    )
    # Eight leaf equalities close the list-of-lists equality constructor-wise.
    leaf_proof = "\n".join(
        ("  · " if index == 0 else "    · ") + f"exact {leaf_theorem(index)}"
        if index == 0 else
        ("    constructor\n" if index + 1 < len(index_chunks) else "") +
        f"    · exact {leaf_theorem(index)}"
        for index in range(len(index_chunks))
    )
    # Use `simp only` on the literal eight constructors, then each leaf theorem.
    leaf_names = ",\n    ".join(leaf_theorem(index) for index in range(len(index_chunks)))
    return f"""{imports}

/-! Aggregate of eight bounded D4-V algebraic bridge leaves. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4VCanonicalIndexChunksPilotV97 : List (List Nat) :=
  [{chunks}]

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
"""


def expected():
    tail, indices, chunks = model()
    files = {
        LEAN_DIR / f"{PREFIX}CorePilotV97.lean": core_source(tail, indices),
        LEAN_DIR / f"{PREFIX}AggregatePilotV97.lean": aggregate_source(chunks),
    }
    for index, chunk in enumerate(chunks):
        files[LEAN_DIR / f"{leaf_stem(index)}.lean"] = leaf_source(index, chunk)
    return files


def main() -> None:
    for path, source in expected().items():
        digest = hashlib.sha256(source.encode()).hexdigest().upper()
        status = "PASS" if path.exists() and path.read_text(encoding="utf-8") == source else "WROTE"
        if status == "WROTE":
            path.write_text(source, encoding="utf-8", newline="\n")
        print(f"{status} {path.name} sha256={digest}")


if __name__ == "__main__":
    main()
