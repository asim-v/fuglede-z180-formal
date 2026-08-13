#!/usr/bin/env python3
"""Generate and authenticate the isolated bounded D4-U algebraic bridge."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_DIR = SCRIPT_DIR.parent
LEAN_DIR = REPO_DIR / "fuglede_lean" / "Fuglede"
ACTIVE_GENERATOR = SCRIPT_DIR / "generate_z180_k30_projective_profile_audit_v97.py"
BASE = LEAN_DIR / "Z180K30ExceptionalProjectiveProfileCompletenessV97D4UBase.lean"
CORE = LEAN_DIR / "Z180K30ExceptionalProjectiveProfileD4UAlgebraicCorePilotV97.lean"
AGGREGATE = LEAN_DIR / "Z180K30ExceptionalProjectiveProfileD4UAlgebraicAggregatePilotV97.lean"
MANIFEST = SCRIPT_DIR / "z180_k30_projective_profile_d4u_algebraic_v97.manifest.json"
PREFIX = "Z180K30ExceptionalProjectiveProfileD4UAlgebraic"
INDEX_BUCKET_COUNT = 17
SOURCE_DEF = "def z180K30ProjectiveCompletenessV97D4USourceGrouped"
PROFILE_DEF = re.compile(
    r"def\s+(z180K30ProfileV97D4U\d+M\d+)\s*:\s*RawSet\s*:=\s*\[([^\]]*)\]"
)
PROFILE_NAME = re.compile(r"z180K30ProfileV97D4U\d+M\d+")
FORBIDDEN_WORDS = (
    "native_" + "decide", "un" + "safe", "sor" + "ry", "axi" + "om",
    "cho" + "ose", "dr" + "op", "ta" + "ke",
)
FORBIDDEN = re.compile(r"\b(?:" + "|".join(FORBIDDEN_WORDS) + r")\b")


@dataclass(frozen=True)
class Chunk:
    number: int
    residue: int
    frame: tuple[int, ...]
    domain: tuple[int, ...]
    length: int
    values: tuple[tuple[int, ...], ...]
    indices: tuple[int, ...]
    keys: tuple[int, ...]

    @property
    def tag(self) -> str:
        return f"{self.number:02d}"

    @property
    def module(self) -> str:
        return f"{PREFIX}Leaf{self.tag}PilotV97"

    @property
    def path(self) -> Path:
        return LEAN_DIR / f"{self.module}.lean"


def load_active():
    spec = importlib.util.spec_from_file_location("profile_v97_generator_d4u", ACTIVE_GENERATOR)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load active V97 generator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def file_sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def relative(path: Path) -> str:
    return path.relative_to(REPO_DIR).as_posix()


def lean_list(values) -> str:
    return "[" + ", ".join(str(int(value)) for value in values) + "]"


def lean_sublists_len(length: int, values: tuple[int, ...]) -> list[tuple[int, ...]]:
    if length == 0:
        return [()]
    if not values:
        return []
    head, tail = values[0], values[1:]
    return lean_sublists_len(length, tail) + [
        (head, *suffix) for suffix in lean_sublists_len(length - 1, tail)
    ]


def split_chunks(
    fuel: int, frame: tuple[int, ...], domain: tuple[int, ...], length: int
) -> list[tuple[tuple[int, ...], tuple[int, ...], int, tuple[tuple[int, ...], ...]]]:
    values = tuple(frame + suffix for suffix in lean_sublists_len(length, domain))
    if fuel == 0 or length == 0 or not domain:
        return [(frame, domain, length, values)]
    head, tail = domain[0], domain[1:]
    return split_chunks(fuel - 1, frame, tail, length) + split_chunks(
        fuel - 1, frame + (head,), tail, length - 1
    )


def parse_source_names(text: str) -> tuple[str, ...]:
    start = text.index(SOURCE_DEF)
    assign = text.index(":=", start)
    left = text.index("[", assign)
    right = text.index("]", left)
    return tuple(PROFILE_NAME.findall(text[left : right + 1]))


def parse_member_values(paths: list[Path]) -> dict[str, tuple[int, ...]]:
    result: dict[str, tuple[int, ...]] = {}
    for path in paths:
        source = path.read_text(encoding="utf-8")
        for match in PROFILE_DEF.finditer(source):
            values = tuple(int(value) for value in re.findall(r"\d+", match.group(2)))
            previous = result.setdefault(match.group(1), values)
            if previous != values:
                raise RuntimeError(f"conflicting member definition {match.group(1)}")
    return result


def build_model():
    active = load_active()
    u_values, _ = active.normalized_choices(4)
    groups: dict[tuple[int, ...], list[tuple[int, ...]]] = {}
    for values in u_values:
        groups.setdefault(active.u_profile(4, values), []).append(values)
    expected_source = tuple(values for members in groups.values() for values in members)

    member_paths = sorted(LEAN_DIR.glob("Z180K30ExceptionalProjectiveProfileMembersV97D4S*.lean"))
    source_names = parse_source_names(BASE.read_text(encoding="utf-8"))
    definitions = parse_member_values(member_paths)
    actual_source = tuple(definitions[name] for name in source_names)
    if actual_source != expected_source:
        raise RuntimeError("active D4-U grouped source differs from reconstructed source")
    if len(actual_source) != 168 or len(set(actual_source)) != 168:
        raise RuntimeError("D4-U grouped source census or uniqueness drift")
    source_index = {values: index for index, values in enumerate(actual_source)}

    blocks: dict[int, tuple[tuple[int, ...], ...]] = {}
    tails: dict[int, tuple[int, ...]] = {}
    chunks: list[Chunk] = []
    canonical: list[tuple[int, ...]] = []
    for residue in range(1, 9):
        tail = tuple(
            value for value in range(1, 36) if value % 9 in (0, residue)
        )
        values = tuple((0, *suffix) for suffix in lean_sublists_len(5, tail))
        if len(values) != 21:
            raise RuntimeError(f"D4-U residue {residue} block census drift")
        tails[residue] = tail
        blocks[residue] = values
        canonical.extend(values)
        specs = split_chunks(2, (0,), tail, 5)
        if [len(spec[3]) for spec in specs] != [1, 5, 5, 10]:
            raise RuntimeError(f"D4-U residue {residue} chunk census drift")
        for frame, domain, length, leaf_values in specs:
            chunks.append(Chunk(
                number=len(chunks),
                residue=residue,
                frame=frame,
                domain=domain,
                length=length,
                values=leaf_values,
                indices=tuple(source_index[value] for value in leaf_values),
                keys=tuple(active.normalized_raw_set_key(value) for value in leaf_values),
            ))

    canonical_tuple = tuple(canonical)
    indices = tuple(source_index[value] for value in canonical_tuple)
    if len(canonical_tuple) != 168 or set(canonical_tuple) != set(actual_source):
        raise RuntimeError("D4-U canonical block union drift")
    if sorted(indices) != list(range(168)):
        raise RuntimeError("D4-U canonical index permutation drift")
    if len(chunks) != 32 or max(len(chunk.values) for chunk in chunks) != 10:
        raise RuntimeError("D4-U bounded chunk DAG drift")
    if tuple(value for chunk in chunks for value in chunk.values) != canonical_tuple:
        raise RuntimeError("D4-U chunk flatten drift")
    all_keys = tuple(key for chunk in chunks for key in chunk.keys)
    if len(set(all_keys)) != 168:
        raise RuntimeError("D4-U normalized raw-set keys are not injective")

    selections = tuple([(residue,) for residue in range(9)] + [
        (first, second) for first in range(9) for second in range(9)
    ])
    occurrences = tuple(canonical_tuple + canonical_tuple)
    active_occurrences, _ = active.normalized_choice_occurrences(4)
    if Counter(active_occurrences) != Counter(occurrences):
        raise RuntimeError("D4-U V88 occurrence multiset differs from double canonical block")
    return member_paths, source_names, actual_source, tails, blocks, chunks, indices, selections


def tail_name(residue: int) -> str:
    return f"z180K30ProjectiveD4UTailR{residue:02d}PilotV97"


def block_name(residue: int) -> str:
    return f"z180K30ProjectiveD4UBlockR{residue:02d}PilotV97"


def leaf_indices_name(chunk: Chunk) -> str:
    return f"z180K30ProjectiveD4ULeaf{chunk.tag}IndicesPilotV97"


def leaf_target_name(chunk: Chunk) -> str:
    return f"z180K30ProjectiveD4ULeaf{chunk.tag}TargetPilotV97"


def leaf_keys_name(chunk: Chunk) -> str:
    return f"z180K30ProjectiveD4ULeaf{chunk.tag}KeysPilotV97"


def leaf_bridge_theorem(chunk: Chunk) -> str:
    return f"z180_k30_projective_d4_u_leaf_{chunk.tag}_bridge_pilot_v97"


def leaf_keys_theorem(chunk: Chunk) -> str:
    return f"z180_k30_projective_d4_u_leaf_{chunk.tag}_keys_pilot_v97"


def leaf_keys_nodup_theorem(chunk: Chunk) -> str:
    return f"z180_k30_projective_d4_u_leaf_{chunk.tag}_keys_nodup_pilot_v97"


def index_bucket_module(index: int) -> str:
    return f"{PREFIX}IndexB{index:02d}PilotV97"


def index_bucket_path(index: int) -> Path:
    return LEAN_DIR / f"{index_bucket_module(index)}.lean"


def index_bucket_theorem(index: int) -> str:
    return f"z180_k30_projective_d4_u_index_bucket_b{index:02d}_pilot_v97"


def index_aggregate_module() -> str:
    return f"{PREFIX}IndexAggregatePilotV97"


def index_aggregate_path() -> Path:
    return LEAN_DIR / f"{index_aggregate_module()}.lean"


def disjoint_row_module(index: int) -> str:
    return f"{PREFIX}KeyDisjointRow{index:02d}PilotV97"


def disjoint_row_path(index: int) -> Path:
    return LEAN_DIR / f"{disjoint_row_module(index)}.lean"


def disjoint_row_theorem(index: int) -> str:
    return f"z180_k30_projective_d4_u_key_disjoint_row_{index:02d}_pilot_v97"


def selection_module(row: str) -> str:
    return f"{PREFIX}Selection{row}PilotV97"


def selection_path(row: str) -> Path:
    return LEAN_DIR / f"{selection_module(row)}.lean"


def selection_theorem(selection: tuple[int, ...]) -> str:
    if len(selection) == 1:
        return f"z180_k30_projective_d4_u_selection_s{selection[0]}_pilot_v97"
    return (
        "z180_k30_projective_d4_u_selection_p"
        f"{selection[0]}_{selection[1]}_pilot_v97"
    )


def canonical_append() -> str:
    return " ++\n    ".join(block_name(residue) for residue in range(1, 9))


def core_source(tails, indices, selections) -> str:
    tail_defs = "\n".join(
        f"def {tail_name(residue)} : RawSet := {lean_list(tails[residue])}\n"
        f"def {block_name(residue)} : List RawSet :=\n"
        f"  z180K30ProjectiveD4UCombPilotV97 [0] {tail_name(residue)} 5"
        for residue in range(1, 9)
    )
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D4UBase
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sublists

/-! Generic core for the bounded structural D4-U completeness bridge. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d4_u_filter_without_zero_pilot_v97
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

theorem z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    {{alpha : Type}} [DecidableEq alpha]
    (point : alpha) (values : List (List alpha)) :
    (values.map (List.cons point)).filter
      (fun set => decide (point ∈ set)) = values.map (List.cons point) := by
  apply List.filter_eq_self.mpr
  intro set hset
  obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hset
  exact decide_eq_true List.mem_cons_self

def z180K30ProjectiveD4UCombPilotV97
    (frame domain : RawSet) (length : Nat) : List RawSet :=
  (List.sublistsLen length domain).map fun suffix => frame ++ suffix

theorem z180_k30_projective_d4_u_comb_succ_cons_pilot_v97
    (frame : RawSet) (head : RawPoint) (tail : RawSet) (length : Nat) :
    z180K30ProjectiveD4UCombPilotV97 frame (head :: tail) (length + 1) =
      z180K30ProjectiveD4UCombPilotV97 frame tail (length + 1) ++
        z180K30ProjectiveD4UCombPilotV97 (frame ++ [head]) tail length := by
  simp only [z180K30ProjectiveD4UCombPilotV97,
    List.sublistsLen_succ_cons, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro suffix _
  change frame ++ head :: suffix = frame ++ [head] ++ suffix
  rw [List.append_assoc, List.singleton_append]

def z180K30ProjectiveD4UCombChunksPilotV97 :
    Nat → RawSet → RawSet → Nat → List (List RawSet)
  | 0, frame, domain, length =>
      [z180K30ProjectiveD4UCombPilotV97 frame domain length]
  | _ + 1, frame, domain, 0 =>
      [z180K30ProjectiveD4UCombPilotV97 frame domain 0]
  | _ + 1, frame, [], length + 1 =>
      [z180K30ProjectiveD4UCombPilotV97 frame [] (length + 1)]
  | fuel + 1, frame, head :: tail, length + 1 =>
      z180K30ProjectiveD4UCombChunksPilotV97 fuel frame tail (length + 1) ++
        z180K30ProjectiveD4UCombChunksPilotV97
          fuel (frame ++ [head]) tail length

theorem z180_k30_projective_d4_u_comb_chunks_flatten_pilot_v97 :
    ∀ fuel frame domain length,
      (z180K30ProjectiveD4UCombChunksPilotV97
        fuel frame domain length).flatten =
        z180K30ProjectiveD4UCombPilotV97 frame domain length
  | 0, frame, domain, length => by
      simp [z180K30ProjectiveD4UCombChunksPilotV97]
  | _ + 1, frame, domain, 0 => by
      simp [z180K30ProjectiveD4UCombChunksPilotV97]
  | fuel + 1, frame, [], length + 1 => by
      simp [z180K30ProjectiveD4UCombChunksPilotV97]
  | fuel + 1, frame, head :: tail, length + 1 => by
      rw [z180K30ProjectiveD4UCombChunksPilotV97, List.flatten_append,
        z180_k30_projective_d4_u_comb_chunks_flatten_pilot_v97,
        z180_k30_projective_d4_u_comb_chunks_flatten_pilot_v97,
        z180_k30_projective_d4_u_comb_succ_cons_pilot_v97]

{tail_defs}

def z180K30ProjectiveD4UCanonicalPilotV97 : List RawSet :=
  {canonical_append()}

def z180K30ProjectiveD4UCanonicalIndicesPilotV97 : List Nat :=
  {lean_list(indices)}

def z180K30ProjectiveD4UIndexPredicatePilotV97
    (bucket value : Nat) : Bool := value % {INDEX_BUCKET_COUNT} == bucket

def z180K30ProjectiveD4USourceAtPilotV97 (index : Nat) : RawSet :=
  z180K30ProjectiveCompletenessV97D4USourceGrouped.getD index []

def z180K30ProjectiveD4UCanonicalIndexedPilotV97 : List RawSet :=
  z180K30ProjectiveD4UCanonicalIndicesPilotV97.map
    z180K30ProjectiveD4USourceAtPilotV97

def z180K30ProjectiveD4USelectionsLiteralPilotV97 : List (List Nat) :=
  [{", ".join(lean_list(selection) for selection in selections)}]

theorem z180_k30_projective_d4_u_selections_literal_pilot_v97 :
    normalizedProjectiveClassSelectionsV88 4 =
      z180K30ProjectiveD4USelectionsLiteralPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def index_bucket_source(index: int, indices: tuple[int, ...]) -> str:
    source_size = sum(value % INDEX_BUCKET_COUNT == index for value in range(168))
    target_size = sum(value % INDEX_BUCKET_COUNT == index for value in indices)
    if max(source_size, target_size) > 10:
        raise RuntimeError(f"D4-U index bucket {index} exceeds ten entries")
    return f"""import Fuglede.{PREFIX}CorePilotV97

/-! D4-U Nat-only index bucket {index}; source={source_size}, target={target_size}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem {index_bucket_theorem(index)} :
    ((List.range 168).filter
      (z180K30ProjectiveD4UIndexPredicatePilotV97 {index})).Perm
      (z180K30ProjectiveD4UCanonicalIndicesPilotV97.filter
        (z180K30ProjectiveD4UIndexPredicatePilotV97 {index})) := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def index_aggregate_source() -> str:
    imports = "\n".join(
        f"import Fuglede.{index_bucket_module(index)}"
        for index in range(INDEX_BUCKET_COUNT)
    )
    cases = "\n".join(
        f"      | exact {index_bucket_theorem(index)}"
        for index in range(INDEX_BUCKET_COUNT)
    )
    return f"""{imports}

/-! Structural aggregate of the seventeen bounded D4-U Nat-index buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d4_u_index_perm_pilot_v97 :
    (List.range 168).Perm z180K30ProjectiveD4UCanonicalIndicesPilotV97 := by
  have hBuckets :
      ((List.range {INDEX_BUCKET_COUNT}).flatMap fun bucket =>
        (List.range 168).filter
          (z180K30ProjectiveD4UIndexPredicatePilotV97 bucket)).Perm
      ((List.range {INDEX_BUCKET_COUNT}).flatMap fun bucket =>
        z180K30ProjectiveD4UCanonicalIndicesPilotV97.filter
          (z180K30ProjectiveD4UIndexPredicatePilotV97 bucket)) := by
    apply List.Perm.flatMap_left
    intro bucket hbucket
    simp only [List.mem_range] at hbucket
    interval_cases bucket <;> first
{cases}
  have hSource := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) {INDEX_BUCKET_COUNT} (by decide) (List.range 168)
  have hTarget := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) {INDEX_BUCKET_COUNT} (by decide)
    z180K30ProjectiveD4UCanonicalIndicesPilotV97
  exact hSource.symm.trans (hBuckets.trans hTarget)

theorem z180_k30_projective_d4_u_source_length_pilot_v97 :
    z180K30ProjectiveCompletenessV97D4USourceGrouped.length = 168 := by
  rfl

private theorem map_range_getD_eq_self_d4u_pilot
    {{alpha : Type}} (values : List alpha) (fallback : alpha) :
    (List.range values.length).map (fun index => values.getD index fallback) =
      values := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem values fallback hright

theorem z180_k30_projective_d4_u_source_range_pilot_v97 :
    (List.range 168).map z180K30ProjectiveD4USourceAtPilotV97 =
      z180K30ProjectiveCompletenessV97D4USourceGrouped := by
  rw [← z180_k30_projective_d4_u_source_length_pilot_v97]
  exact map_range_getD_eq_self_d4u_pilot
    z180K30ProjectiveCompletenessV97D4USourceGrouped []

theorem z180_k30_projective_d4_u_source_perm_indexed_pilot_v97 :
    z180K30ProjectiveCompletenessV97D4USourceGrouped.Perm
      z180K30ProjectiveD4UCanonicalIndexedPilotV97 := by
  have h := z180_k30_projective_d4_u_index_perm_pilot_v97.map
    z180K30ProjectiveD4USourceAtPilotV97
  rw [z180_k30_projective_d4_u_source_range_pilot_v97] at h
  exact h

end Fuglede.Z180K30ExceptionalRawV2
"""


def selection_source(row: str, selections: list[tuple[int, ...]], tails) -> str:
    theorems: list[str] = []
    for selection in selections:
        theorem = selection_theorem(selection)
        literal = lean_list(selection)
        productive = len(selection) == 2 and ((selection[0] == 0) ^ (selection[1] == 0))
        if productive:
            residue = max(selection)
            body = f"""theorem {theorem} :
    normalizedProjectiveUChoicesForSelectionV88 4 {literal} =
      {block_name(residue)} := by
  unfold {block_name(residue)}
  unfold normalizedProjectiveUChoicesForSelectionV88
  have hdomain : normalizedProjectiveClassDomainV88 4 {literal} =
      (0 : RawPoint) :: {tail_name(residue)} := by decide
  rw [hdomain, List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) {tail_name(residue)} 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d4_u_filter_cons_zero_pilot_v97
    (0 : RawPoint) (List.sublistsLen 5 {tail_name(residue)})"""
        elif len(selection) == 1 or selection[0] == selection[1]:
            body = f"""theorem {theorem} :
    normalizedProjectiveUChoicesForSelectionV88 4 {literal} = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  rw [List.sublistsLen_of_length_lt (by decide)]
  rfl"""
        else:
            body = f"""theorem {theorem} :
    normalizedProjectiveUChoicesForSelectionV88 4 {literal} = [] := by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d4_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 4 {literal}) 6
      (by decide)"""
        theorems.append(body)
    joined_theorems = "\n\n".join(theorems)
    return f"""import Fuglede.{PREFIX}CorePilotV97

/-! Algebraic D4-U selection row {row}; no full candidate list is reduced. -/

namespace Fuglede.Z180K30ExceptionalRawV2

{joined_theorems}

end Fuglede.Z180K30ExceptionalRawV2
"""


def leaf_source(chunk: Chunk) -> str:
    return f"""import Fuglede.{PREFIX}CorePilotV97

/-! D4-U bounded literal bridge leaf {chunk.tag}, size {len(chunk.values)}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def {leaf_indices_name(chunk)} : List Nat := {lean_list(chunk.indices)}

def {leaf_target_name(chunk)} : List RawSet :=
  z180K30ProjectiveD4UCombPilotV97
    {lean_list(chunk.frame)} {lean_list(chunk.domain)} {chunk.length}

def {leaf_keys_name(chunk)} : List Nat := {lean_list(chunk.keys)}

theorem {leaf_bridge_theorem(chunk)} :
    {leaf_indices_name(chunk)}.map z180K30ProjectiveD4USourceAtPilotV97 =
      {leaf_target_name(chunk)} := by
  decide

theorem {leaf_keys_theorem(chunk)} :
    {leaf_target_name(chunk)}.map normalizedProjectiveRawSetKeyV89 =
      {leaf_keys_name(chunk)} := by
  decide

theorem {leaf_keys_nodup_theorem(chunk)} :
    {leaf_keys_name(chunk)}.Nodup := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def disjoint_row_source(index: int, chunks: list[Chunk]) -> str:
    current = chunks[index]
    tail = chunks[index + 1 :]
    if not tail:
        imports = f"import Fuglede.{current.module}"
        proof = "  simp"
    else:
        imports = (
            f"import Fuglede.{current.module}\n"
            f"import Fuglede.{disjoint_row_module(index + 1)}"
        )
        tail_list = ",\n      ".join(leaf_keys_name(chunk) for chunk in tail)
        alternatives = " | ".join("rfl" for _ in tail)
        proof = f"""  rw [List.pairwise_cons]
  constructor
  · intro values hvalues
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvalues
    rcases hvalues with ({alternatives}) <;>
      (rw [List.disjoint_left]; decide)
  · exact {disjoint_row_theorem(index + 1)}"""
    full_list = ",\n    ".join(leaf_keys_name(chunk) for chunk in chunks[index:])
    return f"""{imports}

/-! Pairwise key-disjointness row {index}; every decision compares two chunks of at most ten keys. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem {disjoint_row_theorem(index)} :
    List.Pairwise List.Disjoint [{full_list}] := by
{proof}

end Fuglede.Z180K30ExceptionalRawV2
"""


def aggregate_source(chunks: list[Chunk], selection_rows: dict[str, list[tuple[int, ...]]]) -> str:
    imports = ["import Mathlib.Data.List.Basic"]
    imports += [f"import Fuglede.{chunk.module}" for chunk in chunks]
    imports += [f"import Fuglede.{selection_module(row)}" for row in selection_rows]
    imports.append(f"import Fuglede.{disjoint_row_module(0)}")
    imports.append(f"import Fuglede.{index_aggregate_module()}")
    index_defs = ",\n    ".join(leaf_indices_name(chunk) for chunk in chunks)
    source_chunk_defs = ",\n    ".join(
        f"{leaf_indices_name(chunk)}.map z180K30ProjectiveD4USourceAtPilotV97"
        for chunk in chunks
    )
    target_defs = ",\n    ".join(leaf_target_name(chunk) for chunk in chunks)
    target_key_chunk_defs = ",\n    ".join(
        f"{leaf_target_name(chunk)}.map normalizedProjectiveRawSetKeyV89"
        for chunk in chunks
    )
    key_defs = ",\n    ".join(leaf_keys_name(chunk) for chunk in chunks)
    def explicit_cons_proof(theorems: list[str]) -> str:
        lines: list[str] = []
        for theorem in theorems:
            lines.extend([
                "  apply congrArg₂ List.cons",
                f"  · exact {theorem}",
            ])
        lines.append("  · rfl")
        return "\n".join(lines)

    leaf_bridge_proof = explicit_cons_proof(
        [leaf_bridge_theorem(chunk) for chunk in chunks]
    )
    leaf_key_proof = explicit_cons_proof(
        [leaf_keys_theorem(chunk) for chunk in chunks]
    )
    leaf_key_nodup_proofs = "\n".join(
        "    · " + f"exact {leaf_keys_nodup_theorem(chunk)}"
        for index, chunk in enumerate(chunks)
    )
    nodup_alternatives = " | ".join("rfl" for _ in chunks)
    selection_theorems = ",\n    ".join(
        selection_theorem(selection)
        for selections in selection_rows.values()
        for selection in selections
    )
    chunk_trees = " ++\n      ".join(
        f"z180K30ProjectiveD4UCombChunksPilotV97 2 [0] {tail_name(residue)} 5"
        for residue in range(1, 9)
    )
    flatten_rewrites = ",\n    ".join(
        ["List.flatten_append"] * 7 +
        ["z180_k30_projective_d4_u_comb_chunks_flatten_pilot_v97"] * 8
    )
    joined_imports = "\n".join(imports)
    return f"""{joined_imports}

/-! Aggregate of the authenticated bounded D4-U algebraic DAG. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD4UIndexChunksPilotV97 : List (List Nat) :=
  [{index_defs}]

def z180K30ProjectiveD4USourceChunksPilotV97 : List (List RawSet) :=
  [{source_chunk_defs}]

def z180K30ProjectiveD4UTargetChunksPilotV97 : List (List RawSet) :=
  [{target_defs}]

def z180K30ProjectiveD4UTargetKeyChunksPilotV97 : List (List Nat) :=
  [{target_key_chunk_defs}]

def z180K30ProjectiveD4UKeyChunksPilotV97 : List (List Nat) :=
  [{key_defs}]

theorem z180_k30_projective_d4_u_index_chunks_flatten_pilot_v97 :
    z180K30ProjectiveD4UIndexChunksPilotV97.flatten =
      z180K30ProjectiveD4UCanonicalIndicesPilotV97 := by
  rfl

theorem z180_k30_projective_d4_u_index_chunks_map_pilot_v97 :
    (z180K30ProjectiveD4UIndexChunksPilotV97.map fun indices =>
      indices.map z180K30ProjectiveD4USourceAtPilotV97) =
        z180K30ProjectiveD4USourceChunksPilotV97 := by
  rfl

theorem z180_k30_projective_d4_u_source_target_chunks_pilot_v97 :
    z180K30ProjectiveD4USourceChunksPilotV97 =
      z180K30ProjectiveD4UTargetChunksPilotV97 := by
  unfold z180K30ProjectiveD4USourceChunksPilotV97
  unfold z180K30ProjectiveD4UTargetChunksPilotV97
{leaf_bridge_proof}

theorem z180_k30_projective_d4_u_mapped_chunks_pilot_v97 :
    (z180K30ProjectiveD4UIndexChunksPilotV97.map fun indices =>
      indices.map z180K30ProjectiveD4USourceAtPilotV97) =
        z180K30ProjectiveD4UTargetChunksPilotV97 := by
  exact z180_k30_projective_d4_u_index_chunks_map_pilot_v97.trans
    z180_k30_projective_d4_u_source_target_chunks_pilot_v97

theorem z180_k30_projective_d4_u_target_chunks_tree_pilot_v97 :
    z180K30ProjectiveD4UTargetChunksPilotV97 =
      {chunk_trees} := by
  rfl

theorem z180_k30_projective_d4_u_target_chunks_flatten_pilot_v97 :
    z180K30ProjectiveD4UTargetChunksPilotV97.flatten =
      z180K30ProjectiveD4UCanonicalPilotV97 := by
  rw [z180_k30_projective_d4_u_target_chunks_tree_pilot_v97,
    {flatten_rewrites}]
  rfl

theorem z180_k30_projective_d4_u_indexed_canonical_pilot_v97 :
    z180K30ProjectiveD4UCanonicalIndexedPilotV97 =
      z180K30ProjectiveD4UCanonicalPilotV97 := by
  unfold z180K30ProjectiveD4UCanonicalIndexedPilotV97
  rw [← z180_k30_projective_d4_u_index_chunks_flatten_pilot_v97,
    List.map_flatten, z180_k30_projective_d4_u_mapped_chunks_pilot_v97,
    z180_k30_projective_d4_u_target_chunks_flatten_pilot_v97]

theorem z180_k30_projective_d4_u_target_chunks_map_keys_pilot_v97 :
    (z180K30ProjectiveD4UTargetChunksPilotV97.map fun values =>
      values.map normalizedProjectiveRawSetKeyV89) =
        z180K30ProjectiveD4UTargetKeyChunksPilotV97 := by
  rfl

theorem z180_k30_projective_d4_u_target_key_chunks_values_pilot_v97 :
    z180K30ProjectiveD4UTargetKeyChunksPilotV97 =
      z180K30ProjectiveD4UKeyChunksPilotV97 := by
  unfold z180K30ProjectiveD4UTargetKeyChunksPilotV97
  unfold z180K30ProjectiveD4UKeyChunksPilotV97
{leaf_key_proof}

theorem z180_k30_projective_d4_u_target_chunk_keys_pilot_v97 :
    (z180K30ProjectiveD4UTargetChunksPilotV97.map fun values =>
      values.map normalizedProjectiveRawSetKeyV89) =
        z180K30ProjectiveD4UKeyChunksPilotV97 := by
  exact z180_k30_projective_d4_u_target_chunks_map_keys_pilot_v97.trans
    z180_k30_projective_d4_u_target_key_chunks_values_pilot_v97

theorem z180_k30_projective_d4_u_canonical_keys_pilot_v97 :
    z180K30ProjectiveD4UCanonicalPilotV97.map
      normalizedProjectiveRawSetKeyV89 =
        z180K30ProjectiveD4UKeyChunksPilotV97.flatten := by
  rw [← z180_k30_projective_d4_u_target_chunks_flatten_pilot_v97,
    List.map_flatten, z180_k30_projective_d4_u_target_chunk_keys_pilot_v97]

theorem z180_k30_projective_d4_u_key_chunks_nodup_pilot_v97 :
    z180K30ProjectiveD4UKeyChunksPilotV97.flatten.Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro values hvalues
    unfold z180K30ProjectiveD4UKeyChunksPilotV97 at hvalues
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvalues
    rcases hvalues with ({nodup_alternatives})
{leaf_key_nodup_proofs}
  · unfold z180K30ProjectiveD4UKeyChunksPilotV97
    exact {disjoint_row_theorem(0)}

theorem z180_k30_projective_d4_u_canonical_nodup_pilot_v97 :
    z180K30ProjectiveD4UCanonicalPilotV97.Nodup := by
  apply List.Nodup.of_map normalizedProjectiveRawSetKeyV89
  rw [z180_k30_projective_d4_u_canonical_keys_pilot_v97]
  exact z180_k30_projective_d4_u_key_chunks_nodup_pilot_v97

theorem z180_k30_projective_d4_u_choices_double_pilot_v97 :
    normalizedProjectiveUChoicesV88 4 =
      z180K30ProjectiveD4UCanonicalPilotV97 ++
        z180K30ProjectiveD4UCanonicalPilotV97 := by
  unfold normalizedProjectiveUChoicesV88
  rw [z180_k30_projective_d4_u_selections_literal_pilot_v97]
  simp only [z180K30ProjectiveD4USelectionsLiteralPilotV97,
    List.flatMap_cons, List.flatMap_nil, {selection_theorems},
    List.nil_append, List.append_nil, z180K30ProjectiveD4UCanonicalPilotV97,
    List.append_assoc]

private theorem z180_k30_projective_d4_u_erase_nodup_pilot_v97
    {{alpha : Type}} [BEq alpha] [LawfulBEq alpha] :
    ∀ {{values : List alpha}}, values.Nodup → values.eraseDups = values
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
        z180_k30_projective_d4_u_erase_nodup_pilot_v97 htail]

private theorem z180_k30_projective_d4_u_removeAll_self_pilot_v97
    {{alpha : Type}} [BEq alpha] [LawfulBEq alpha] (values : List alpha) :
    values.removeAll values = [] := by
  unfold List.removeAll
  apply List.filter_eq_nil_iff.mpr
  intro item hitem hkeep
  have helem : values.elem item = true := List.elem_eq_true_of_mem hitem
  have hfalse : values.elem item = false :=
    Bool.eq_false_of_not_eq_true' hkeep
  rw [helem] at hfalse
  cases hfalse

private theorem z180_k30_projective_d4_u_erase_double_pilot_v97
    {{alpha : Type}} [BEq alpha] [LawfulBEq alpha]
    (values : List alpha) (hnodup : values.Nodup) :
    (values ++ values).eraseDups = values := by
  rw [List.eraseDups_append,
    z180_k30_projective_d4_u_erase_nodup_pilot_v97 hnodup,
    z180_k30_projective_d4_u_removeAll_self_pilot_v97,
    List.eraseDups_nil, List.append_nil]

theorem z180_k30_projective_d4_u_unique_canonical_pilot_v97 :
    normalizedProjectiveUniqueUChoicesV89 4 =
      z180K30ProjectiveD4UCanonicalPilotV97 := by
  unfold normalizedProjectiveUniqueUChoicesV89
  rw [z180_k30_projective_d4_u_choices_double_pilot_v97]
  exact z180_k30_projective_d4_u_erase_double_pilot_v97
    z180K30ProjectiveD4UCanonicalPilotV97
    z180_k30_projective_d4_u_canonical_nodup_pilot_v97

theorem z180_k30_projective_d4_u_complete_algebraic_pilot_v97 :
    z180K30ProjectiveCompletenessV97D4USourceGrouped.Perm
      (normalizedProjectiveUniqueUChoicesV89 4) := by
  exact z180_k30_projective_d4_u_source_perm_indexed_pilot_v97.trans
    (List.Perm.of_eq
      (z180_k30_projective_d4_u_indexed_canonical_pilot_v97.trans
        z180_k30_projective_d4_u_unique_canonical_pilot_v97.symm))

#print axioms z180_k30_projective_d4_u_complete_algebraic_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
"""


def build():
    member_paths, source_names, source_values, tails, blocks, chunks, indices, selections = build_model()
    singleton_selections = [selection for selection in selections if len(selection) == 1]
    selection_rows: dict[str, list[tuple[int, ...]]] = {"Singleton": singleton_selections}
    for first in range(9):
        selection_rows[f"PairR{first}"] = [
            selection for selection in selections
            if len(selection) == 2 and selection[0] == first
        ]

    outputs: dict[Path, str] = {
        CORE: core_source(tails, indices, selections),
        AGGREGATE: aggregate_source(chunks, selection_rows),
        index_aggregate_path(): index_aggregate_source(),
    }
    for index in range(INDEX_BUCKET_COUNT):
        outputs[index_bucket_path(index)] = index_bucket_source(index, indices)
    for row, row_selections in selection_rows.items():
        outputs[selection_path(row)] = selection_source(row, row_selections, tails)
    for chunk in chunks:
        outputs[chunk.path] = leaf_source(chunk)
    for index in reversed(range(len(chunks))):
        outputs[disjoint_row_path(index)] = disjoint_row_source(index, chunks)

    for path, source in outputs.items():
        match = FORBIDDEN.search(source)
        if match:
            raise RuntimeError(f"forbidden Lean token {match.group(0)} in {relative(path)}")
    aggregate_imports = re.findall(r"^import Fuglede\.(\S+)$", outputs[AGGREGATE], re.M)
    expected_imports = [chunk.module for chunk in chunks] + [
        selection_module(row) for row in selection_rows
    ] + [disjoint_row_module(0), index_aggregate_module()]
    if aggregate_imports != expected_imports:
        raise RuntimeError("D4-U generated import topology drift")

    data_path = LEAN_DIR / "Z180K30ExceptionalProjectiveProfileDataV97D4.lean"
    isolation_paths = [
        REPO_DIR / "fuglede_lean" / "Fuglede.lean",
        SCRIPT_DIR / "z180_k30_projective_profile_audit_v97.manifest.json",
    ]
    for path in isolation_paths:
        if AGGREGATE.stem in path.read_text(encoding="utf-8"):
            raise RuntimeError(f"isolated D4-U aggregate leaked into {relative(path)}")

    inputs = [ACTIVE_GENERATOR, BASE, *member_paths, data_path, *isolation_paths]
    manifest = {
        "schema": "z180-k30-projective-profile-d4u-algebraic-v97/1",
        "generator": relative(Path(__file__).resolve()),
        "generator_sha256": file_sha256(Path(__file__).resolve()),
        "inputs": {relative(path): file_sha256(path) for path in inputs},
        "invariants": {
            "source_count": len(source_values),
            "canonical_count": sum(len(blocks[residue]) for residue in blocks),
            "selection_count": len(selections),
            "selection_module_count": len(selection_rows),
            "leaf_count": len(chunks),
            "key_disjoint_row_count": len(chunks),
            "index_bucket_count": INDEX_BUCKET_COUNT,
            "maximum_nat_indices_per_bucket": 10,
            "maximum_rawsets_per_decision": max(len(chunk.values) for chunk in chunks),
            "key_injective": True,
            "canonical_indices_sha256": sha256_text(json.dumps(indices)),
            "source_names_sha256": sha256_text(json.dumps(source_names)),
            "source_values_sha256": sha256_text(json.dumps(source_values)),
            "generated_import_graph_acyclic": True,
            "active_manifest_isolated": True,
            "forbidden_lean_tokens_absent": True,
        },
        "outputs": {
            relative(path): sha256_text(source) for path, source in sorted(
                outputs.items(), key=lambda item: relative(item[0])
            )
        },
    }
    return chunks, outputs, manifest


def manifest_text(manifest) -> str:
    return json.dumps(manifest, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    chunks, outputs, manifest = build()
    if args.write:
        for path, source in outputs.items():
            path.write_text(source, encoding="utf-8", newline="\n")
        MANIFEST.write_text(manifest_text(manifest), encoding="utf-8", newline="\n")
        action = "wrote"
    else:
        failures = []
        for path, source in outputs.items():
            if not path.exists() or path.read_text(encoding="utf-8") != source:
                failures.append(relative(path))
        if not MANIFEST.exists() or MANIFEST.read_text(encoding="utf-8") != manifest_text(manifest):
            failures.append(relative(MANIFEST))
        if failures:
            raise RuntimeError("D4-U generated check failed: " + ", ".join(failures))
        action = "checked"
    print(
        f"{action} D4-U algebraic DAG: leaves={len(chunks)}; "
        f"total={sum(len(chunk.values) for chunk in chunks)}; "
        f"max={max(len(chunk.values) for chunk in chunks)}; outputs={len(outputs)}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError) as error:
        print(f"FAIL CLOSED: {error}", file=sys.stderr)
        raise SystemExit(1)
