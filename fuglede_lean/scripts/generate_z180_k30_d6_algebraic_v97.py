#!/usr/bin/env python3
"""Generate authenticated bounded algebraic D6U/D6V completeness pilots."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FUGLEDE = ROOT / "Fuglede"
U_BASE = FUGLEDE / "Z180K30ExceptionalProjectiveProfileCompletenessV97D6UBase.lean"
V_BASE = FUGLEDE / "Z180K30ExceptionalProjectiveProfileCompletenessV97D6VBase.lean"
CORE = FUGLEDE / "Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97.lean"
INDEX_AGG = FUGLEDE / "Z180K30ExceptionalProjectiveProfileD6UAlgebraicIndexPermPilotV97.lean"
BRIDGE_AGG = FUGLEDE / "Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgePilotV97.lean"
V_OUT = FUGLEDE / "Z180K30ExceptionalProjectiveProfileD6VAlgebraicPilotV97.lean"
MANIFEST = ROOT / "generated/z180_k30_d6_algebraic_v97.manifest.json"
ACTIVE_FILES = [
    ROOT / "Fuglede.lean",
]
INTEGRATION_FILES = [
    FUGLEDE / "Z180K30ExceptionalProjectiveProfileDataV97D6.lean",
]

PROFILE_DEF = re.compile(
    r"def\s+(z180K30ProfileV97D6[UV]\d+M\d+)\s*:\s*RawSet\s*:=\s*"
    r"\[([^\]]*)\]"
)
FORBIDDEN = re.compile(r"\b(?:native_decide|unsafe|sorry|axiom|choose|drop|take)\b")
INDEX_BUCKET_COUNT = 256
CHUNK_FUEL = 6
BRIDGE_ROW_SIZE = 32
A = (0, 6, 12, 18, 24, 30)
TAILS = {
    residue: tuple(point for point in range(1, 36) if point % 6 in (0, residue))
    for residue in range(1, 6)
}


@dataclass(frozen=True)
class CombLeaf:
    number: int
    residue: int
    local_number: int
    offset: int
    indices: tuple[int, ...]
    frame: tuple[int, ...]
    domain: tuple[int, ...]
    length: int
    raw_targets: tuple[tuple[int, ...], ...]
    targets: tuple[tuple[int, ...], ...]

    @property
    def tag(self) -> str:
        return f"{self.number:03d}"

    @property
    def module(self) -> str:
        return f"Z180K30ExceptionalProjectiveProfileD6UAlgebraicLeaf{self.tag}PilotV97"

    @property
    def path(self) -> Path:
        return FUGLEDE / f"{self.module}.lean"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def lean_list(values: tuple[int, ...] | list[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def bracket_body_after(text: str, marker: str) -> str:
    start = text.index(marker)
    assign = text.index(":=", start)
    left = text.index("[", assign)
    depth = 0
    for index in range(left, len(text)):
        if text[index] == "[":
            depth += 1
        elif text[index] == "]":
            depth -= 1
            if depth == 0:
                return text[left + 1 : index]
    raise RuntimeError(f"unterminated bracketed body after {marker}")


def parse_source_names(path: Path, side: str) -> tuple[str, ...]:
    text = path.read_text(encoding="utf-8")
    body = bracket_body_after(
        text, f"def z180K30ProjectiveCompletenessV97D6{side}SourceGrouped"
    )
    return tuple(re.findall(rf"z180K30ProfileV97D6{side}\d+M\d+", body))


def parse_profiles(paths: list[Path]) -> dict[str, tuple[int, ...]]:
    profiles: dict[str, tuple[int, ...]] = {}
    for path in paths:
        for match in PROFILE_DEF.finditer(path.read_text(encoding="utf-8")):
            value = tuple(int(piece) for piece in re.findall(r"\d+", match.group(2)))
            previous = profiles.setdefault(match.group(1), value)
            if previous != value:
                raise RuntimeError(f"conflicting definition for {match.group(1)}")
    return profiles


def sublists_tail_first(length: int, domain: tuple[int, ...]) -> list[tuple[int, ...]]:
    if length == 0:
        return [()]
    if not domain:
        return []
    head, tail = domain[0], domain[1:]
    return sublists_tail_first(length, tail) + [
        (head,) + suffix for suffix in sublists_tail_first(length - 1, tail)
    ]


def leaf_specs(
    fuel: int, frame: tuple[int, ...], domain: tuple[int, ...], length: int
) -> list[tuple[tuple[int, ...], tuple[int, ...], int]]:
    if fuel == 0 or length == 0 or not domain:
        return [(frame, domain, length)]
    head, tail = domain[0], domain[1:]
    return leaf_specs(fuel - 1, frame, tail, length) + leaf_specs(
        fuel - 1, frame + (head,), tail, length - 1
    )


def comb(frame: tuple[int, ...], domain: tuple[int, ...], length: int) -> list[tuple[int, ...]]:
    return [frame + suffix for suffix in sublists_tail_first(length, domain)]


def block(residue: int) -> list[tuple[int, ...]]:
    return comb((0,), TAILS[residue], 5)


def canonical_u() -> list[tuple[int, ...]]:
    return [A] + [value for residue in range(1, 6) for value in block(residue) if value != A]


def normalized_u_choices() -> list[tuple[int, ...]]:
    # The six singleton selections are first, then the 36 ordered pairs.
    def selection(selection: tuple[int, ...]) -> list[tuple[int, ...]]:
        domain = tuple(
            point for point in range(36) if any(point % 6 == residue for residue in selection)
        )
        return [value for value in sublists_tail_first(6, domain) if 0 in value]

    result: list[tuple[int, ...]] = []
    for residue in range(6):
        result.extend(selection((residue,)))
    for first in range(6):
        for second in range(6):
            result.extend(selection((first, second)))
    return result


def stable_dedup(values: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    result: list[tuple[int, ...]] = []
    for value in values:
        if value not in result:
            result.append(value)
    return result


def split_lines(values: list[int] | tuple[int, ...], indent: str = "  ", width: int = 100) -> str:
    pieces = [str(value) for value in values]
    lines: list[str] = []
    current = indent + "["
    for index, piece in enumerate(pieces):
        token = piece + (", " if index + 1 < len(pieces) else "]")
        if len(current) + len(token) > width and current != indent + "[":
            lines.append(current.rstrip())
            current = indent + " " + token
        else:
            current += token
    lines.append(current.rstrip())
    return "\n".join(lines)


def core_content(indices: tuple[int, ...]) -> str:
    tails = "\n".join(
        f"def z180K30ProjectiveD6UTailR{residue}PilotV97 : RawSet :=\n"
        f"  {lean_list(TAILS[residue])}"
        for residue in range(1, 6)
    )
    raw_blocks = "\n".join(
        f"def z180K30ProjectiveD6URawBlockR{residue}PilotV97 : List RawSet :=\n"
        f"  z180K30ProjectiveD6UCombPilotV97 [0]\n"
        f"    z180K30ProjectiveD6UTailR{residue}PilotV97 5"
        for residue in range(1, 6)
    )
    blocks = "\n".join(
        f"def z180K30ProjectiveD6UBlockR{residue}PilotV97 : List RawSet :=\n"
        f"  z180K30ProjectiveD6URawBlockR{residue}PilotV97.filter\n"
        f"      (fun value => value != z180K30ProjectiveD6UAPilotV97)"
        for residue in range(1, 6)
    )
    raw_blocks_twice = ",\n    ".join(
        ["[z180K30ProjectiveD6UAPilotV97]"]
        + [
            f"z180K30ProjectiveD6URawBlockR{residue}PilotV97"
            for residue in range(1, 6)
        ]
        + [
            f"z180K30ProjectiveD6URawBlockR{residue}PilotV97"
            for residue in range(1, 6)
        ]
    )
    canonical_append = " ++\n    ".join(
        f"z180K30ProjectiveD6UBlockR{residue}PilotV97" for residue in range(1, 6)
    )
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6UBase
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sublists

/-! Structural core for the bounded source-only D6-U algebraic bridge. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UAPilotV97 : RawSet :=
  {lean_list(A)}

def z180K30ProjectiveD6UCombPilotV97
    (frame domain : RawSet) (length : Nat) : List RawSet :=
  (List.sublistsLen length domain).map fun suffix => frame ++ suffix

theorem z180_k30_projective_d6_u_comb_succ_cons_pilot_v97
    (frame : RawSet) (head : RawPoint) (tail : RawSet) (length : Nat) :
    z180K30ProjectiveD6UCombPilotV97 frame (head :: tail) (length + 1) =
      z180K30ProjectiveD6UCombPilotV97 frame tail (length + 1) ++
        z180K30ProjectiveD6UCombPilotV97
          (frame ++ [head]) tail length := by
  simp only [z180K30ProjectiveD6UCombPilotV97,
    List.sublistsLen_succ_cons, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro suffix _
  change frame ++ head :: suffix = frame ++ [head] ++ suffix
  rw [List.append_assoc, List.singleton_append]

def z180K30ProjectiveD6UCombChunksPilotV97 :
    Nat → RawSet → RawSet → Nat → List (List RawSet)
  | 0, frame, domain, length =>
      [(z180K30ProjectiveD6UCombPilotV97 frame domain length).filter
        (fun value => value != z180K30ProjectiveD6UAPilotV97)]
  | _ + 1, frame, domain, 0 =>
      [(z180K30ProjectiveD6UCombPilotV97 frame domain 0).filter
        (fun value => value != z180K30ProjectiveD6UAPilotV97)]
  | _ + 1, frame, [], length + 1 =>
      [(z180K30ProjectiveD6UCombPilotV97 frame [] (length + 1)).filter
        (fun value => value != z180K30ProjectiveD6UAPilotV97)]
  | fuel + 1, frame, head :: tail, length + 1 =>
      z180K30ProjectiveD6UCombChunksPilotV97 fuel frame tail (length + 1) ++
        z180K30ProjectiveD6UCombChunksPilotV97
          fuel (frame ++ [head]) tail length

theorem z180_k30_projective_d6_u_comb_chunks_flatten_pilot_v97 :
    ∀ fuel frame domain length,
      (z180K30ProjectiveD6UCombChunksPilotV97
        fuel frame domain length).flatten =
        (z180K30ProjectiveD6UCombPilotV97 frame domain length).filter
          (fun value => value != z180K30ProjectiveD6UAPilotV97)
  | 0, frame, domain, length => by
      simp [z180K30ProjectiveD6UCombChunksPilotV97]
  | _ + 1, frame, domain, 0 => by
      simp [z180K30ProjectiveD6UCombChunksPilotV97]
  | fuel + 1, frame, [], length + 1 => by
      simp [z180K30ProjectiveD6UCombChunksPilotV97]
  | fuel + 1, frame, head :: tail, length + 1 => by
      rw [z180K30ProjectiveD6UCombChunksPilotV97, List.flatten_append,
        z180_k30_projective_d6_u_comb_chunks_flatten_pilot_v97,
        z180_k30_projective_d6_u_comb_chunks_flatten_pilot_v97,
        z180_k30_projective_d6_u_comb_succ_cons_pilot_v97,
        List.filter_append]

{tails}

{raw_blocks}

def z180K30ProjectiveD6URawBlocksTwicePilotV97 : List (List RawSet) :=
  [{raw_blocks_twice}]

{blocks}

def z180K30ProjectiveD6UCanonicalTailPilotV97 : List RawSet :=
  {canonical_append}

def z180K30ProjectiveD6UCanonicalPilotV97 : List RawSet :=
  z180K30ProjectiveD6UAPilotV97 :: z180K30ProjectiveD6UCanonicalTailPilotV97

set_option maxRecDepth 100000 in
def z180K30ProjectiveD6UCanonicalIndicesPilotV97 : List Nat :=
{split_lines(indices, "  ", 100)}

def z180K30ProjectiveD6USourceAtPilotV97 (index : Nat) : RawSet :=
  z180K30ProjectiveCompletenessV97D6USourceGrouped.getD index []

def z180K30ProjectiveD6UCanonicalIndexedPilotV97 : List RawSet :=
  z180K30ProjectiveD6UCanonicalIndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6UIndexPredicatePilotV97
    (bucket index : Nat) : Bool :=
  index % {INDEX_BUCKET_COUNT} == bucket

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_source_length_pilot_v97 :
    z180K30ProjectiveCompletenessV97D6USourceGrouped.length = 2306 := by
  rfl

private theorem z180_k30_projective_d6_u_map_range_getD_eq_self_pilot_v97
    {{alpha : Type}} (values : List alpha) (fallback : alpha) :
    (List.range values.length).map (fun index =>
      values.getD index fallback) = values := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem values fallback hright

theorem z180_k30_projective_d6_u_source_range_pilot_v97 :
    (List.range 2306).map z180K30ProjectiveD6USourceAtPilotV97 =
      z180K30ProjectiveCompletenessV97D6USourceGrouped := by
  rw [← z180_k30_projective_d6_u_source_length_pilot_v97]
  exact z180_k30_projective_d6_u_map_range_getD_eq_self_pilot_v97
    z180K30ProjectiveCompletenessV97D6USourceGrouped []

end Fuglede.Z180K30ExceptionalRawV2
"""


def index_leaf_path(bucket: int) -> Path:
    return FUGLEDE / (
        f"Z180K30ExceptionalProjectiveProfileD6UAlgebraicIndexPermB{bucket:03d}PilotV97.lean"
    )


def index_leaf_content(bucket: int, source_size: int, target_size: int) -> str:
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Nat-only D6-U index bucket {bucket}; sizes {source_size}/{target_size}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_index_bucket_b{bucket:03d}_pilot_v97 :
    ((List.range 2306).filter
      (z180K30ProjectiveD6UIndexPredicatePilotV97 {bucket})).Perm
      (z180K30ProjectiveD6UCanonicalIndicesPilotV97.filter
        (z180K30ProjectiveD6UIndexPredicatePilotV97 {bucket})) := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def index_aggregate_content() -> str:
    imports = "\n".join(
        "import Fuglede."
        f"Z180K30ExceptionalProjectiveProfileD6UAlgebraicIndexPermB{bucket:03d}PilotV97"
        for bucket in range(INDEX_BUCKET_COUNT)
    )
    cases = "\n".join(
        f"    · exact z180_k30_projective_d6_u_index_bucket_b{bucket:03d}_pilot_v97"
        for bucket in range(INDEX_BUCKET_COUNT)
    )
    return f"""{imports}

/-! Structural aggregate of {INDEX_BUCKET_COUNT} bounded Nat-only D6-U index buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_canonical_indices_perm_pilot_v97 :
    (List.range 2306).Perm
      z180K30ProjectiveD6UCanonicalIndicesPilotV97 := by
  have hBuckets :
      ((List.range {INDEX_BUCKET_COUNT}).flatMap fun bucket =>
        (List.range 2306).filter
          (z180K30ProjectiveD6UIndexPredicatePilotV97 bucket)).Perm
      ((List.range {INDEX_BUCKET_COUNT}).flatMap fun bucket =>
        z180K30ProjectiveD6UCanonicalIndicesPilotV97.filter
          (z180K30ProjectiveD6UIndexPredicatePilotV97 bucket)) := by
    apply List.Perm.flatMap_left
    intro bucket hbucket
    simp only [List.mem_range] at hbucket
    interval_cases bucket
{cases}
  have hSource := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) {INDEX_BUCKET_COUNT} (by decide)
    (List.range 2306)
  have hTarget := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) {INDEX_BUCKET_COUNT} (by decide)
    z180K30ProjectiveD6UCanonicalIndicesPilotV97
  exact hSource.symm.trans (hBuckets.trans hTarget)

theorem z180_k30_projective_d6_u_source_perm_indexed_pilot_v97 :
    z180K30ProjectiveCompletenessV97D6USourceGrouped.Perm
      z180K30ProjectiveD6UCanonicalIndexedPilotV97 := by
  have h := z180_k30_projective_d6_u_canonical_indices_perm_pilot_v97.map
    z180K30ProjectiveD6USourceAtPilotV97
  rw [z180_k30_projective_d6_u_source_range_pilot_v97] at h
  exact h

#print axioms z180_k30_projective_d6_u_canonical_indices_perm_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
"""


def comb_leaf_content(leaf: CombLeaf) -> str:
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97

/-! Bounded D6-U structural leaf {leaf.tag}: residue {leaf.residue}, size {len(leaf.targets)}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6ULeaf{leaf.tag}IndicesPilotV97 : List Nat :=
  {lean_list(leaf.indices)}

def z180K30ProjectiveD6ULeaf{leaf.tag}SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD6ULeaf{leaf.tag}IndicesPilotV97.map
    z180K30ProjectiveD6USourceAtPilotV97

def z180K30ProjectiveD6ULeaf{leaf.tag}TargetPilotV97 : List RawSet :=
  (z180K30ProjectiveD6UCombPilotV97
    {lean_list(leaf.frame)} {lean_list(leaf.domain)} {leaf.length}).filter
      (fun value => value != z180K30ProjectiveD6UAPilotV97)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d6_u_leaf_{leaf.tag}_bridge_pilot_v97 :
    z180K30ProjectiveD6ULeaf{leaf.tag}SourcePilotV97 =
      z180K30ProjectiveD6ULeaf{leaf.tag}TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def pairwise_cons_steps(names: list[str]) -> str:
    lines: list[str] = []
    for index, name in enumerate(names):
        lines.extend(
            [
                "  apply congrArg₂ List.cons",
                f"  · exact {name}",
            ]
        )
        if index + 1 == len(names):
            lines.append("  · rfl")
    return "\n".join(lines)


def bridge_row_module(row: int) -> str:
    return (
        "Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgeRow"
        f"{row:02d}PilotV97"
    )


def bridge_row_path(row: int) -> Path:
    return FUGLEDE / f"{bridge_row_module(row)}.lean"


def bridge_row_content(
    row: int,
    entries: list[CombLeaf | None],
    singleton_index: int,
) -> str:
    leaves = [entry for entry in entries if entry is not None]
    imports = [
        "import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicCorePilotV97",
        *(f"import Fuglede.{leaf.module}" for leaf in leaves),
    ]
    index_names: list[str] = []
    source_names: list[str] = []
    target_names: list[str] = []
    bridge_names: list[str] = []
    for entry in entries:
        if entry is None:
            index_names.append(f"[{singleton_index}]")
            source_names.append(
                f"[z180K30ProjectiveD6USourceAtPilotV97 {singleton_index}]"
            )
            target_names.append("[z180K30ProjectiveD6UAPilotV97]")
            bridge_names.append(
                "z180_k30_projective_d6_u_singleton_bridge_pilot_v97"
            )
        else:
            index_names.append(
                f"z180K30ProjectiveD6ULeaf{entry.tag}IndicesPilotV97"
            )
            source_names.append(
                f"z180K30ProjectiveD6ULeaf{entry.tag}SourcePilotV97"
            )
            target_names.append(
                f"z180K30ProjectiveD6ULeaf{entry.tag}TargetPilotV97"
            )
            bridge_names.append(
                f"z180_k30_projective_d6_u_leaf_{entry.tag}_bridge_pilot_v97"
            )
    singleton = ""
    if entries[0] is None:
        singleton = f"""
set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_singleton_bridge_pilot_v97 :
    [z180K30ProjectiveD6USourceAtPilotV97 {singleton_index}] =
      [z180K30ProjectiveD6UAPilotV97] := by
  decide
"""
    return f"""{chr(10).join(imports)}

/-! Bounded structural D6-U bridge row {row:02d}; {len(entries)} certificates. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UIndexRow{row:02d}PilotV97 : List (List Nat) :=
  [{", ".join(index_names)}]

def z180K30ProjectiveD6USourceRow{row:02d}PilotV97 : List (List RawSet) :=
  [{", ".join(source_names)}]

def z180K30ProjectiveD6UTargetRow{row:02d}PilotV97 : List (List RawSet) :=
  [{", ".join(target_names)}]
{singleton}
set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_index_source_row_{row:02d}_pilot_v97 :
    (z180K30ProjectiveD6UIndexRow{row:02d}PilotV97.map fun indices =>
      indices.map z180K30ProjectiveD6USourceAtPilotV97) =
        z180K30ProjectiveD6USourceRow{row:02d}PilotV97 := by
  rfl

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_source_target_row_{row:02d}_pilot_v97 :
    z180K30ProjectiveD6USourceRow{row:02d}PilotV97 =
      z180K30ProjectiveD6UTargetRow{row:02d}PilotV97 := by
  unfold z180K30ProjectiveD6USourceRow{row:02d}PilotV97
  unfold z180K30ProjectiveD6UTargetRow{row:02d}PilotV97
{pairwise_cons_steps(bridge_names)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def block_structural_theorems_text() -> str:
    pieces: list[str] = []
    for residue in range(1, 6):
        pieces.append(
            f"""theorem z180_k30_projective_d6_u_block_r{residue}_nodup_pilot_v97 :
    z180K30ProjectiveD6UBlockR{residue}PilotV97.Nodup := by
  unfold z180K30ProjectiveD6UBlockR{residue}PilotV97
  unfold z180K30ProjectiveD6URawBlockR{residue}PilotV97
  unfold z180K30ProjectiveD6UCombPilotV97
  apply List.Nodup.filter
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide

theorem z180_k30_projective_d6_u_block_r{residue}_marker_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR{residue}PilotV97) :
    ∃ point ∈ value, point.val % 6 = {residue} := by
  unfold z180K30ProjectiveD6UBlockR{residue}PilotV97 at hvalue
  rcases List.mem_filter.mp hvalue with ⟨hraw, hne⟩
  unfold z180K30ProjectiveD6URawBlockR{residue}PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  by_contra hmarker
  push_neg at hmarker
  have hsub := (List.mem_sublistsLen.mp hsuffix).1
  have hlength : suffix.length = 5 :=
    (List.mem_sublistsLen.mp hsuffix).2
  have hfilterSuffix :
      suffix.filter (fun point => point.val % 6 != {residue}) = suffix := by
    apply List.filter_eq_self.mpr
    intro point hpoint
    have hneResidue : point.val % 6 ≠ {residue} :=
      hmarker point (by simp [hpoint])
    simpa using hneResidue
  have hfilterTail :
      z180K30ProjectiveD6UTailR{residue}PilotV97.filter
          (fun point => point.val % 6 != {residue}) =
        [6, 12, 18, 24, 30] := by
    decide
  have hsubZero : List.Sublist suffix ([6, 12, 18, 24, 30] : RawSet) := by
    rw [← hfilterSuffix, ← hfilterTail]
    exact hsub.filter _
  have hsuffixZero : suffix = ([6, 12, 18, 24, 30] : RawSet) :=
    hsubZero.eq_of_length (by simpa using hlength)
  simp [hsuffixZero, z180K30ProjectiveD6UAPilotV97] at hne

theorem z180_k30_projective_d6_u_block_r{residue}_residues_pilot_v97
    (value : RawSet)
    (hvalue : value ∈ z180K30ProjectiveD6UBlockR{residue}PilotV97)
    (point : RawPoint) (hpoint : point ∈ value) :
    point.val % 6 = 0 ∨ point.val % 6 = {residue} := by
  unfold z180K30ProjectiveD6UBlockR{residue}PilotV97 at hvalue
  have hraw := (List.mem_filter.mp hvalue).1
  unfold z180K30ProjectiveD6URawBlockR{residue}PilotV97 at hraw
  unfold z180K30ProjectiveD6UCombPilotV97 at hraw
  rcases List.mem_map.mp hraw with ⟨suffix, hsuffix, hequal⟩
  subst value
  simp only [List.singleton_append, List.mem_cons] at hpoint
  rcases hpoint with hzero | hsuffixPoint
  · subst point
    simp
  · have htailPoint : point ∈ z180K30ProjectiveD6UTailR{residue}PilotV97 :=
      (List.mem_sublistsLen.mp hsuffix).1.subset hsuffixPoint
    have hclassify : ∀ candidate : RawPoint,
        candidate ∈ z180K30ProjectiveD6UTailR{residue}PilotV97 →
          candidate.val % 6 = 0 ∨ candidate.val % 6 = {residue} := by
      decide
    exact hclassify point htailPoint
"""
        )
    for left in range(1, 6):
        for right in range(left + 1, 6):
            pieces.append(
                f"""theorem z180_k30_projective_d6_u_blocks_r{left}_r{right}_disjoint_pilot_v97 :
    z180K30ProjectiveD6UBlockR{left}PilotV97.Disjoint
      z180K30ProjectiveD6UBlockR{right}PilotV97 := by
  apply List.disjoint_iff_ne.mpr
  intro leftValue hleft rightValue hright hequal
  obtain ⟨point, hpoint, hresidue⟩ :=
    z180_k30_projective_d6_u_block_r{left}_marker_pilot_v97 leftValue hleft
  have hclasses :=
    z180_k30_projective_d6_u_block_r{right}_residues_pilot_v97
      rightValue hright point (hequal ▸ hpoint)
  rcases hclasses with hzero | hrightResidue <;> omega
"""
            )
    return "\n".join(pieces)


def bridge_aggregate_content(
    leaves: list[CombLeaf], singleton_index: int, row_count: int
) -> str:
    imports = [
        "import Fuglede.Z180K30ExceptionalProjectiveProfileD6UAlgebraicIndexPermPilotV97",
        *(f"import Fuglede.{bridge_row_module(row)}" for row in range(row_count)),
    ]
    index_rows = ",\n    ".join(
        f"z180K30ProjectiveD6UIndexRow{row:02d}PilotV97"
        for row in range(row_count)
    )
    source_rows = ",\n    ".join(
        f"z180K30ProjectiveD6USourceRow{row:02d}PilotV97"
        for row in range(row_count)
    )
    target_rows = ",\n    ".join(
        f"z180K30ProjectiveD6UTargetRow{row:02d}PilotV97"
        for row in range(row_count)
    )
    index_source_row_names = [
        f"z180_k30_projective_d6_u_index_source_row_{row:02d}_pilot_v97"
        for row in range(row_count)
    ]
    source_target_row_names = [
        f"z180_k30_projective_d6_u_source_target_row_{row:02d}_pilot_v97"
        for row in range(row_count)
    ]
    tree = " ++\n      ".join(
        f"z180K30ProjectiveD6UCombChunksPilotV97 {CHUNK_FUEL} [0] "
        f"z180K30ProjectiveD6UTailR{residue}PilotV97 5"
        for residue in range(1, 6)
    )
    selection_names = [f"z180_k30_projective_d6_u_selection_s{r}_pilot_v97" for r in range(6)]
    selection_names += [
        f"z180_k30_projective_d6_u_selection_p{first}_{second}_pilot_v97"
        for first in range(6)
        for second in range(6)
    ]
    selection_simp = ",\n    ".join(selection_names)
    return f"""{chr(10).join(imports)}

/-!
Structural D6-U aggregate.  Every RawSet equality certificate is imported
from one leaf of size at most ten; aggregation and duplicate elimination are
proved generically.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6UIndexChunksPilotV97 : List (List Nat) :=
  [ {index_rows}].flatten

def z180K30ProjectiveD6USourceChunksPilotV97 : List (List RawSet) :=
  [ {source_rows}].flatten

def z180K30ProjectiveD6UTargetChunksPilotV97 : List (List RawSet) :=
  [ {target_rows}].flatten

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
{pairwise_cons_steps(index_source_row_names)}

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_source_target_chunks_pilot_v97 :
    z180K30ProjectiveD6USourceChunksPilotV97 =
      z180K30ProjectiveD6UTargetChunksPilotV97 := by
  unfold z180K30ProjectiveD6USourceChunksPilotV97
  unfold z180K30ProjectiveD6UTargetChunksPilotV97
  apply congrArg (fun rows : List (List (List RawSet)) => rows.flatten)
{pairwise_cons_steps(source_target_row_names)}

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_target_chunks_tree_pilot_v97 :
    z180K30ProjectiveD6UTargetChunksPilotV97 =
      [z180K30ProjectiveD6UAPilotV97] ::
        ({tree}) := by
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

private theorem z180_k30_projective_d6_u_filter_cons_zero_pilot_v97
    {{alpha : Type}} [DecidableEq alpha]
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

{chr(10).join(selection_theorem_text(first=None, second=residue) for residue in range(1, 6))}

{chr(10).join(selection_theorem_text(first=first, second=second) for first in range(6) for second in range(6))}

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
    {selection_simp}, List.nil_append, List.append_nil, List.append_assoc]

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d6_u_choices_raw_blocks_pilot_v97 :
    normalizedProjectiveUChoicesV88 6 =
      z180K30ProjectiveD6UAPilotV97 ::
        z180K30ProjectiveD6URawBlocksTwicePilotV97.flatten := by
  rw [z180_k30_projective_d6_u_choices_expanded_pilot_v97]
  rfl

{block_structural_theorems_text()}

private theorem z180_k30_projective_d6_u_erase_cons_flatten_pilot_v97
    {{alpha : Type}} [BEq alpha] [LawfulBEq alpha]
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
        z180_k30_projective_d6_u_erase_nodup_pilot_v97 htail]

private theorem z180_k30_projective_d6_u_removeAll_self_pilot_v97
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

private theorem z180_k30_projective_d6_u_erase_double_pilot_v97
    {{alpha : Type}} [BEq alpha] [LawfulBEq alpha]
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
    {{alpha : Type}} [BEq alpha] [LawfulBEq alpha]
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
"""


def selection_theorem_text(first: int | None, second: int) -> str:
    if first is None:
        name = f"z180_k30_projective_d6_u_selection_s{second}_pilot_v97"
        selection = f"[{second}]"
        body = """by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 SELECTION) 6
      (by decide)""".replace("SELECTION", selection)
        return f"theorem {name} :\n    normalizedProjectiveUChoicesForSelectionV88 6 {selection} = [] := {body}\n"

    name = f"z180_k30_projective_d6_u_selection_p{first}_{second}_pilot_v97"
    selection = f"[{first}, {second}]"
    if first == 0 and second == 0:
        return f"""theorem {name} :
    normalizedProjectiveUChoicesForSelectionV88 6 {selection} =
      [z180K30ProjectiveD6UAPilotV97] := by
  decide
"""
    if first == 0 and second > 0:
        residue = second
    elif second == 0 and first > 0:
        residue = first
    else:
        residue = 0
    if residue:
        return f"""theorem {name} :
    normalizedProjectiveUChoicesForSelectionV88 6 {selection} =
      z180K30ProjectiveD6UCombPilotV97 [0]
        z180K30ProjectiveD6UTailR{residue}PilotV97 5 := by
  exact z180_k30_projective_d6_u_selection_zero_residue_pilot_v97
    {selection} z180K30ProjectiveD6UTailR{residue}PilotV97 (by decide) (by decide)
"""
    proof = f"""by
  unfold normalizedProjectiveUChoicesForSelectionV88
  exact z180_k30_projective_d6_u_filter_without_zero_pilot_v97
    (0 : RawPoint) (normalizedProjectiveClassDomainV88 6 {selection}) 6
      (by decide)"""
    return f"theorem {name} :\n    normalizedProjectiveUChoicesForSelectionV88 6 {selection} = [] := {proof}\n"


def v_content() -> str:
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D6VBase
import Mathlib.Data.List.Sublists

/-! Source-only algebraic D6-V completeness pilot. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD6VPilotV97 : RawSet := {lean_list(A)}

private theorem z180_k30_projective_d6_v_filter_without_zero_pilot_v97
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

private theorem z180_k30_projective_d6_v_filter_cons_zero_pilot_v97
    {{alpha : Type}} [DecidableEq alpha]
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
"""


def build() -> tuple[dict[Path, str], dict[str, object]]:
    member_paths = sorted(FUGLEDE.glob("Z180K30ExceptionalProjectiveProfileMembersV97D6S*.lean"))
    profiles = parse_profiles(member_paths)
    u_names = parse_source_names(U_BASE, "U")
    v_names = parse_source_names(V_BASE, "V")
    missing = [name for name in (*u_names, *v_names) if name not in profiles]
    if missing:
        raise RuntimeError(f"missing profile definitions: {missing[:5]}")
    u_source = [profiles[name] for name in u_names]
    v_source = [profiles[name] for name in v_names]
    canonical = canonical_u()
    choices = normalized_u_choices()
    unique = stable_dedup(choices)
    expected_choices = [A, A] + sum((block(residue) for residue in range(1, 6)), []) * 2
    if choices != expected_choices:
        raise RuntimeError("D6U normalized order differs from the audited A/A/forward/reverse order")
    if unique != canonical:
        raise RuntimeError("D6U stable dedup does not equal the canonical order")
    if len(u_source) != 2306 or len(set(u_source)) != 2306:
        raise RuntimeError("D6U SourceGrouped does not contain 2306 distinct values")
    if set(u_source) != set(canonical):
        raise RuntimeError("D6U SourceGrouped and canonical values differ")
    if v_source != [A]:
        raise RuntimeError("D6V SourceGrouped is not the expected singleton")
    indices = tuple(u_source.index(value) for value in canonical)
    if sorted(indices) != list(range(2306)):
        raise RuntimeError("D6U canonical indices are not a permutation")

    outputs: dict[Path, str] = {CORE: core_content(indices)}
    source_bucket_sizes: list[int] = []
    target_bucket_sizes: list[int] = []
    for bucket in range(INDEX_BUCKET_COUNT):
        source_size = sum(index % INDEX_BUCKET_COUNT == bucket for index in range(2306))
        target_size = sum(index % INDEX_BUCKET_COUNT == bucket for index in indices)
        if source_size > 10 or target_size > 10:
            raise RuntimeError(f"index bucket {bucket} exceeds ten values")
        source_bucket_sizes.append(source_size)
        target_bucket_sizes.append(target_size)
        outputs[index_leaf_path(bucket)] = index_leaf_content(bucket, source_size, target_size)
    outputs[INDEX_AGG] = index_aggregate_content()

    singleton_index = indices[0]
    leaves: list[CombLeaf] = []
    canonical_offset = 1
    leaf_number = 0
    for residue in range(1, 6):
        raw = block(residue)
        filtered = [value for value in raw if value != A]
        specs = leaf_specs(CHUNK_FUEL, (0,), TAILS[residue], 5)
        local_offset = 0
        for local_number, (frame, domain, length) in enumerate(specs):
            raw_targets = tuple(comb(frame, domain, length))
            targets = tuple(value for value in raw_targets if value != A)
            leaf_indices = indices[canonical_offset + local_offset : canonical_offset + local_offset + len(targets)]
            actual = tuple(u_source[index] for index in leaf_indices)
            if actual != targets:
                raise RuntimeError(
                    f"D6U leaf {leaf_number:03d} source/target mismatch at canonical offset "
                    f"{canonical_offset + local_offset}"
                )
            leaf = CombLeaf(
                leaf_number,
                residue,
                local_number,
                canonical_offset + local_offset,
                tuple(leaf_indices),
                frame,
                domain,
                length,
                raw_targets,
                targets,
            )
            if max(len(raw_targets), len(targets)) > 10:
                raise RuntimeError(
                    f"D6U leaf {leaf_number:03d} evaluates more than ten RawSets"
                )
            leaves.append(leaf)
            outputs[leaf.path] = comb_leaf_content(leaf)
            local_offset += len(targets)
            leaf_number += 1
        if local_offset != len(filtered):
            raise RuntimeError(f"D6U residue {residue} leaf flatten length mismatch")
        canonical_offset += len(filtered)
    if len(leaves) != 315 or canonical_offset != 2306:
        raise RuntimeError(f"unexpected D6U leaf shape: {len(leaves)} leaves, offset {canonical_offset}")
    bridge_entries: list[CombLeaf | None] = [None, *leaves]
    bridge_rows = [
        bridge_entries[start : start + BRIDGE_ROW_SIZE]
        for start in range(0, len(bridge_entries), BRIDGE_ROW_SIZE)
    ]
    for row, entries in enumerate(bridge_rows):
        outputs[bridge_row_path(row)] = bridge_row_content(
            row, entries, singleton_index
        )
    outputs[BRIDGE_AGG] = bridge_aggregate_content(
        leaves, singleton_index, len(bridge_rows)
    )
    outputs[V_OUT] = v_content()

    for path, content in outputs.items():
        hit = FORBIDDEN.search(content)
        if hit:
            raise RuntimeError(f"forbidden token {hit.group(0)!r} in {rel(path)}")
    for active in ACTIVE_FILES:
        text = active.read_text(encoding="utf-8")
        for aggregate in (INDEX_AGG.stem, BRIDGE_AGG.stem, V_OUT.stem):
            if aggregate in text:
                raise RuntimeError(f"isolated D6 pilot leaked into {rel(active)}")

    expected_imports = [
        INDEX_AGG.stem,
        *(bridge_row_module(row) for row in range(len(bridge_rows))),
    ]
    actual_imports = [
        line.removeprefix("import Fuglede.")
        for line in outputs[BRIDGE_AGG].splitlines()
        if line.startswith("import Fuglede.")
    ]
    if actual_imports != expected_imports:
        raise RuntimeError("D6U bridge import graph differs from the generated acyclic graph")
    for leaf in leaves:
        content = outputs[leaf.path]
        if content.count("import ") != 1 or content.count("\n  decide\n") != 1:
            raise RuntimeError(f"unexpected D6U leaf proof shape: {rel(leaf.path)}")
    for row, entries in enumerate(bridge_rows):
        content = outputs[bridge_row_path(row)]
        if len(entries) > BRIDGE_ROW_SIZE:
            raise RuntimeError(f"D6U bridge row {row:02d} exceeds its bound")
        expected_import_count = 1 + sum(entry is not None for entry in entries)
        if content.count("import ") != expected_import_count:
            raise RuntimeError(f"unexpected D6U bridge row imports: {row:02d}")

    inputs = [
        U_BASE,
        V_BASE,
        *ACTIVE_FILES,
        *INTEGRATION_FILES,
        *member_paths,
    ]
    manifest: dict[str, object] = {
        "schema": "z180-k30-d6-algebraic-v97/1",
        "generator": rel(Path(__file__).resolve()),
        "generator_sha256": sha256_file(Path(__file__).resolve()),
        "inputs": {rel(path): sha256_file(path) for path in inputs},
        "invariants": {
            "u_source_count": len(u_source),
            "u_source_distinct_count": len(set(u_source)),
            "u_normalized_choices_before_dedup": len(choices),
            "u_canonical_count": len(canonical),
            "u_comb_leaf_count": len(leaves),
            "u_bridge_row_count": len(bridge_rows),
            "u_maximum_certificates_per_bridge_row": max(map(len, bridge_rows)),
            "u_total_rawset_leaf_count_including_singleton": len(leaves) + 1,
            "u_maximum_rawsets_per_leaf_before_filter": max(
                [1, *(len(leaf.raw_targets) for leaf in leaves)]
            ),
            "u_maximum_rawsets_per_leaf_after_filter": max(
                [1, *(len(leaf.targets) for leaf in leaves)]
            ),
            "u_index_bucket_count": INDEX_BUCKET_COUNT,
            "u_maximum_nat_values_per_index_bucket": max(
                max(source_bucket_sizes), max(target_bucket_sizes)
            ),
            "u_canonical_indices_sha256": sha256_text(json.dumps(indices)),
            "u_canonical_values_sha256": sha256_text(json.dumps(canonical)),
            "v_unique_count": 1,
            "generated_import_graph_acyclic": True,
            "active_manifests_isolated": True,
            "integration_files_hashed_without_leak_rejection": True,
            "forbidden_lean_tokens_absent": True,
            "lean_was_run": False,
        },
        "index_buckets": [
            {
                "bucket": bucket,
                "source_size": source_bucket_sizes[bucket],
                "target_size": target_bucket_sizes[bucket],
                "file": rel(index_leaf_path(bucket)),
                "file_sha256": sha256_text(outputs[index_leaf_path(bucket)]),
            }
            for bucket in range(INDEX_BUCKET_COUNT)
        ],
        "comb_leaves": [
            {
                "number": leaf.number,
                "residue": leaf.residue,
                "local_number": leaf.local_number,
                "offset": leaf.offset,
                "size": len(leaf.targets),
                "raw_size": len(leaf.raw_targets),
                "indices": list(leaf.indices),
                "frame": list(leaf.frame),
                "domain": list(leaf.domain),
                "length": leaf.length,
                "targets_sha256": sha256_text(json.dumps(leaf.targets)),
                "file": rel(leaf.path),
                "file_sha256": sha256_text(outputs[leaf.path]),
            }
            for leaf in leaves
        ],
        "bridge_rows": [
            {
                "row": row,
                "size": len(entries),
                "includes_singleton": entries[0] is None,
                "file": rel(bridge_row_path(row)),
                "file_sha256": sha256_text(outputs[bridge_row_path(row)]),
            }
            for row, entries in enumerate(bridge_rows)
        ],
        "compile_stages": [
            {
                "stage": 1,
                "kind": "core",
                "files": [rel(CORE)],
            },
            {
                "stage": 2,
                "kind": "nat_index_leaves",
                "files": [
                    rel(index_leaf_path(bucket))
                    for bucket in range(INDEX_BUCKET_COUNT)
                ],
            },
            {
                "stage": 3,
                "kind": "nat_index_aggregate",
                "files": [rel(INDEX_AGG)],
            },
            {
                "stage": 4,
                "kind": "rawset_comb_leaves",
                "files": [rel(leaf.path) for leaf in leaves],
            },
            {
                "stage": 5,
                "kind": "bounded_bridge_rows",
                "files": [
                    rel(bridge_row_path(row)) for row in range(len(bridge_rows))
                ],
            },
            {
                "stage": 6,
                "kind": "u_bridge_aggregate",
                "files": [rel(BRIDGE_AGG)],
            },
            {
                "stage": 7,
                "kind": "v_singleton",
                "files": [rel(V_OUT)],
            },
        ],
        "outputs": {rel(path): sha256_text(content) for path, content in outputs.items()},
    }
    return outputs, manifest


def manifest_text(manifest: dict[str, object]) -> str:
    return json.dumps(manifest, indent=2, sort_keys=True) + "\n"


def write_outputs(outputs: dict[Path, str], manifest: dict[str, object]) -> None:
    for path, content in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text(encoding="utf-8") != content:
            path.write_text(content, encoding="utf-8", newline="\n")
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    expected_manifest = manifest_text(manifest)
    if (
        not MANIFEST.exists()
        or MANIFEST.read_text(encoding="utf-8") != expected_manifest
    ):
        MANIFEST.write_text(expected_manifest, encoding="utf-8", newline="\n")


def check_outputs(outputs: dict[Path, str], manifest: dict[str, object]) -> None:
    failures: list[str] = []
    for path, expected in outputs.items():
        if not path.exists():
            failures.append(f"missing {rel(path)}")
        elif path.read_text(encoding="utf-8") != expected:
            failures.append(f"content mismatch {rel(path)}")
    expected_manifest = manifest_text(manifest)
    if not MANIFEST.exists():
        failures.append(f"missing {rel(MANIFEST)}")
    elif MANIFEST.read_text(encoding="utf-8") != expected_manifest:
        failures.append(f"content mismatch {rel(MANIFEST)}")
    if failures:
        raise RuntimeError("generated D6 algebraic check failed:\n  " + "\n  ".join(failures))


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs, manifest = build()
    if args.write:
        write_outputs(outputs, manifest)
        action = "wrote"
    else:
        check_outputs(outputs, manifest)
        action = "checked"
    invariants = manifest["invariants"]
    print(
        f"{action} {len(outputs)} Lean files; "
        f"rawset_leaves={invariants['u_total_rawset_leaf_count_including_singleton']}; "
        f"max_rawsets={invariants['u_maximum_rawsets_per_leaf_before_filter']}; "
        f"index_buckets={invariants['u_index_bucket_count']}; "
        f"max_nat={invariants['u_maximum_nat_values_per_index_bucket']}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
