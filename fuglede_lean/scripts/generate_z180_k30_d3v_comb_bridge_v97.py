#!/usr/bin/env python3
"""Generate and authenticate the bounded D3-V combination bridge."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FUGLEDE = ROOT / "Fuglede"
INDEX_SOURCE = FUGLEDE / (
    "Z180K30ExceptionalProjectiveProfileD3VIndexPermBasePilotV97.lean"
)
GROUP_SOURCE = FUGLEDE / (
    "Z180K30ExceptionalProjectiveProfileCompletenessV97D3VBase.lean"
)
INDEX_AGGREGATE = FUGLEDE / (
    "Z180K30ExceptionalProjectiveProfileD3VIndexPermPilotV97.lean"
)
COMB_CORE = FUGLEDE / (
    "Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97.lean"
)
AGGREGATE = FUGLEDE / (
    "Z180K30ExceptionalProjectiveProfileD3VCombBridgePilotV97.lean"
)
MANIFEST = ROOT / "generated" / "z180_k30_d3v_comb_bridge_v97.manifest.json"
ACTIVE_MANIFESTS = [
    ROOT / "Fuglede.lean",
    FUGLEDE / "Z180K30ExceptionalProjectiveProfileDataV97D3.lean",
]

INDEX_DEF = "def z180K30ProjectiveD3VCanonicalIndicesPilotV97"
GROUP_DEF = "def z180K30ProjectiveCompletenessV97D3VSourceGrouped"
PROFILE_NAME = re.compile(r"z180K30ProfileV97D3V\d+M\d+")
PROFILE_DEF = re.compile(
    r"def\s+(z180K30ProfileV97D3V\d+M\d+)\s*:\s*RawSet\s*:=\s*"
    r"\[([^\]]*)\]"
)
FORBIDDEN_LEAN = re.compile(
    r"\b(?:native_decide|unsafe|sorry|axiom|choose|drop|take)\b"
)


@dataclass(frozen=True)
class Leaf:
    number: int
    offset: int
    indices: tuple[int, ...]
    prefix: tuple[int, ...]
    domain: tuple[int, ...]
    length: int
    targets: tuple[tuple[int, ...], ...]

    @property
    def tag(self) -> str:
        return f"{self.number:02d}"

    @property
    def module(self) -> str:
        return (
            "Z180K30ExceptionalProjectiveProfileD3VCombLeaf"
            f"{self.tag}PilotV97"
        )

    @property
    def path(self) -> Path:
        return FUGLEDE / f"{self.module}.lean"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def file_sha256(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def bracket_body_after(text: str, marker: str) -> str:
    start = text.index(marker)
    assign = text.index(":=", start)
    left = text.index("[", assign)
    right = text.index("]", left)
    return text[left + 1 : right]


def parse_nat_list(text: str, marker: str) -> tuple[int, ...]:
    return tuple(int(value) for value in re.findall(r"\d+", bracket_body_after(text, marker)))


def parse_source_names(text: str) -> tuple[str, ...]:
    return tuple(PROFILE_NAME.findall(bracket_body_after(text, GROUP_DEF)))


def parse_profiles(paths: list[Path]) -> dict[str, tuple[int, ...]]:
    profiles: dict[str, tuple[int, ...]] = {}
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for match in PROFILE_DEF.finditer(text):
            values = tuple(int(value) for value in re.findall(r"\d+", match.group(2)))
            previous = profiles.setdefault(match.group(1), values)
            if previous != values:
                raise RuntimeError(f"conflicting profile definition: {match.group(1)}")
    return profiles


def sublists_len_tail_first(length: int, domain: tuple[int, ...]) -> list[tuple[int, ...]]:
    if length == 0:
        return [()]
    if not domain:
        return []
    head, tail = domain[0], domain[1:]
    without = sublists_len_tail_first(length, tail)
    with_head = [
        (head,) + suffix
        for suffix in sublists_len_tail_first(length - 1, tail)
    ]
    return without + with_head


def structural_leaf_specs(
    fuel: int,
    prefix: tuple[int, ...],
    domain: tuple[int, ...],
    length: int,
) -> list[tuple[tuple[int, ...], tuple[int, ...], int]]:
    if fuel == 0 or length == 0 or not domain:
        return [(prefix, domain, length)]
    head, tail = domain[0], domain[1:]
    return structural_leaf_specs(fuel - 1, prefix, tail, length) + structural_leaf_specs(
        fuel - 1, prefix + (head,), tail, length - 1
    )


def lean_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def wrapped_names(names: list[str], indent: str, width: int = 98) -> str:
    lines: list[str] = []
    current = indent
    for index, name in enumerate(names):
        token = name + ("," if index + 1 < len(names) else "")
        if len(current) > len(indent) and len(current) + 1 + len(token) > width:
            lines.append(current)
            current = indent + token
        else:
            current += (" " if len(current) > len(indent) else "") + token
    lines.append(current)
    return "\n".join(lines)


def leaf_content(leaf: Leaf) -> str:
    tag = leaf.tag
    size = len(leaf.indices)
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97

/-! Generated bounded D3-V bridge leaf {tag}: offset {leaf.offset}, size {size}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCombLeaf{tag}IndicesPilotV97 : List Nat :=
  {lean_list(leaf.indices)}

def z180K30ProjectiveD3VCombLeaf{tag}SourcePilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombLeaf{tag}IndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

def z180K30ProjectiveD3VCombLeaf{tag}TargetPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCombPilotV97
    {lean_list(leaf.prefix)} {lean_list(leaf.domain)} {leaf.length}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_comb_leaf{tag}_bridge_pilot_v97 :
    z180K30ProjectiveD3VCombLeaf{tag}SourcePilotV97 =
      z180K30ProjectiveD3VCombLeaf{tag}TargetPilotV97 := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def erase_and_filter_section() -> str:
    return """
private theorem z180_k30_projective_d3_v_comb_erase_eq_self_pilot_v97
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall {values : List alpha}, values.Nodup -> values.eraseDups = values
  | [], _ => rfl
  | head :: tail, hnodup => by
      rw [List.nodup_cons] at hnodup
      have hfilter : (tail.filter fun point => !point == head) = tail := by
        apply List.filter_eq_self.mpr
        intro point hpoint
        have hne : point ≠ head := by
          intro heq
          apply hnodup.1
          simpa [heq] using hpoint
        simp [hne]
      rw [List.eraseDups_cons, hfilter,
        z180_k30_projective_d3_v_comb_erase_eq_self_pilot_v97 hnodup.2]

private theorem z180_k30_projective_d3_v_comb_filter_without_zero_pilot_v97
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (domain : List alpha) (length : Nat)
    (hpoint : point ∉ domain) :
    (List.sublistsLen length domain).filter
      (fun values => decide (point ∈ values)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro values hvalues hcontains
  have hmember : point ∈ values := of_decide_eq_true hcontains
  have hsublist : values <+ domain :=
    (List.mem_sublistsLen.mp hvalues).1
  exact hpoint (hsublist.subset hmember)

private theorem z180_k30_projective_d3_v_comb_filter_cons_zero_pilot_v97
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (values : List (List alpha)) :
    (values.map (List.cons point)).filter
      (fun set => decide (point ∈ set)) =
        values.map (List.cons point) := by
  apply List.filter_eq_self.mpr
  intro set hset
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp hset
  exact decide_eq_true List.mem_cons_self

theorem z180_k30_projective_d3_v_comb_base_pilot_v97 :
    baseForDivisor 3 =
      (0 : RawPoint) :: z180K30ProjectiveD3VPositiveTailCombPilotV97 := by
  decide

theorem z180_k30_projective_d3_v_comb_choices_sublists_pilot_v97 :
    normalizedProjectiveVChoicesV88 3 =
      (List.sublistsLen 5
        z180K30ProjectiveD3VPositiveTailCombPilotV97).map
          (List.cons (0 : RawPoint)) := by
  unfold normalizedProjectiveVChoicesV88
  rw [z180_k30_projective_d3_v_comb_base_pilot_v97,
    List.sublistsLen_succ_cons, List.filter_append]
  rw [z180_k30_projective_d3_v_comb_filter_without_zero_pilot_v97
    (0 : RawPoint) z180K30ProjectiveD3VPositiveTailCombPilotV97 6 (by decide)]
  rw [List.nil_append]
  exact z180_k30_projective_d3_v_comb_filter_cons_zero_pilot_v97
    (0 : RawPoint)
    (List.sublistsLen 5 z180K30ProjectiveD3VPositiveTailCombPilotV97)

theorem z180_k30_projective_d3_v_comb_unique_sublists_pilot_v97 :
    normalizedProjectiveUniqueVChoicesV89 3 =
      (List.sublistsLen 5
        z180K30ProjectiveD3VPositiveTailCombPilotV97).map
          (List.cons (0 : RawPoint)) := by
  unfold normalizedProjectiveUniqueVChoicesV89
  rw [z180_k30_projective_d3_v_comb_choices_sublists_pilot_v97]
  apply z180_k30_projective_d3_v_comb_erase_eq_self_pilot_v97
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide
"""


def aggregate_content(leaves: list[Leaf]) -> str:
    imports = [
        "import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermPilotV97"
    ] + [f"import Fuglede.{leaf.module}" for leaf in leaves]
    index_names = [
        f"z180K30ProjectiveD3VCombLeaf{leaf.tag}IndicesPilotV97"
        for leaf in leaves
    ]
    source_names = [
        f"z180K30ProjectiveD3VCombLeaf{leaf.tag}SourcePilotV97"
        for leaf in leaves
    ]
    target_names = [
        f"z180K30ProjectiveD3VCombLeaf{leaf.tag}TargetPilotV97"
        for leaf in leaves
    ]
    bridge_names = [
        f"z180_k30_projective_d3_v_comb_leaf{leaf.tag}_bridge_pilot_v97"
        for leaf in leaves
    ]
    source_target_steps = "\n".join(
        (
            "  apply List.cons.injEq.mpr\n"
            "  constructor\n"
            f"  · exact {bridge}"
            + ("\n  · rfl" if index + 1 == len(bridge_names) else "")
        )
        for index, bridge in enumerate(bridge_names)
    )
    return f"""{chr(10).join(imports)}

/-!
Generated structural aggregate for all 63 bounded D3-V combination leaves.
Every finite `RawSet` decision is confined to one imported leaf of size at
most ten; this module only replays list equalities.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCanonicalIndexChunksPilotV97 : List (List Nat) :=
  [{chr(10).join('   ' + name + (',' if i + 1 < len(index_names) else '') for i, name in enumerate(index_names))}]

def z180K30ProjectiveD3VCanonicalSourceChunksPilotV97 :
    List (List RawSet) :=
  [{chr(10).join('   ' + name + (',' if i + 1 < len(source_names) else '') for i, name in enumerate(source_names))}]

def z180K30ProjectiveD3VCanonicalTargetChunksPilotV97 :
    List (List RawSet) :=
  [{chr(10).join('   ' + name + (',' if i + 1 < len(target_names) else '') for i, name in enumerate(target_names))}]

theorem z180_k30_projective_d3_v_comb_index_chunks_flatten_pilot_v97 :
    z180K30ProjectiveD3VCanonicalIndexChunksPilotV97.flatten =
      z180K30ProjectiveD3VCanonicalIndicesPilotV97 := by
  rfl

theorem z180_k30_projective_d3_v_comb_index_chunks_map_pilot_v97 :
    (z180K30ProjectiveD3VCanonicalIndexChunksPilotV97.map fun indices =>
      indices.map z180K30ProjectiveD3VSourceAtPilotV97) =
        z180K30ProjectiveD3VCanonicalSourceChunksPilotV97 := by
  rfl

theorem z180_k30_projective_d3_v_comb_source_target_chunks_pilot_v97 :
    z180K30ProjectiveD3VCanonicalSourceChunksPilotV97 =
      z180K30ProjectiveD3VCanonicalTargetChunksPilotV97 := by
  unfold z180K30ProjectiveD3VCanonicalSourceChunksPilotV97
  unfold z180K30ProjectiveD3VCanonicalTargetChunksPilotV97
{source_target_steps.rstrip()}

theorem z180_k30_projective_d3_v_comb_target_chunks_tree_pilot_v97 :
    z180K30ProjectiveD3VCanonicalTargetChunksPilotV97 =
      z180K30ProjectiveD3VCombChunkTreePilotV97 := by
  rfl

theorem z180_k30_projective_d3_v_comb_mapped_chunks_tree_pilot_v97 :
    (z180K30ProjectiveD3VCanonicalIndexChunksPilotV97.map fun indices =>
      indices.map z180K30ProjectiveD3VSourceAtPilotV97) =
        z180K30ProjectiveD3VCombChunkTreePilotV97 := by
  exact z180_k30_projective_d3_v_comb_index_chunks_map_pilot_v97.trans
    (z180_k30_projective_d3_v_comb_source_target_chunks_pilot_v97.trans
      z180_k30_projective_d3_v_comb_target_chunks_tree_pilot_v97)

theorem z180_k30_projective_d3_v_indexed_sublists_chunked_pilot_v97 :
    z180K30ProjectiveD3VCanonicalIndexedPilotV97 =
      (List.sublistsLen 5
        z180K30ProjectiveD3VPositiveTailCombPilotV97).map
          (List.cons (0 : RawPoint)) := by
  unfold z180K30ProjectiveD3VCanonicalIndexedPilotV97
  rw [← z180_k30_projective_d3_v_comb_index_chunks_flatten_pilot_v97,
    List.map_flatten,
    z180_k30_projective_d3_v_comb_mapped_chunks_tree_pilot_v97]
  exact z180_k30_projective_d3_v_comb_chunk_tree_flatten_pilot_v97
{erase_and_filter_section()}
theorem z180_k30_projective_d3_v_complete_comb_chunked_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3VSourceGrouped.Perm
      (normalizedProjectiveUniqueVChoicesV89 3) := by
  exact z180_k30_projective_d3_v_source_perm_indexed_pilot_v97.trans
    (List.Perm.of_eq
      (z180_k30_projective_d3_v_indexed_sublists_chunked_pilot_v97.trans
        z180_k30_projective_d3_v_comb_unique_sublists_pilot_v97.symm))

#print axioms z180_k30_projective_d3_v_indexed_sublists_chunked_pilot_v97
#print axioms z180_k30_projective_d3_v_complete_comb_chunked_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
"""


def build() -> tuple[list[Leaf], dict[Path, str], dict[str, object]]:
    index_text = INDEX_SOURCE.read_text(encoding="utf-8")
    group_text = GROUP_SOURCE.read_text(encoding="utf-8")
    canonical_indices = parse_nat_list(index_text, INDEX_DEF)
    source_names = parse_source_names(group_text)
    member_paths = sorted(
        FUGLEDE.glob("Z180K30ExceptionalProjectiveProfileMembersV97D3S*.lean")
    )
    profiles = parse_profiles(member_paths)
    if len(canonical_indices) != 462:
        raise RuntimeError(f"expected 462 canonical indices, got {len(canonical_indices)}")
    if len(source_names) != 462:
        raise RuntimeError(f"expected 462 source names, got {len(source_names)}")
    if sorted(canonical_indices) != list(range(462)):
        raise RuntimeError("canonical indices are not a permutation of range 462")
    missing = [name for name in source_names if name not in profiles]
    if missing:
        raise RuntimeError(f"missing profile definitions: {missing[:3]}")
    source_values = tuple(profiles[name] for name in source_names)

    specs = structural_leaf_specs(
        6, (0,), (3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33), 5
    )
    leaves: list[Leaf] = []
    offset = 0
    all_targets: list[tuple[int, ...]] = []
    for number, (prefix, domain, length) in enumerate(specs):
        targets = tuple(
            prefix + suffix
            for suffix in sublists_len_tail_first(length, domain)
        )
        size = len(targets)
        indices = canonical_indices[offset : offset + size]
        actual = tuple(source_values[index] for index in indices)
        if actual != targets:
            raise RuntimeError(
                f"leaf {number:02d} source/target mismatch at offset {offset}"
            )
        leaves.append(
            Leaf(number, offset, indices, prefix, domain, length, targets)
        )
        all_targets.extend(targets)
        offset += size

    expected_root = [
        (0,) + suffix
        for suffix in sublists_len_tail_first(
            5, (3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33)
        )
    ]
    if len(leaves) != 63 or offset != 462:
        raise RuntimeError(f"unexpected tree shape: {len(leaves)} leaves, {offset} values")
    if max(len(leaf.targets) for leaf in leaves) > 10:
        raise RuntimeError("a bounded decision leaf exceeds ten RawSet values")
    if all_targets != expected_root:
        raise RuntimeError("structural leaves do not flatten to the root enumeration")
    if tuple(source_values[index] for index in canonical_indices) != tuple(expected_root):
        raise RuntimeError("canonical source order does not equal the root enumeration")

    outputs = {leaf.path: leaf_content(leaf) for leaf in leaves}
    outputs[AGGREGATE] = aggregate_content(leaves)
    for path, content in outputs.items():
        forbidden = FORBIDDEN_LEAN.search(content)
        if forbidden:
            raise RuntimeError(
                f"forbidden Lean token {forbidden.group(0)!r} in {relative(path)}"
            )
    for leaf in leaves:
        content = outputs[leaf.path]
        expected_import = (
            "import Fuglede."
            "Z180K30ExceptionalProjectiveProfileD3VCombCorePilotV97\n"
        )
        if not content.startswith(expected_import):
            raise RuntimeError(f"unexpected leaf import: {relative(leaf.path)}")
        if content.count("import ") != 1 or content.count("\n  decide\n") != 1:
            raise RuntimeError(f"unexpected leaf proof shape: {relative(leaf.path)}")
    aggregate_imports = [
        line.removeprefix("import Fuglede.")
        for line in outputs[AGGREGATE].splitlines()
        if line.startswith("import Fuglede.")
    ]
    expected_aggregate_imports = [
        "Z180K30ExceptionalProjectiveProfileD3VIndexPermPilotV97",
        *(leaf.module for leaf in leaves),
    ]
    if aggregate_imports != expected_aggregate_imports:
        raise RuntimeError("aggregate imports differ from the acyclic generated graph")
    aggregate_module = AGGREGATE.stem
    for path in ACTIVE_MANIFESTS:
        if aggregate_module in path.read_text(encoding="utf-8"):
            raise RuntimeError(f"generated aggregate leaked into {relative(path)}")

    inputs = [
        INDEX_SOURCE,
        GROUP_SOURCE,
        INDEX_AGGREGATE,
        COMB_CORE,
        *ACTIVE_MANIFESTS,
        *member_paths,
    ]
    manifest: dict[str, object] = {
        "schema": "z180-k30-d3v-comb-bridge-v97/1",
        "generator": relative(Path(__file__).resolve()),
        "generator_sha256": file_sha256(Path(__file__).resolve()),
        "inputs": {relative(path): file_sha256(path) for path in inputs},
        "invariants": {
            "fuel": 6,
            "leaf_count": len(leaves),
            "maximum_rawsets_per_decision": max(len(leaf.targets) for leaf in leaves),
            "total_rawsets": sum(len(leaf.targets) for leaf in leaves),
            "canonical_indices_sha256": sha256_text(json.dumps(canonical_indices)),
            "root_targets_sha256": sha256_text(json.dumps(expected_root)),
            "source_names_sha256": sha256_text(json.dumps(source_names)),
            "generated_import_graph_acyclic": True,
            "active_manifests_isolated": True,
            "forbidden_lean_tokens_absent": True,
        },
        "leaves": [
            {
                "number": leaf.number,
                "offset": leaf.offset,
                "size": len(leaf.targets),
                "indices": list(leaf.indices),
                "prefix": list(leaf.prefix),
                "domain": list(leaf.domain),
                "length": leaf.length,
                "targets_sha256": sha256_text(json.dumps(leaf.targets)),
                "file": relative(leaf.path),
                "file_sha256": sha256_text(outputs[leaf.path]),
            }
            for leaf in leaves
        ],
        "aggregate": {
            "file": relative(AGGREGATE),
            "file_sha256": sha256_text(outputs[AGGREGATE]),
        },
    }
    return leaves, outputs, manifest


def manifest_text(manifest: dict[str, object]) -> str:
    return json.dumps(manifest, indent=2, sort_keys=True) + "\n"


def write_outputs(outputs: dict[Path, str], manifest: dict[str, object]) -> None:
    for path, content in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8", newline="\n")
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(manifest_text(manifest), encoding="utf-8", newline="\n")


def check_outputs(outputs: dict[Path, str], manifest: dict[str, object]) -> None:
    failures: list[str] = []
    for path, expected in outputs.items():
        if not path.exists():
            failures.append(f"missing {relative(path)}")
        elif path.read_text(encoding="utf-8") != expected:
            failures.append(f"content mismatch {relative(path)}")
    expected_manifest = manifest_text(manifest)
    if not MANIFEST.exists():
        failures.append(f"missing {relative(MANIFEST)}")
    elif MANIFEST.read_text(encoding="utf-8") != expected_manifest:
        failures.append(f"content mismatch {relative(MANIFEST)}")
    if failures:
        raise RuntimeError("generated bridge check failed:\n  " + "\n  ".join(failures))


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    leaves, outputs, manifest = build()
    if args.write:
        write_outputs(outputs, manifest)
        action = "wrote"
    else:
        check_outputs(outputs, manifest)
        action = "checked"
    sizes = [len(leaf.targets) for leaf in leaves]
    print(
        f"{action} {len(leaves)} leaves; total={sum(sizes)}; max={max(sizes)}; "
        f"aggregate={relative(AGGREGATE)}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
