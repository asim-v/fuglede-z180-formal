#!/usr/bin/env python3
"""Generate and authenticate the isolated D3U algebraic completeness pilot.

The Lean module produced here never asks one finite certificate to reduce the
complete normalized U enumeration.  It first rewrites that enumeration into
one singleton block and twelve ordered-pair rows.  The only finite filter
certificates are the singleton block, two halves of row zero, and the eleven
remaining rows; every nonempty target has at most six RawSets.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "Fuglede/Z180K30ExceptionalProjectiveProfileCompletenessV97D3UBase.lean"
MEMBER_GLOB = "Z180K30ExceptionalProjectiveProfileMembersV97D3S*.lean"
OUT = ROOT / "Fuglede/Z180K30ExceptionalProjectiveProfileD3UAlgebraicPilotV97.lean"
MANIFEST = ROOT / "generated/z180_k30_d3u_algebraic_v97.manifest.json"
MODULE = "Fuglede.Z180K30ExceptionalProjectiveProfileD3UAlgebraicPilotV97"
FINAL_THEOREM = "z180_k30_projective_d3_u_complete_algebraic_pilot_v97"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def rawset(residue: int) -> tuple[int, ...]:
    return (0, residue, 12, 12 + residue, 24, 24 + residue)


CANONICAL = [rawset(residue) for residue in range(1, 12)]
CANONICAL_LOW = CANONICAL[:5]
CANONICAL_HIGH = CANONICAL[5:]


def lean_rawset(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def lean_rawset_list(values: list[tuple[int, ...]]) -> str:
    return "[" + ", ".join(lean_rawset(value) for value in values) + "]"


def parse_source() -> tuple[list[str], dict[str, tuple[int, ...]], list[Path]]:
    base_text = BASE.read_text(encoding="utf-8")
    match = re.search(
        r"def z180K30ProjectiveCompletenessV97D3USourceGrouped\s*:\s*List RawSet\s*:=\s*\[(.*?)\]",
        base_text,
        re.S,
    )
    if not match:
        raise RuntimeError("D3U SourceGrouped definition not found")
    names = re.findall(r"z180K30ProfileV97D3U\d+M\d+", match.group(1))
    if len(names) != 11 or len(set(names)) != 11:
        raise RuntimeError(f"expected 11 distinct D3U source names, got {len(names)}")

    member_paths = sorted((ROOT / "Fuglede").glob(MEMBER_GLOB))
    definitions: dict[str, tuple[int, ...]] = {}
    definition_re = re.compile(
        r"def\s+(z180K30ProfileV97D3U\d+M\d+)\s*:\s*RawSet\s*:=\s*\[([^\]]*)\]"
    )
    for path in member_paths:
        text = path.read_text(encoding="utf-8")
        for name, body in definition_re.findall(text):
            definitions[name] = tuple(int(piece.strip()) for piece in body.split(","))
    missing = [name for name in names if name not in definitions]
    if missing:
        raise RuntimeError(f"missing D3U member definitions: {missing}")
    return names, definitions, member_paths


def choices_for_selection(selection: list[int]) -> list[tuple[int, ...]]:
    domain = [point for point in range(36) if any(point % 12 == residue for residue in selection)]
    return [values for values in itertools.combinations(domain, 6) if 0 in values]


def normalized_choices() -> tuple[list[tuple[int, ...]], list[list[tuple[int, ...]]], list[tuple[int, ...]]]:
    singleton = []
    for residue in range(12):
        singleton.extend(choices_for_selection([residue]))
    rows: list[list[tuple[int, ...]]] = []
    for first in range(12):
        row: list[tuple[int, ...]] = []
        for second in range(12):
            row.extend(choices_for_selection([first, second]))
        rows.append(row)
    return singleton, rows, singleton + [value for row in rows for value in row]


def stable_dedup(values: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    result: list[tuple[int, ...]] = []
    for value in values:
        if value not in result:
            result.append(value)
    return result


def render_decide_theorem(name: str, lhs: str, rhs: str) -> str:
    return f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem {name} :
    {lhs} = {rhs} := by
  decide
"""


def render_module(indices: list[int]) -> str:
    low_indices = indices[:5]
    high_indices = indices[5:]
    row_theorems = []
    for residue in range(1, 12):
        row_theorems.append(
            render_decide_theorem(
                f"z180_k30_projective_d3_u_pair_row_{residue:02d}_pilot_v97",
                f"z180K30ProjectiveD3UPairRowChoicesPilotV97 {residue}",
                lean_rawset_list([rawset(residue)]),
            )
        )
    row_names = ",\n    ".join(
        f"z180_k30_projective_d3_u_pair_row_{residue:02d}_pilot_v97"
        for residue in range(1, 12)
    )
    expanded_rows = " ++\n      ".join(
        f"z180K30ProjectiveD3UPairRowChoicesPilotV97 {residue}"
        for residue in range(12)
    )
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3UBase
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Source-only algebraic D3U completeness pilot

The normalized enumeration is replayed as one singleton block followed by
twelve ordered-pair rows.  No theorem evaluates the complete normalized list:
the nonempty finite row certificates contain at most six RawSets.  Source
reordering is certified over Nat indices and bridged in chunks of five and six.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3UCanonicalLowPilotV97 : List RawSet :=
  {lean_rawset_list(CANONICAL_LOW)}

def z180K30ProjectiveD3UCanonicalHighPilotV97 : List RawSet :=
  {lean_rawset_list(CANONICAL_HIGH)}

def z180K30ProjectiveD3UCanonicalPilotV97 : List RawSet :=
  z180K30ProjectiveD3UCanonicalLowPilotV97 ++
    z180K30ProjectiveD3UCanonicalHighPilotV97

def z180K30ProjectiveD3USingletonChoicesPilotV97 : List RawSet :=
  (List.range 12).flatMap fun residue =>
    normalizedProjectiveUChoicesForSelectionV88 3 [residue]

def z180K30ProjectiveD3UPairRowChoicesPilotV97
    (first : Nat) : List RawSet :=
  (List.range 12).flatMap fun second =>
    normalizedProjectiveUChoicesForSelectionV88 3 [first, second]

def z180K30ProjectiveD3ULowSecondsPilotV97 : List Nat :=
  [0, 1, 2, 3, 4, 5]

def z180K30ProjectiveD3UHighSecondsPilotV97 : List Nat :=
  [6, 7, 8, 9, 10, 11]

def z180K30ProjectiveD3UPairSegmentChoicesPilotV97
    (first : Nat) (seconds : List Nat) : List RawSet :=
  seconds.flatMap fun second =>
    normalizedProjectiveUChoicesForSelectionV88 3 [first, second]

theorem z180_k30_projective_d3_u_choices_rows_pilot_v97 :
    normalizedProjectiveUChoicesV88 3 =
      z180K30ProjectiveD3USingletonChoicesPilotV97 ++
        (List.range 12).flatMap
          z180K30ProjectiveD3UPairRowChoicesPilotV97 := by
  simp only [normalizedProjectiveUChoicesV88,
    normalizedProjectiveClassSelectionsV88,
    z180K30ProjectiveD3USingletonChoicesPilotV97,
    z180K30ProjectiveD3UPairRowChoicesPilotV97,
    List.flatMap_append, List.flatMap_map, List.flatMap_assoc,
    Function.comp_apply]

theorem z180_k30_projective_d3_u_pair_rows_expand_pilot_v97 :
    (List.range 12).flatMap
        z180K30ProjectiveD3UPairRowChoicesPilotV97 =
      {expanded_rows} := by
  rfl

theorem z180_k30_projective_d3_u_seconds_split_pilot_v97 :
    List.range 12 = z180K30ProjectiveD3ULowSecondsPilotV97 ++
      z180K30ProjectiveD3UHighSecondsPilotV97 := by
  rfl

theorem z180_k30_projective_d3_u_pair_row_zero_split_pilot_v97 :
    z180K30ProjectiveD3UPairRowChoicesPilotV97 0 =
      z180K30ProjectiveD3UPairSegmentChoicesPilotV97 0
          z180K30ProjectiveD3ULowSecondsPilotV97 ++
        z180K30ProjectiveD3UPairSegmentChoicesPilotV97 0
          z180K30ProjectiveD3UHighSecondsPilotV97 := by
  unfold z180K30ProjectiveD3UPairRowChoicesPilotV97
  unfold z180K30ProjectiveD3UPairSegmentChoicesPilotV97
  rw [z180_k30_projective_d3_u_seconds_split_pilot_v97,
    List.flatMap_append]

{render_decide_theorem(
        "z180_k30_projective_d3_u_singletons_empty_pilot_v97",
        "z180K30ProjectiveD3USingletonChoicesPilotV97",
        "[]",
    )}
{render_decide_theorem(
        "z180_k30_projective_d3_u_pair_row_zero_low_pilot_v97",
        "z180K30ProjectiveD3UPairSegmentChoicesPilotV97 0 "
        "z180K30ProjectiveD3ULowSecondsPilotV97",
        "z180K30ProjectiveD3UCanonicalLowPilotV97",
    )}
{render_decide_theorem(
        "z180_k30_projective_d3_u_pair_row_zero_high_pilot_v97",
        "z180K30ProjectiveD3UPairSegmentChoicesPilotV97 0 "
        "z180K30ProjectiveD3UHighSecondsPilotV97",
        "z180K30ProjectiveD3UCanonicalHighPilotV97",
    )}
{''.join(row_theorems)}
theorem z180_k30_projective_d3_u_choices_twice_pilot_v97 :
    normalizedProjectiveUChoicesV88 3 =
      z180K30ProjectiveD3UCanonicalPilotV97 ++
        z180K30ProjectiveD3UCanonicalPilotV97 := by
  rw [z180_k30_projective_d3_u_choices_rows_pilot_v97,
    z180_k30_projective_d3_u_pair_rows_expand_pilot_v97,
    z180_k30_projective_d3_u_pair_row_zero_split_pilot_v97,
    z180_k30_projective_d3_u_singletons_empty_pilot_v97,
    z180_k30_projective_d3_u_pair_row_zero_low_pilot_v97,
    z180_k30_projective_d3_u_pair_row_zero_high_pilot_v97,
    {row_names}]
  rfl

def z180K30ProjectiveD3UCanonicalIndexLowPilotV97 : List Nat :=
  {low_indices}

def z180K30ProjectiveD3UCanonicalIndexHighPilotV97 : List Nat :=
  {high_indices}

def z180K30ProjectiveD3UCanonicalIndicesPilotV97 : List Nat :=
  z180K30ProjectiveD3UCanonicalIndexLowPilotV97 ++
    z180K30ProjectiveD3UCanonicalIndexHighPilotV97

def z180K30ProjectiveD3USourceAtPilotV97 (index : Nat) : RawSet :=
  z180K30ProjectiveCompletenessV97D3USourceGrouped.getD index []

def z180K30ProjectiveD3UCanonicalIndexedPilotV97 : List RawSet :=
  z180K30ProjectiveD3UCanonicalIndicesPilotV97.map
    z180K30ProjectiveD3USourceAtPilotV97

def z180K30ProjectiveD3UCanonicalSourceLowPilotV97 : List RawSet :=
  z180K30ProjectiveD3UCanonicalIndexLowPilotV97.map
    z180K30ProjectiveD3USourceAtPilotV97

def z180K30ProjectiveD3UCanonicalSourceHighPilotV97 : List RawSet :=
  z180K30ProjectiveD3UCanonicalIndexHighPilotV97.map
    z180K30ProjectiveD3USourceAtPilotV97

theorem z180_k30_projective_d3_u_source_length_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3USourceGrouped.length = 11 := by
  rfl

private theorem z180_k30_projective_d3_u_map_range_getD_eq_self_pilot_v97
    {{alpha : Type}} (values : List alpha) (fallback : alpha) :
    (List.range values.length).map (fun index =>
      values.getD index fallback) = values := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem values fallback hright

theorem z180_k30_projective_d3_u_source_range_pilot_v97 :
    (List.range 11).map z180K30ProjectiveD3USourceAtPilotV97 =
      z180K30ProjectiveCompletenessV97D3USourceGrouped := by
  rw [← z180_k30_projective_d3_u_source_length_pilot_v97]
  exact z180_k30_projective_d3_u_map_range_getD_eq_self_pilot_v97
    z180K30ProjectiveCompletenessV97D3USourceGrouped []

theorem z180_k30_projective_d3_u_index_perm_pilot_v97 :
    (List.range 11).Perm z180K30ProjectiveD3UCanonicalIndicesPilotV97 := by
  decide

theorem z180_k30_projective_d3_u_source_perm_indexed_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3USourceGrouped.Perm
      z180K30ProjectiveD3UCanonicalIndexedPilotV97 := by
  have h := z180_k30_projective_d3_u_index_perm_pilot_v97.map
    z180K30ProjectiveD3USourceAtPilotV97
  rw [z180_k30_projective_d3_u_source_range_pilot_v97] at h
  exact h

theorem z180_k30_projective_d3_u_indexed_chunks_pilot_v97 :
    z180K30ProjectiveD3UCanonicalIndexedPilotV97 =
      z180K30ProjectiveD3UCanonicalSourceLowPilotV97 ++
        z180K30ProjectiveD3UCanonicalSourceHighPilotV97 := by
  unfold z180K30ProjectiveD3UCanonicalIndexedPilotV97
  unfold z180K30ProjectiveD3UCanonicalIndicesPilotV97
  unfold z180K30ProjectiveD3UCanonicalSourceLowPilotV97
  unfold z180K30ProjectiveD3UCanonicalSourceHighPilotV97
  rw [List.map_append]

{render_decide_theorem(
        "z180_k30_projective_d3_u_source_low_bridge_pilot_v97",
        "z180K30ProjectiveD3UCanonicalSourceLowPilotV97",
        "z180K30ProjectiveD3UCanonicalLowPilotV97",
    )}
{render_decide_theorem(
        "z180_k30_projective_d3_u_source_high_bridge_pilot_v97",
        "z180K30ProjectiveD3UCanonicalSourceHighPilotV97",
        "z180K30ProjectiveD3UCanonicalHighPilotV97",
    )}
theorem z180_k30_projective_d3_u_indexed_canonical_pilot_v97 :
    z180K30ProjectiveD3UCanonicalIndexedPilotV97 =
      z180K30ProjectiveD3UCanonicalPilotV97 := by
  rw [z180_k30_projective_d3_u_indexed_chunks_pilot_v97,
    z180_k30_projective_d3_u_source_low_bridge_pilot_v97,
    z180_k30_projective_d3_u_source_high_bridge_pilot_v97]
  rfl

theorem z180_k30_projective_d3_u_source_perm_canonical_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3USourceGrouped.Perm
      z180K30ProjectiveD3UCanonicalPilotV97 := by
  exact z180_k30_projective_d3_u_source_perm_indexed_pilot_v97.trans
    (List.Perm.of_eq z180_k30_projective_d3_u_indexed_canonical_pilot_v97)

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d3_u_canonical_low_nodup_pilot_v97 :
    z180K30ProjectiveD3UCanonicalLowPilotV97.Nodup := by
  decide

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d3_u_canonical_high_nodup_pilot_v97 :
    z180K30ProjectiveD3UCanonicalHighPilotV97.Nodup := by
  decide

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d3_u_canonical_chunks_disjoint_pilot_v97 :
    z180K30ProjectiveD3UCanonicalLowPilotV97.Disjoint
      z180K30ProjectiveD3UCanonicalHighPilotV97 := by
  decide

theorem z180_k30_projective_d3_u_canonical_nodup_pilot_v97 :
    z180K30ProjectiveD3UCanonicalPilotV97.Nodup := by
  unfold z180K30ProjectiveD3UCanonicalPilotV97
  exact z180_k30_projective_d3_u_canonical_low_nodup_pilot_v97.append
    z180_k30_projective_d3_u_canonical_high_nodup_pilot_v97
    z180_k30_projective_d3_u_canonical_chunks_disjoint_pilot_v97

private theorem z180_k30_projective_d3_u_erase_append_self_pilot_v97
    {{alpha : Type}} [BEq alpha] [LawfulBEq alpha] :
    ∀ {{values : List alpha}}, values.Nodup →
      (values ++ values).eraseDups = values
  | [], _ => rfl
  | head :: tail, hnodup => by
      have hhead : head ∉ tail := (List.nodup_cons.mp hnodup).1
      have htail : tail.Nodup := (List.nodup_cons.mp hnodup).2
      have hfilterTail :
          tail.filter (fun item => !item == head) = tail := by
        apply List.filter_eq_self.mpr
        intro item hitem
        have hne : item ≠ head := by
          intro hequal
          exact hhead (hequal ▸ hitem)
        simp [hne]
      have hfilterAppend :
          (tail ++ head :: tail).filter (fun item => !item == head) =
            tail ++ tail := by
        rw [List.filter_append, hfilterTail]
        simp [hfilterTail]
      rw [List.eraseDups_cons, hfilterAppend,
        z180_k30_projective_d3_u_erase_append_self_pilot_v97 htail]

theorem z180_k30_projective_d3_u_unique_canonical_pilot_v97 :
    normalizedProjectiveUniqueUChoicesV89 3 =
      z180K30ProjectiveD3UCanonicalPilotV97 := by
  unfold normalizedProjectiveUniqueUChoicesV89
  rw [z180_k30_projective_d3_u_choices_twice_pilot_v97]
  exact z180_k30_projective_d3_u_erase_append_self_pilot_v97
    z180_k30_projective_d3_u_canonical_nodup_pilot_v97

theorem {FINAL_THEOREM} :
    z180K30ProjectiveCompletenessV97D3USourceGrouped.Perm
      (normalizedProjectiveUniqueUChoicesV89 3) := by
  rw [z180_k30_projective_d3_u_unique_canonical_pilot_v97]
  exact z180_k30_projective_d3_u_source_perm_canonical_pilot_v97

#print axioms z180_k30_projective_d3_u_choices_twice_pilot_v97
#print axioms {FINAL_THEOREM}

end Fuglede.Z180K30ExceptionalRawV2
"""


def build() -> tuple[str, dict[str, object]]:
    names, definitions, member_paths = parse_source()
    source = [definitions[name] for name in names]
    if sorted(source) != sorted(CANONICAL):
        raise RuntimeError("D3U SourceGrouped is not exactly the canonical family")
    indices = [source.index(value) for value in CANONICAL]
    if indices != [0, 4, 6, 8, 1, 10, 2, 9, 7, 5, 3]:
        raise RuntimeError(f"unexpected D3U canonical source indices: {indices}")
    if sorted(indices) != list(range(11)):
        raise RuntimeError("D3U canonical source indices are not a permutation")

    singleton, rows, choices = normalized_choices()
    if singleton:
        raise RuntimeError("D3U singleton selections unexpectedly produced choices")
    if rows[0] != CANONICAL:
        raise RuntimeError("D3U forward zero row is not canonical")
    for residue in range(1, 12):
        if rows[residue] != [rawset(residue)]:
            raise RuntimeError(f"D3U reverse row {residue} is unexpected")
    if choices != CANONICAL + CANONICAL:
        raise RuntimeError("D3U normalized choices are not canonical twice")
    if stable_dedup(choices) != CANONICAL:
        raise RuntimeError("D3U stable dedup is not canonical")

    leaf_targets = [0, 5, 6] + [1] * 11
    if max(leaf_targets) > 6:
        raise RuntimeError("a D3U finite filter leaf exceeds six RawSets")

    text = render_module(indices)
    forbidden = re.compile(r"\b(native_decide|unsafe|sorry|axiom|choose|drop|take)\b")
    hits = forbidden.findall(text)
    if hits:
        raise RuntimeError(f"forbidden Lean tokens: {hits}")
    if "normalizedProjectiveUChoicesV88 3" not in text:
        raise RuntimeError("missing honest bridge to normalizedProjectiveUChoicesV88 3")
    if "normalizedProjectiveUniqueUChoicesV89 3" not in text:
        raise RuntimeError("missing honest bridge to normalizedProjectiveUniqueUChoicesV89 3")
    if f"theorem {FINAL_THEOREM}" not in text:
        raise RuntimeError("missing required final theorem")

    active_files = [
        ROOT / "Fuglede.lean",
        ROOT / "Fuglede/Z180K30ExceptionalProjectiveProfileDataV97D3.lean",
    ]
    for active in active_files:
        if active.exists() and MODULE in active.read_text(encoding="utf-8"):
            raise RuntimeError(f"isolated pilot is already imported by {active.relative_to(ROOT)}")

    dependencies = [BASE, *member_paths]
    manifest: dict[str, object] = {
        "schema": 1,
        "module": MODULE,
        "output": str(OUT.relative_to(ROOT)).replace("\\", "/"),
        "final_theorem": FINAL_THEOREM,
        "source_count": len(source),
        "canonical_count": len(CANONICAL),
        "normalized_choice_count_before_dedup": len(choices),
        "normalized_unique_count": len(stable_dedup(choices)),
        "canonical_source_indices": indices,
        "finite_filter_leaf_target_sizes": leaf_targets,
        "max_finite_filter_leaf_target_size": max(leaf_targets),
        "source_bridge_chunk_sizes": [len(indices[:5]), len(indices[5:])],
        "source_grouped_values": [list(value) for value in source],
        "canonical_values": [list(value) for value in CANONICAL],
        "dependency_sha256": {
            str(path.relative_to(ROOT)).replace("\\", "/"): sha256_file(path)
            for path in dependencies
        },
        "output_sha256": sha256_bytes(text.encode("utf-8")),
        "forbidden_tokens": [
            "native_decide",
            "unsafe",
            "sorry",
            "axiom",
            "choose",
            "drop",
            "take",
        ],
        "lean_was_run": False,
    }
    return text, manifest


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    text, manifest = build()
    manifest_text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(text, encoding="utf-8", newline="\n")
        MANIFEST.write_text(manifest_text, encoding="utf-8", newline="\n")
        print(f"wrote {OUT.relative_to(ROOT)}")
        print(f"wrote {MANIFEST.relative_to(ROOT)}")
        return

    failures: list[str] = []
    if not OUT.exists() or OUT.read_text(encoding="utf-8") != text:
        failures.append(str(OUT.relative_to(ROOT)))
    if not MANIFEST.exists() or MANIFEST.read_text(encoding="utf-8") != manifest_text:
        failures.append(str(MANIFEST.relative_to(ROOT)))
    if failures:
        raise SystemExit("stale generated files: " + ", ".join(failures))
    print("D3U algebraic pilot source and manifest are current")


if __name__ == "__main__":
    main()
