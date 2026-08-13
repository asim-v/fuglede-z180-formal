#!/usr/bin/env python3
"""Generate the isolated D3-V canonical-enumeration equality pilot.

This pilot contains exactly one computational bridge: an explicit canonical
list of the already certified V-profile member constants is compared with the
normalized V89 enumeration.  It neither edits nor participates in the active
V97 manifest.
"""

from __future__ import annotations

import hashlib
import importlib.util
from collections import OrderedDict
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_DIR = SCRIPT_DIR.parent
LEAN_DIR = REPO_DIR / "fuglede_lean" / "Fuglede"
ACTIVE_GENERATOR = SCRIPT_DIR / "generate_z180_k30_projective_profile_audit_v97.py"
OUTPUT = (
    LEAN_DIR /
    "Z180K30ExceptionalProjectiveProfileD3VCanonicalEqualityPilotV97.lean"
)
INDEX_OUTPUT = (
    LEAN_DIR /
    "Z180K30ExceptionalProjectiveProfileD3VIndexPermPilotV97.lean"
)
INDEX_BASE_OUTPUT = (
    LEAN_DIR /
    "Z180K30ExceptionalProjectiveProfileD3VIndexPermBasePilotV97.lean"
)
INDEX_BUCKET_COUNT = 64
ALGEBRAIC_OUTPUT = (
    LEAN_DIR /
    "Z180K30ExceptionalProjectiveProfileD3VAlgebraicEnumerationPilotV97.lean"
)


def load_generator():
    spec = importlib.util.spec_from_file_location("profile_v97_generator", ACTIVE_GENERATOR)
    if spec is None or spec.loader is None:
        raise SystemExit("FAIL CLOSED: cannot load active V97 generator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def wrapped_list(names: list[str], width: int = 92) -> str:
    lines: list[str] = []
    current = "  ["
    for index, name in enumerate(names):
        token = name + ("," if index + 1 < len(names) else "")
        if len(current) + len(token) + 1 > width and current != "  [":
            lines.append(current)
            current = "   " + token
        else:
            current += ("" if current.endswith("[") else " ") + token
    lines.append(current + "]")
    return "\n".join(lines)


def lean_sublists_len(length: int, values: list[int]) -> list[tuple[int, ...]]:
    """Mirror Mathlib's tail-first `List.sublistsLen` enumeration exactly."""
    if length == 0:
        return [()]
    if not values:
        return []
    head, tail = values[0], values[1:]
    return (
        lean_sublists_len(length, tail) +
        [(head, *suffix) for suffix in lean_sublists_len(length - 1, tail)]
    )


def expected_source() -> str:
    generator = load_generator()
    # `normalizedProjectiveUniqueVChoicesV89` is not Python's lexicographic
    # combinations order. Mathlib enumerates sublists tail-first; all these
    # candidates are distinct, so `eraseDups` preserves that exact order.
    base = [value for value in range(36) if value % 3 == 0]
    canonical = [
        values for values in lean_sublists_len(6, base) if 0 in values
    ]
    _, canonical_set = generator.normalized_choices(3)
    if set(canonical) != set(canonical_set):
        raise SystemExit("FAIL CLOSED: exact D3-V Lean enumeration set drift")
    # Member names were assigned by the active generator's own (itertools)
    # grouping order.  Build the value-to-name map in that original order,
    # then project the names into Lean's independent tail-first order.
    groups: OrderedDict[tuple[int, ...], list[tuple[int, ...]]] = OrderedDict()
    for values in canonical_set:
        groups.setdefault(generator.v_profile(3, values), []).append(values)
    location: dict[tuple[int, ...], str] = {}
    for profile_index, members in enumerate(groups.values()):
        for member_index, values in enumerate(members):
            location[values] = generator.v_member_name(
                3, profile_index, member_index
            )
    names = [location[values] for values in canonical]
    if len(names) != 462 or len(set(names)) != 462:
        raise SystemExit("FAIL CLOSED: D3-V canonical pilot census drift")
    imports = "\n".join(
        f"import Fuglede.{generator.member_stem(3, shard)}"
        for shard in range(24)
    )
    return f"""{imports}

/-!
Isolated pilot for the sole computational bridge in the structural D3-V
completeness replay. The explicit list is in normalized canonical order.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCanonicalNamedPilotV97 : List RawSet :=
{wrapped_list(names)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_canonical_named_pilot_v97 :
    z180K30ProjectiveD3VCanonicalNamedPilotV97 =
      normalizedProjectiveUniqueVChoicesV89 3 := by
  decide

#print axioms z180_k30_projective_d3_v_canonical_named_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
"""


def canonical_index_permutation() -> list[int]:
    generator = load_generator()
    base = [value for value in range(36) if value % 3 == 0]
    canonical = [
        values for values in lean_sublists_len(6, base) if 0 in values
    ]
    _, active = generator.normalized_choices(3)
    groups: OrderedDict[tuple[int, ...], list[tuple[int, ...]]] = OrderedDict()
    for values in active:
        groups.setdefault(generator.v_profile(3, values), []).append(values)
    source_values: list[tuple[int, ...]] = []
    for members in groups.values():
        source_values.extend(members)
    source_index = {values: index for index, values in enumerate(source_values)}
    indices = [source_index[values] for values in canonical]
    if (
        len(indices) != 462 or
        sorted(indices) != list(range(462)) or
        [source_values[index] for index in indices] != canonical
    ):
        raise SystemExit("FAIL CLOSED: D3-V canonical index permutation drift")
    return indices


def expected_index_base_source() -> str:
    indices = canonical_index_permutation()
    index_literals = wrapped_list([str(index) for index in indices])
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessV97D3VBase
import Mathlib.Data.List.GetD

/-!
RawSet-opaque source-permutation pilot base.  All permutation certificates
below contain only `Nat` indices.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveD3VCanonicalIndicesPilotV97 : List Nat :=
{index_literals}

set_option maxRecDepth 100000 in
theorem z180_k30_projective_d3_v_source_length_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3VSourceGrouped.length = 462 := by
  rfl

def z180K30ProjectiveD3VIndexPredicatePilotV97
    (bucket index : Nat) : Bool :=
  index % {INDEX_BUCKET_COUNT} == bucket

def z180K30ProjectiveD3VSourceAtPilotV97 (index : Nat) : RawSet :=
  z180K30ProjectiveCompletenessV97D3VSourceGrouped.getD index []

def z180K30ProjectiveD3VCanonicalIndexedPilotV97 : List RawSet :=
  z180K30ProjectiveD3VCanonicalIndicesPilotV97.map
    z180K30ProjectiveD3VSourceAtPilotV97

end Fuglede.Z180K30ExceptionalRawV2
"""


def index_bucket_stem(bucket: int) -> str:
    return (
        "Z180K30ExceptionalProjectiveProfileD3VIndexPerm"
        f"B{bucket:02d}PilotV97"
    )


def index_bucket_theorem(bucket: int) -> str:
    return f"z180_k30_projective_d3_v_index_bucket_b{bucket:02d}_pilot_v97"


def expected_index_bucket_source(bucket: int) -> str:
    source_size = sum(
        value % INDEX_BUCKET_COUNT == bucket for value in range(462)
    )
    target_size = sum(
        value % INDEX_BUCKET_COUNT == bucket
        for value in canonical_index_permutation()
    )
    if source_size != target_size or source_size > 8:
        raise SystemExit("FAIL CLOSED: D3-V Nat index bucket census drift")
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermBasePilotV97

/-! Nat-only index bucket {bucket}, size {source_size}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem {index_bucket_theorem(bucket)} :
    ((List.range 462).filter
      (z180K30ProjectiveD3VIndexPredicatePilotV97 {bucket})).Perm
      (z180K30ProjectiveD3VCanonicalIndicesPilotV97.filter
        (z180K30ProjectiveD3VIndexPredicatePilotV97 {bucket})) := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def expected_index_source() -> str:
    imports = "\n".join(
        f"import Fuglede.{index_bucket_stem(bucket)}"
        for bucket in range(INDEX_BUCKET_COUNT)
    )
    cases = "\n".join(
        f"      | exact {index_bucket_theorem(bucket)}"
        for bucket in range(INDEX_BUCKET_COUNT)
    )
    return f"""{imports}

/-! Structural aggregate of 64 Nat-only index buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_d3_v_canonical_indices_perm_pilot_v97 :
    (List.range 462).Perm
      z180K30ProjectiveD3VCanonicalIndicesPilotV97 := by
  have hBuckets :
      ((List.range {INDEX_BUCKET_COUNT}).flatMap fun bucket =>
        (List.range 462).filter
          (z180K30ProjectiveD3VIndexPredicatePilotV97 bucket)).Perm
      ((List.range {INDEX_BUCKET_COUNT}).flatMap fun bucket =>
        z180K30ProjectiveD3VCanonicalIndicesPilotV97.filter
          (z180K30ProjectiveD3VIndexPredicatePilotV97 bucket)) := by
    apply List.Perm.flatMap_left
    intro bucket hbucket
    simp only [List.mem_range] at hbucket
    interval_cases bucket <;> first
{cases}
  have hSource := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) {INDEX_BUCKET_COUNT} (by decide)
    (List.range 462)
  have hTarget := projectiveProfileRangeFlatMapFilterModPermV97
    (fun value : Nat => value) {INDEX_BUCKET_COUNT} (by decide)
    z180K30ProjectiveD3VCanonicalIndicesPilotV97
  exact hSource.symm.trans (hBuckets.trans hTarget)

private theorem map_range_getD_eq_self_pilot_v97
    {{alpha : Type}} (values : List alpha) (fallback : alpha) :
    (List.range values.length).map (fun index =>
      values.getD index fallback) = values := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem values fallback hright

theorem z180_k30_projective_d3_v_source_range_pilot_v97 :
    (List.range 462).map z180K30ProjectiveD3VSourceAtPilotV97 =
      z180K30ProjectiveCompletenessV97D3VSourceGrouped := by
  rw [← z180_k30_projective_d3_v_source_length_pilot_v97]
  exact map_range_getD_eq_self_pilot_v97
    z180K30ProjectiveCompletenessV97D3VSourceGrouped []

theorem z180_k30_projective_d3_v_source_perm_indexed_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3VSourceGrouped.Perm
      z180K30ProjectiveD3VCanonicalIndexedPilotV97 := by
  have h := z180_k30_projective_d3_v_canonical_indices_perm_pilot_v97.map
    z180K30ProjectiveD3VSourceAtPilotV97
  rw [z180_k30_projective_d3_v_source_range_pilot_v97] at h
  exact h

#print axioms z180_k30_projective_d3_v_canonical_indices_perm_pilot_v97
#print axioms z180_k30_projective_d3_v_source_perm_indexed_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
"""


def expected_algebraic_source() -> str:
    return """import Fuglede.Z180K30ExceptionalProjectiveProfileD3VIndexPermPilotV97
import Mathlib.Data.List.Sublists

/-!
Algebraic second half of the D3-V completeness pilot.  It removes the
deduplication and zero-membership filter by generic list lemmas, leaving the
tail-first `sublistsLen` enumeration.  The sole definitional bridge evaluates
only list constructors and indices: it performs no `BEq`, filtering, or
permutation search over `RawSet` values.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

private theorem eraseDups_eq_self_of_nodup_v97
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    ∀ {values : List alpha}, values.Nodup → values.eraseDups = values
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
        eraseDups_eq_self_of_nodup_v97 htail]

private theorem filter_sublists_without_point_v97
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

private theorem filter_cons_point_v97
    {alpha : Type} [DecidableEq alpha]
    (point : alpha) (values : List (List alpha)) :
    (values.map (List.cons point)).filter
      (fun set => decide (point ∈ set)) =
        values.map (List.cons point) := by
  apply List.filter_eq_self.mpr
  intro set hset
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp hset
  exact decide_eq_true (List.mem_cons_self)

def z180K30ProjectiveD3VPositiveTailPilotV97 : List RawPoint :=
  [3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33]

theorem z180_k30_projective_d3_v_base_pilot_v97 :
    baseForDivisor 3 =
      (0 : RawPoint) :: z180K30ProjectiveD3VPositiveTailPilotV97 := by
  decide

theorem z180_k30_projective_d3_v_choices_sublists_pilot_v97 :
    normalizedProjectiveVChoicesV88 3 =
      (List.sublistsLen 5 z180K30ProjectiveD3VPositiveTailPilotV97).map
        (List.cons (0 : RawPoint)) := by
  unfold normalizedProjectiveVChoicesV88
  rw [z180_k30_projective_d3_v_base_pilot_v97,
    List.sublistsLen_succ_cons, List.filter_append]
  rw [filter_sublists_without_point_v97
    (0 : RawPoint) z180K30ProjectiveD3VPositiveTailPilotV97 6 (by decide)]
  rw [List.nil_append]
  exact filter_cons_point_v97 (0 : RawPoint)
    (List.sublistsLen 5 z180K30ProjectiveD3VPositiveTailPilotV97)

theorem z180_k30_projective_d3_v_unique_sublists_pilot_v97 :
    normalizedProjectiveUniqueVChoicesV89 3 =
      (List.sublistsLen 5 z180K30ProjectiveD3VPositiveTailPilotV97).map
        (List.cons (0 : RawPoint)) := by
  unfold normalizedProjectiveUniqueVChoicesV89
  rw [z180_k30_projective_d3_v_choices_sublists_pilot_v97]
  apply eraseDups_eq_self_of_nodup_v97
  apply List.Nodup.map
  · intro left right hequal
    simpa using hequal
  · apply List.nodup_sublistsLen
    decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem z180_k30_projective_d3_v_indexed_sublists_pilot_v97 :
    z180K30ProjectiveD3VCanonicalIndexedPilotV97 =
      (List.sublistsLen 5 z180K30ProjectiveD3VPositiveTailPilotV97).map
        (List.cons (0 : RawPoint)) := by
  rfl

theorem z180_k30_projective_d3_v_complete_algebraic_pilot_v97 :
    z180K30ProjectiveCompletenessV97D3VSourceGrouped.Perm
      (normalizedProjectiveUniqueVChoicesV89 3) := by
  exact z180_k30_projective_d3_v_source_perm_indexed_pilot_v97.trans
    (List.Perm.of_eq
      (z180_k30_projective_d3_v_indexed_sublists_pilot_v97.trans
        z180_k30_projective_d3_v_unique_sublists_pilot_v97.symm))

#print axioms z180_k30_projective_d3_v_unique_sublists_pilot_v97
#print axioms z180_k30_projective_d3_v_indexed_sublists_pilot_v97
#print axioms z180_k30_projective_d3_v_complete_algebraic_pilot_v97

end Fuglede.Z180K30ExceptionalRawV2
"""


def main() -> None:
    source = expected_source()
    index_base_source = expected_index_base_source()
    index_source = expected_index_source()
    algebraic_source = expected_algebraic_source()
    outputs = [
        (OUTPUT, source, "canonical equality"),
        (INDEX_BASE_OUTPUT, index_base_source, "Nat-index base"),
    ]
    outputs.extend(
        (
            LEAN_DIR / f"{index_bucket_stem(bucket)}.lean",
            expected_index_bucket_source(bucket),
            f"Nat-index bucket {bucket}",
        )
        for bucket in range(INDEX_BUCKET_COUNT)
    )
    outputs.extend([
        (INDEX_OUTPUT, index_source, "Nat-index permutation aggregate"),
        (ALGEBRAIC_OUTPUT, algebraic_source, "algebraic enumeration"),
    ])
    for path, expected, label in outputs:
        digest = hashlib.sha256(expected.encode()).hexdigest().upper()
        if path.exists() and path.read_text(encoding="utf-8") == expected:
            print(f"PASS D3-V {label} pilot sha256={digest}")
        else:
            path.write_text(expected, encoding="utf-8", newline="\n")
            print(f"WROTE D3-V {label} pilot sha256={digest}")


if __name__ == "__main__":
    main()
