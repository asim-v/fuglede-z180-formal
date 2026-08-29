#!/usr/bin/env python3
"""Generate the isolated histogram/profile projective audit V97.

The generator independently reconstructs the normalized candidate marginals,
groups them by exact coefficient-zero profiles, authenticates every positive
pair against its precise V87 source location, and emits a fail-closed Lean DAG.
It never reads or writes the generated V89 tree or its replay state.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from collections import OrderedDict
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_DIR = SCRIPT_DIR.parent
LEAN_DIR = REPO_DIR / "fuglede_lean" / "Fuglede"
CATALOGUE_PATH = SCRIPT_DIR / "z180_k30_exceptional_literal_pairs.json"
MANIFEST_PATH = SCRIPT_DIR / "z180_k30_projective_profile_audit_v97.manifest.json"
D4U_CHILD_MANIFEST = (
    SCRIPT_DIR / "z180_k30_projective_profile_d4u_algebraic_v97.manifest.json"
)
D6_ALG_CHILD_MANIFEST = (
    REPO_DIR / "fuglede_lean/generated/z180_k30_d6_algebraic_v97.manifest.json"
)
D6_VALID_CHILD_MANIFEST = (
    REPO_DIR / "fuglede_lean/generated/z180_k30_d6_u_validity_v97.manifest.json"
)
D6_ALG_STATE = REPO_DIR / "audit/z180_k30_projective_d6_algebraic_v97/state.json"
D6_VALID_STATE = REPO_DIR / "audit/z180_k30_projective_d6_u_validity_v97/state.json"
D3U_GENERATOR = (
    REPO_DIR / "fuglede_lean/scripts/generate_z180_k30_d3u_algebraic_v97.py"
)
D3V_GENERATOR = (
    SCRIPT_DIR / "generate_z180_k30_projective_profile_d3v_canonical_pilot_v97.py"
)
D4V_GENERATOR = (
    SCRIPT_DIR / "generate_z180_k30_projective_profile_d4v_algebraic_pilot_v97.py"
)

CORE_SOURCES = [
    "Z180K30ExceptionalProjectiveHistogramCoreV97.lean",
    "Z180K30ExceptionalProjectiveProfileCoreV97.lean",
    "Z180K30ExceptionalProjectiveProfileBridgeV97.lean",
    "Z180K30ExceptionalProjectiveScalarNormalizationAdapterV97.lean",
]
COMPLETENESS_CORE_SOURCE = (
    "Z180K30ExceptionalProjectiveProfileCompletenessPartitionCoreV97.lean"
)
MEMBER_SHARD_SIZE = 20
SUPPORTED_DIVISORS = (3, 4, 6)
COMPLETENESS_BUCKET_COUNTS = {
    3: {"U": 2, "V": 68},
    4: {"U": 26, "V": 7},
    6: {"U": 479, "V": 1},
}
EXPECTED_POSITIVE_SHA256 = (
    "D46CC8AF89FF20F306E5F1E0F7E444ED493C0971FC501128733C9ED7E4867958"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def module_from_child_source(source: str) -> str:
    source = source.replace("\\", "/")
    if source.startswith("fuglede_lean/"):
        source = source[len("fuglede_lean/"):]
    if not source.startswith("Fuglede/") or not source.endswith(".lean"):
        raise SystemExit(f"FAIL CLOSED: non-Lean child output path {source}")
    return (
        "Fuglede."
        + source[len("Fuglede/"):-len(".lean")].replace("/", ".")
    )


def source_for_module(module: str) -> Path:
    prefix = "Fuglede."
    if not module.startswith(prefix):
        raise SystemExit(f"FAIL CLOSED: non-Fuglede module {module}")
    return LEAN_DIR / (module[len(prefix):].replace(".", "/") + ".lean")


def authenticate_child_manifest(
    path: Path,
    base: Path,
    schema: str,
    cyclic_input_exclusions: set[str],
    require_compile_stages: bool,
) -> tuple[dict, dict, list[str]]:
    raw = path.read_bytes()
    try:
        manifest = json.loads(raw.decode("utf-8-sig"))
    except Exception as exc:
        raise SystemExit(
            f"FAIL CLOSED: unreadable child manifest {path}: {exc}"
        )
    if manifest.get("schema") != schema:
        raise SystemExit(f"FAIL CLOSED: child schema drift {path}")
    generator_relative = str(manifest.get("generator", ""))
    generator_path = base / generator_relative
    if (
        not generator_path.is_file()
        or sha256_bytes(generator_path.read_bytes())
        != str(manifest.get("generator_sha256", "")).upper()
    ):
        raise SystemExit(f"FAIL CLOSED: child generator drift {path}")
    inputs = manifest.get("inputs")
    outputs = manifest.get("outputs")
    if not isinstance(inputs, dict) or not isinstance(outputs, dict):
        raise SystemExit(f"FAIL CLOSED: child input/output map absent {path}")
    if not cyclic_input_exclusions <= set(inputs):
        raise SystemExit(f"FAIL CLOSED: cyclic exclusion absent from {path}")
    for relative, expected_sha in inputs.items():
        if relative in cyclic_input_exclusions:
            continue
        input_path = base / relative
        if (
            not input_path.is_file()
            or sha256_bytes(input_path.read_bytes()) != str(expected_sha).upper()
        ):
            raise SystemExit(f"FAIL CLOSED: child input drift {relative}")
    output_hashes: dict[str, str] = {}
    for relative, expected_sha in outputs.items():
        output_path = base / relative
        actual_sha = (
            sha256_bytes(output_path.read_bytes()) if output_path.is_file() else ""
        )
        if actual_sha != str(expected_sha).upper():
            raise SystemExit(f"FAIL CLOSED: child output drift {relative}")
        output_hashes[relative] = actual_sha
    staged_modules: list[str] = []
    if require_compile_stages:
        stages = manifest.get("compile_stages")
        if not isinstance(stages, list):
            raise SystemExit(f"FAIL CLOSED: child stages absent {path}")
        staged_sources = [
            str(source) for stage in stages for source in stage["files"]
        ]
        if (
            len(staged_sources) != len(set(staged_sources))
            or set(staged_sources) != set(outputs)
        ):
            raise SystemExit(f"FAIL CLOSED: child stages/output mismatch {path}")
        staged_modules = [
            module_from_child_source(source) for source in staged_sources
        ]
    output_encoding = json.dumps(
        output_hashes, sort_keys=True, separators=(",", ":")
    )
    record = {
        "path": str(path.relative_to(REPO_DIR)).replace("\\", "/"),
        "sha256": sha256_bytes(raw),
        "schema": schema,
        "generator": str(generator_path.relative_to(REPO_DIR)).replace("\\", "/"),
        "generatorSha256": sha256_bytes(generator_path.read_bytes()),
        "cyclicInputExclusions": sorted(cyclic_input_exclusions),
        "authenticatedInputCount": len(inputs) - len(cyclic_input_exclusions),
        "outputCount": len(outputs),
        "outputsCanonicalSha256": sha256_text(output_encoding),
    }
    return manifest, record, staged_modules


def topo_sort_modules(output_map: dict[str, str]) -> list[str]:
    modules = {module_from_child_source(relative) for relative in output_map}
    imports = re.compile(r"^import (Fuglede\.\S+)$", re.M)
    permanent: set[str] = set()
    temporary: set[str] = set()
    ordered: list[str] = []

    def visit(module: str) -> None:
        if module in permanent:
            return
        if module in temporary:
            raise SystemExit(f"FAIL CLOSED: external import cycle at {module}")
        temporary.add(module)
        source = source_for_module(module).read_text(encoding="utf-8")
        for dependency in imports.findall(source):
            if dependency in modules:
                visit(dependency)
        temporary.remove(module)
        permanent.add(module)
        ordered.append(module)

    for module in sorted(modules):
        visit(module)
    if len(ordered) != len(modules):
        raise SystemExit("FAIL CLOSED: external topological closure mismatch")
    return ordered


def authenticate_sealed_state(
    path: Path, schema: str, manifest_sha: str, modules: list[str]
) -> dict:
    raw = path.read_bytes()
    state = json.loads(raw.decode("utf-8-sig"))
    completed = [str(module) for module in state.get("completedModules", [])]
    if (
        state.get("schema") != schema
        or str(state.get("manifestSha256", "")).upper() != manifest_sha.upper()
        or len(completed) != len(set(completed))
        or set(completed) != set(modules)
    ):
        raise SystemExit(f"FAIL CLOSED: child sealed state mismatch {path}")
    return {
        "path": str(path.relative_to(REPO_DIR)).replace("\\", "/"),
        "sha256": sha256_bytes(raw),
        "schema": schema,
        "completedModuleCount": len(completed),
    }


def lean_nat_list(values) -> str:
    return "[" + ", ".join(str(int(value)) for value in values) + "]"


def lean_int_list(values) -> str:
    return "[" + ", ".join(str(int(value)) for value in values) + "]"


def lean_set(values) -> str:
    return lean_nat_list(values)


def chunks(values: list, size: int) -> list[list]:
    return [values[index:index + size] for index in range(0, len(values), size)]


def normalized_choice_occurrences(divisor: int):
    base = [value for value in range(36) if value % divisor == 0]
    v_choices = [
        tuple(values)
        for values in itertools.combinations(base, 6)
        if 0 in values
    ]
    modulus = 36 // divisor
    selections = [[r] for r in range(modulus)] + [
        [first, second]
        for first in range(modulus)
        for second in range(modulus)
    ]
    u_occurrences: list[tuple[int, ...]] = []
    for selection in selections:
        domain = [
            value for value in range(36)
            if any(value % modulus == residue for residue in selection)
        ]
        u_occurrences.extend(
            tuple(values)
            for values in itertools.combinations(domain, 6)
            if 0 in values
        )
    return u_occurrences, v_choices


def normalized_choices(divisor: int):
    u_occurrences, v_occurrences = normalized_choice_occurrences(divisor)
    return list(dict.fromkeys(u_occurrences)), list(dict.fromkeys(v_occurrences))


def ordered_differences(values: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        (left + 36 - right) % 36
        for left in values
        for right in values
    )


def zeta_scalar_zero(exponent: int) -> int:
    residue = exponent % 36
    if residue in (0, 30):
        return 1
    if residue in (12, 18):
        return -1
    return 0


def u_profile(divisor: int, values: tuple[int, ...]) -> tuple[int, ...]:
    differences = ordered_differences(values)
    return tuple(
        sum(zeta_scalar_zero(outer * projective_difference)
            for outer in differences)
        if projective_difference % divisor == 0 else 0
        for projective_difference in range(36)
    )


def v_profile(_divisor: int, values: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sorted(ordered_differences(values)))


def profile_dot(u_values: tuple[int, ...], v_values: tuple[int, ...]) -> int:
    return sum(u_values[difference] for difference in v_values)


def scalar_direct(left: tuple[int, ...], right: tuple[int, ...]) -> int:
    return sum(
        zeta_scalar_zero(outer * inner)
        for outer in ordered_differences(left)
        for inner in ordered_differences(right)
    )


def normalized_raw_set_key(values: tuple[int, ...]) -> int:
    result = 0
    for value in values:
        result = (37 * result + value + 1) % 65521
    return result


def witness_key(entry: dict):
    return (
        int(entry["divisor"]),
        tuple(sorted(int(value) for value in entry["U"])),
        tuple(sorted(int(value) for value in entry["V"])),
    )


def authenticate_v87_locations(catalogue_pairs: list[dict]) -> dict[str, str]:
    pattern = re.compile(
        "⟨\\[([^\\]]*)\\],\\s*\\[([^\\]]*)\\],\\s*"
        "(\\d+),\\s*(\\d+),\\s*(\\d+),\\s*(\\d+),\\s*(\\d+),\\s*(\\d+)⟩",
        re.S,
    )
    hashes: dict[str, str] = {}
    cursor = 0
    for shard_index in range(66):
        path = LEAN_DIR / (
            f"Z180K30ExceptionalLiteralWitnessV87Shard{shard_index:02d}.lean"
        )
        source = path.read_text(encoding="utf-8")
        hashes[str(path.relative_to(REPO_DIR)).replace("\\", "/")] = (
            sha256_text(source)
        )
        parsed = pattern.findall(source)
        if len(parsed) != 24:
            raise SystemExit(
                f"FAIL CLOSED: V87 shard {shard_index} has {len(parsed)} entries"
            )
        for witness_index, fields in enumerate(parsed):
            if cursor >= len(catalogue_pairs):
                raise SystemExit("FAIL CLOSED: V87 sources exceed the catalogue")
            entry = catalogue_pairs[cursor]
            actual = (
                [int(value.strip()) for value in fields[0].split(",")],
                [int(value.strip()) for value in fields[1].split(",")],
                *(int(value) for value in fields[2:]),
            )
            expected = (
                entry["U"], entry["V"],
                int(entry["uWitness"]["representative"]),
                int(entry["uWitness"]["unit"]),
                int(entry["uWitness"]["translation"]),
                int(entry["vWitness"]["representative"]),
                int(entry["vWitness"]["unit"]),
                int(entry["vWitness"]["translation"]),
            )
            if actual != expected:
                raise SystemExit(
                    "FAIL CLOSED: catalogue/V87 mismatch at "
                    f"entry {cursor}, shard {shard_index}, witness {witness_index}"
                )
            entry["_shardIndex"] = shard_index
            entry["_witnessIndex"] = witness_index
            cursor += 1
    if cursor != len(catalogue_pairs):
        raise SystemExit("FAIL CLOSED: V87 source/catalogue counts differ")

    aggregate_path = LEAN_DIR / "Z180K30ExceptionalLiteralWitnessAggregateV87.lean"
    aggregate_source = aggregate_path.read_text(encoding="utf-8")
    aggregate_pattern = re.compile(
        r"\{ divisor := (\d+).*?"
        r"witnesses := z180K30ExceptionalLiteralWitnessesV87Shard(\d+).*?"
        r"verified := z180_k30_exceptional_literal_witnesses_v87_shard(\d+)",
        re.S,
    )
    aggregate_entries = aggregate_pattern.findall(aggregate_source)
    if len(aggregate_entries) != 66:
        raise SystemExit("FAIL CLOSED: V87 aggregate does not contain 66 shards")
    for shard_index, (divisor_text, witness_shard, proof_shard) in enumerate(
        aggregate_entries
    ):
        shard_pairs = catalogue_pairs[24 * shard_index:24 * (shard_index + 1)]
        shard_divisors = {int(entry["divisor"]) for entry in shard_pairs}
        if shard_divisors != {int(divisor_text)}:
            raise SystemExit(
                f"FAIL CLOSED: aggregate divisor drift at shard {shard_index}"
            )
        if int(witness_shard) != shard_index or int(proof_shard) != shard_index:
            raise SystemExit(
                f"FAIL CLOSED: aggregate order drift at shard {shard_index}"
            )
    hashes[str(aggregate_path.relative_to(REPO_DIR)).replace("\\", "/")] = (
        sha256_text(aggregate_source)
    )
    return hashes


def member_stem(divisor: int, shard_index: int) -> str:
    return f"Z180K30ExceptionalProjectiveProfileMembersV97D{divisor}S{shard_index:03d}"


def data_stem(divisor: int) -> str:
    return f"Z180K30ExceptionalProjectiveProfileDataV97D{divisor}"


def row_stem(divisor: int, u_index: int) -> str:
    return f"Z180K30ExceptionalProjectiveProfileCellsV97D{divisor}U{u_index:02d}"


def divisor_stem(divisor: int) -> str:
    return f"Z180K30ExceptionalProjectiveProfileDivisorV97D{divisor}"


def completeness_base_stem(divisor: int, side: str) -> str:
    return (
        "Z180K30ExceptionalProjectiveProfileCompletenessV97"
        f"D{divisor}{side}Base"
    )


def completeness_bucket_stem(divisor: int, side: str, bucket: int) -> str:
    return (
        "Z180K30ExceptionalProjectiveProfileCompletenessV97"
        f"D{divisor}{side}B{bucket:02d}"
    )


def completeness_aggregate_stem(divisor: int, side: str) -> str:
    return (
        "Z180K30ExceptionalProjectiveProfileCompletenessV97"
        f"D{divisor}{side}Aggregate"
    )


def completeness_prefix(divisor: int, side: str) -> str:
    return f"z180K30ProjectiveCompletenessV97D{divisor}{side}"


def completeness_source_remainder(divisor: int, side: str, bucket: int) -> str:
    return f"{completeness_prefix(divisor, side)}SourceRemainderB{bucket:02d}"


def completeness_target_remainder(divisor: int, side: str, bucket: int) -> str:
    return f"{completeness_prefix(divisor, side)}TargetRemainderB{bucket:02d}"


def completeness_source_bucket(divisor: int, side: str, bucket: int) -> str:
    return f"{completeness_prefix(divisor, side)}SourceBucketB{bucket:02d}"


def completeness_target_bucket(divisor: int, side: str, bucket: int) -> str:
    return f"{completeness_prefix(divisor, side)}TargetBucketB{bucket:02d}"


def completeness_source_tail(divisor: int, side: str, bucket: int) -> str:
    return f"{completeness_prefix(divisor, side)}SourceTailB{bucket:02d}"


def completeness_target_tail(divisor: int, side: str, bucket: int) -> str:
    return f"{completeness_prefix(divisor, side)}TargetTailB{bucket:02d}"


def completeness_bucket_theorem(divisor: int, side: str, bucket: int) -> str:
    return (
        "z180_k30_projective_profile_completeness_v97_"
        f"d{divisor}_{side.lower()}_b{bucket:02d}"
    )


def completeness_theorem(divisor: int, side: str) -> str:
    return (
        "z180_k30_projective_profile_members_complete_v97_"
        f"d{divisor}_{side.lower()}"
    )


def u_member_name(divisor: int, profile_index: int, member_index: int) -> str:
    return f"z180K30ProfileV97D{divisor}U{profile_index:02d}M{member_index:04d}"


def v_member_name(divisor: int, profile_index: int, member_index: int) -> str:
    return f"z180K30ProfileV97D{divisor}V{profile_index:02d}M{member_index:04d}"


def u_profiles_name(divisor: int) -> str:
    return f"z180K30ProjectiveUProfilesV97D{divisor}"


def v_profiles_name(divisor: int) -> str:
    return f"z180K30ProjectiveVProfilesV97D{divisor}"


def lookup_for_name(divisor: int) -> str:
    return f"z180K30ProjectiveProfileLookupForV97D{divisor}"


def cell_theorem(divisor: int, u_index: int, v_index: int) -> str:
    return f"z180_k30_projective_profile_cell_v97_d{divisor}_u{u_index:02d}_v{v_index:02d}"


def row_theorem(divisor: int, u_index: int) -> str:
    return f"z180_k30_projective_profile_row_v97_d{divisor}_u{u_index:02d}"


def lookup_record(lookup: dict) -> str:
    return (
        f"⟨{lookup['uProfileIndex']}, {lookup['vProfileIndex']}, "
        f"{lookup['uMemberIndex']}, {lookup['vMemberIndex']}, "
        f"{lookup['shardIndex']}, {lookup['witnessIndex']}⟩"
    )


def member_source(divisor: int, assignments: list[dict]) -> str:
    declarations: list[str] = []
    for assignment in assignments:
        name = assignment["name"]
        declarations.append(f"def {name} : RawSet := {lean_set(assignment['set'])}")
        if assignment["side"] == "U":
            declarations.append(f"""@[simp] theorem {name}_profile :
    projectiveUProfileV97 {divisor} {name} =
      {lean_int_list(assignment['profile'])} := by
  decide""")
        else:
            declarations.append(f"""@[simp] theorem {name}_profile :
    projectiveVProfileV97 {divisor} {name} =
      {lean_nat_list(assignment['profile'])} := by
  apply projectiveVProfileV97_eq_of_perm_sorted
  · decide
  · decide

@[simp] theorem {name}_divisible :
    projectiveSideDivisibleB_v97 {divisor} {name} = true := by
  decide""")
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileCoreV97

/-! Generated literal profile-member certificates for divisor {divisor}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

{chr(10).join(declarations)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def completeness_base_source(divisor: int, side: str, groups: list[dict],
                             member_modules: list[str],
                             bucket_count: int) -> str:
    imports = "\n".join(
        f"import Fuglede.{module}" for module in member_modules
    )
    source_names = [
        member["name"]
        for group in groups
        for member in group["members"]
    ]
    prefix = completeness_prefix(divisor, side)
    if bucket_count == 1:
        return f"""{imports}

/-! Generated hash partitions for divisor {divisor}, side {side}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def {prefix}Predicate (bucket : Nat) (set : RawSet) : Bool :=
  normalizedProjectiveRawSetKeyV89 set % 1 == bucket

def {prefix}SourceGrouped : List RawSet :=
  [{", ".join(source_names)}]

def {prefix}SourceRemainderB00 : List RawSet :=
  {prefix}SourceGrouped

def {prefix}TargetRemainderB00 : List RawSet :=
  normalizedProjectiveUnique{side}ChoicesV89 {divisor}
def {prefix}SourceBucketB00 : List RawSet :=
  {prefix}SourceRemainderB00

def {prefix}TargetBucketB00 : List RawSet :=
  {prefix}TargetRemainderB00

def {prefix}SourceTailB00 : List RawSet :=
  {prefix}SourceBucketB00

def {prefix}TargetTailB00 : List RawSet :=
  {prefix}TargetBucketB00

end Fuglede.Z180K30ExceptionalRawV2
"""
    declarations = [f"""
def {prefix}Predicate (bucket : Nat) (set : RawSet) : Bool :=
  normalizedProjectiveRawSetKeyV89 set % {bucket_count} == bucket

def {prefix}SourceGrouped : List RawSet :=
  [{", ".join(source_names)}]

""".strip()]
    for bucket in range(bucket_count):
        declarations.append(f"""
def {completeness_source_bucket(divisor, side, bucket)} : List RawSet :=
  ({prefix}SourceGrouped).filter ({prefix}Predicate {bucket})

def {completeness_target_bucket(divisor, side, bucket)} : List RawSet :=
  (normalizedProjectiveUnique{side}ChoicesV89 {divisor}).filter
    ({prefix}Predicate {bucket})
""".strip())

    return f"""import Fuglede.{COMPLETENESS_CORE_SOURCE.removesuffix('.lean')}
{imports}

/-! Generated hash partitions for divisor {divisor}, side {side}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

{chr(10).join(declarations)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def completeness_bucket_source(divisor: int, side: str, bucket: int,
                               bucket_size: int) -> str:
    return f"""import Fuglede.{completeness_base_stem(divisor, side)}

/-! Generated completeness bucket of size {bucket_size}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem {completeness_bucket_theorem(divisor, side, bucket)} :
    ({completeness_source_bucket(divisor, side, bucket)}).Perm
      {completeness_target_bucket(divisor, side, bucket)} := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def completeness_aggregate_source(divisor: int, side: str,
                                  bucket_count: int) -> str:
    imports = "\n".join(
        f"import Fuglede.{completeness_bucket_stem(divisor, side, bucket)}"
        for bucket in range(bucket_count)
    )
    if bucket_count == 1:
        prefix = completeness_prefix(divisor, side)
        return f"""{imports}

/-! Generated structural replay of completeness buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem {completeness_theorem(divisor, side)} :
    {prefix}SourceGrouped.Perm
      normalizedProjectiveUnique{side}ChoicesV89 {divisor} := by
  have hSource00 :
      {prefix}SourceTailB00.Perm {prefix}SourceRemainderB00 := by
    rfl
  have hTarget00 :
      {prefix}TargetTailB00.Perm {prefix}TargetRemainderB00 := by
    rfl
  have hBuckets00 :
      {prefix}SourceTailB00.Perm {prefix}TargetTailB00 := by
    exact {completeness_bucket_theorem(divisor, side, 0)}
  exact hSource00.symm.trans (hBuckets00.trans hTarget00)

end Fuglede.Z180K30ExceptionalRawV2
"""
    prefix = completeness_prefix(divisor, side)
    bucket_cases = "\n".join(
        f"    | {bucket} => exact {completeness_bucket_theorem(divisor, side, bucket)}"
        for bucket in range(bucket_count)
    )
    proof = f"""  have hBuckets :
      (List.range {bucket_count}).flatMap
          (fun bucket => ({prefix}SourceGrouped).filter
            ({prefix}Predicate bucket)) |>.Perm
        ((List.range {bucket_count}).flatMap
          (fun bucket => (normalizedProjectiveUnique{side}ChoicesV89 {divisor}).filter
            ({prefix}Predicate bucket))) := by
    apply List.Perm.flatMap_left
    intro bucket hbucket
    simp only [List.mem_range] at hbucket
    interval_cases bucket
{bucket_cases}
  have hSource := projectiveProfileRangeFlatMapFilterModPermV97
    normalizedProjectiveRawSetKeyV89 {bucket_count} (by decide)
    {prefix}SourceGrouped
  have hTarget := projectiveProfileRangeFlatMapFilterModPermV97
    normalizedProjectiveRawSetKeyV89 {bucket_count} (by decide)
    (normalizedProjectiveUnique{side}ChoicesV89 {divisor})
  exact hSource.symm.trans (hBuckets.trans hTarget)"""

    return f"""{imports}

/-! Generated structural replay of completeness buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem {completeness_theorem(divisor, side)} :
    {prefix}SourceGrouped.Perm
      normalizedProjectiveUnique{side}ChoicesV89 {divisor} := by
{proof}

end Fuglede.Z180K30ExceptionalRawV2
"""


def data_source(divisor: int, u_groups: list[dict], v_groups: list[dict],
                completeness_modules: list[str], positive_cells: dict) -> str:
    completeness_modules = {
        3: (
            "Z180K30ExceptionalProjectiveProfileD3UAlgebraicPilotV97",
            "Z180K30ExceptionalProjectiveProfileD3VAlgebraicEnumerationPilotV97",
        ),
        4: (
            "Z180K30ExceptionalProjectiveProfileD4UAlgebraicAggregatePilotV97",
            "Z180K30ExceptionalProjectiveProfileD4VAlgebraicAggregatePilotV97",
        ),
        6: (
            "Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgePilotV97",
            "Z180K30ExceptionalProjectiveProfileD6VAlgebraicPilotV97",
        ),
    }[divisor]
    completeness_proofs = {
        3: (
            "z180_k30_projective_d3_u_complete_algebraic_pilot_v97",
            "z180_k30_projective_d3_v_complete_algebraic_pilot_v97",
        ),
        4: (
            "z180_k30_projective_d4_u_complete_algebraic_pilot_v97",
            "z180_k30_projective_d4_v_complete_algebraic_pilot_v97",
        ),
        6: (
            "z180_k30_projective_d6_u_complete_algebraic_pilot_v97",
            "z180_k30_projective_d6_v_complete_algebraic_pilot_v97",
        ),
    }[divisor]
    imports = "\n".join(
        f"import Fuglede.{module}" for module in completeness_modules
    )
    u_classes = ",\n  ".join(
        "⟨" + lean_int_list(group["profile"]) + ", [" +
        ", ".join(member["name"] for member in group["members"]) + "]⟩"
        for group in u_groups
    )
    v_classes = ",\n  ".join(
        "⟨" + lean_nat_list(group["profile"]) + ", [" +
        ", ".join(member["name"] for member in group["members"]) + "]⟩"
        for group in v_groups
    )
    lookup_clauses = []
    for (u_index, v_index), lookups in sorted(positive_cells.items()):
        lookup_clauses.append(
            f"  | {u_index}, {v_index} =>\n      [" +
            ",\n       ".join(lookup_record(lookup) for lookup in lookups) + "]"
        )
    lookup_clauses.append("  | _, _ => []")
    u_validity_source = ""
    if divisor != 6:
        u_validity_source = f"""theorem z180_k30_projective_u_profiles_valid_v97_d{divisor} :
    projectiveUProfilesValidB_v97 {divisor}
      {u_profiles_name(divisor)} = true := by
  simp [projectiveUProfilesValidB_v97, {u_profiles_name(divisor)}]

"""
    return f"""{imports}

/-! Generated complete literal profile data for divisor {divisor}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def {u_profiles_name(divisor)} : List ProjectiveProfileClassV97 :=
  [{u_classes}]

def {v_profiles_name(divisor)} : List ProjectiveVProfileClassV97 :=
  [{v_classes}]

def {lookup_for_name(divisor)} : Nat → Nat →
    List ProjectiveProfileWitnessLookupV97
{chr(10).join(lookup_clauses)}

set_option maxRecDepth 100000 in
theorem z180_k30_projective_u_profile_members_complete_v97_d{divisor} :
    (projectiveProfileMembersV97 {u_profiles_name(divisor)}).Perm
      (normalizedProjectiveUniqueUChoicesV89 {divisor}) := by
  change {completeness_prefix(divisor, "U")}SourceGrouped.Perm _
  exact {completeness_proofs[0]}

set_option maxRecDepth 100000 in
theorem z180_k30_projective_v_profile_members_complete_v97_d{divisor} :
    (projectiveVProfileMembersV97 {v_profiles_name(divisor)}).Perm
      (normalizedProjectiveUniqueVChoicesV89 {divisor}) := by
  change {completeness_prefix(divisor, "V")}SourceGrouped.Perm _
  exact {completeness_proofs[1]}

{u_validity_source}theorem z180_k30_projective_v_profiles_valid_v97_d{divisor} :
    projectiveVProfilesValidB_v97 {divisor}
      {v_profiles_name(divisor)} = true := by
  simp [projectiveVProfilesValidB_v97, {v_profiles_name(divisor)}]

theorem z180_k30_projective_v_profiles_divisible_v97_d{divisor} :
    projectiveVProfilesDivisibleB_v97 {divisor}
      {v_profiles_name(divisor)} = true := by
  simp [projectiveVProfilesDivisibleB_v97, {v_profiles_name(divisor)}]

end Fuglede.Z180K30ExceptionalRawV2
"""


def row_source(divisor: int, u_index: int, v_group_count: int,
               positive_cells: dict) -> str:
    witness_theorems: list[str] = []
    cell_theorems: list[str] = []
    for v_index in range(v_group_count):
        lookups = positive_cells.get((u_index, v_index), [])
        local_names: list[str] = []
        for lookup_index, lookup in enumerate(lookups):
            theorem_name = (
                f"z180_k30_projective_profile_member_v97_d{divisor}_"
                f"u{u_index:02d}_v{v_index:02d}_m{lookup_index:03d}"
            )
            local_names.append(theorem_name)
            witness_theorems.append(f"""@[simp] theorem {theorem_name} :
    projectiveProfileMemberWitnessedB_v97 {divisor}
      {u_profiles_name(divisor)} {v_profiles_name(divisor)}
      ({lookup_for_name(divisor)} {u_index} {v_index})
      {u_index} {v_index} {lookup['uMemberIndex']} {lookup['vMemberIndex']} =
        true := by
  decide""")
        if not lookups:
            proof = "by\n  decide"
        else:
            u_member_count = 1 + max(
                lookup["uMemberIndex"] for lookup in lookups
            )
            v_member_count = 1 + max(
                lookup["vMemberIndex"] for lookup in lookups
            )
            actual_member_pairs = {
                (lookup["uMemberIndex"], lookup["vMemberIndex"])
                for lookup in lookups
            }
            expected_member_pairs = {
                (u_member_index, v_member_index)
                for u_member_index in range(u_member_count)
                for v_member_index in range(v_member_count)
            }
            if actual_member_pairs != expected_member_pairs:
                raise SystemExit(
                    "FAIL CLOSED: positive profile cell lookup is not an "
                    f"exact member product d={divisor}, u={u_index}, "
                    f"v={v_index}"
                )
            if divisor == 6:
                proof = f"""by
  change (List.range {u_member_count}).all (fun uMember =>
    projectiveProfileMemberWitnessedB_v97 {divisor}
      {u_profiles_name(divisor)} {v_profiles_name(divisor)}
      ({lookup_for_name(divisor)} {u_index} {v_index})
      {u_index} {v_index} uMember 0) = true
  apply List.all_eq_true.mpr
  intro uMember huMember
  simp only [List.mem_range] at huMember
  interval_cases uMember <;> simp"""
            else:
                proof = f"""by
  change (List.range {u_member_count}).all (fun uMember =>
    (List.range {v_member_count}).all (fun vMember =>
      projectiveProfileMemberWitnessedB_v97 {divisor}
        {u_profiles_name(divisor)} {v_profiles_name(divisor)}
        ({lookup_for_name(divisor)} {u_index} {v_index})
        {u_index} {v_index} uMember vMember)) = true
  apply List.all_eq_true.mpr
  intro uMember huMember
  apply List.all_eq_true.mpr
  intro vMember hvMember
  simp only [List.mem_range] at huMember hvMember
  interval_cases uMember <;> interval_cases vMember <;> simp"""
        cell_scope = "set_option maxRecDepth 100000 in\n" if divisor == 6 else ""
        cell_theorems.append(f"""{cell_scope}@[simp] theorem {cell_theorem(divisor, u_index, v_index)} :
    projectiveProfileCellCoveredB_v97 {divisor}
      {u_profiles_name(divisor)} {v_profiles_name(divisor)}
      ({lookup_for_name(divisor)} {u_index} {v_index})
      {u_index} {v_index} = true := {proof}""")
    if divisor == 6:
        row_proof = (
            f"  simpa [{v_profiles_name(divisor)}] using "
            f"{cell_theorem(divisor, u_index, 0)}"
        )
    else:
        row_proof = f"""  apply List.all_eq_true.mpr
  intro vIndex hvIndex
  simp only [List.mem_range] at hvIndex
  change vIndex < {v_group_count} at hvIndex
  interval_cases vIndex <;> simp"""
    return f"""import Fuglede.{data_stem(divisor)}

/-! Generated 213-cell audit row for divisor {divisor}, U profile {u_index}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

{chr(10).join(witness_theorems)}

{chr(10).join(cell_theorems)}

@[simp] theorem {row_theorem(divisor, u_index)} :
    (List.range {v_profiles_name(divisor)}.length).all fun vIndex =>
      projectiveProfileCellCoveredB_v97 {divisor}
        {u_profiles_name(divisor)} {v_profiles_name(divisor)}
        ({lookup_for_name(divisor)} {u_index} vIndex)
        {u_index} vIndex = true := by
{row_proof}

end Fuglede.Z180K30ExceptionalRawV2
"""


def divisor_source(divisor: int, u_group_count: int) -> str:
    imports = "\n".join(
        f"import Fuglede.{row_stem(divisor, u_index)}"
        for u_index in range(u_group_count)
    )
    if divisor == 6:
        imports += (
            "\nimport Fuglede."
            "Z180K30ExceptionalProjectiveProfileD6UValidityAggregatePilotV97"
        )
    row_cases = "\n".join(
        f"      | exact {row_theorem(divisor, u_index)}"
        for u_index in range(u_group_count)
    )
    cells_proof = f"""    unfold projectiveProfileAllCellsCoveredB_v97
    apply List.all_eq_true.mpr
    intro uIndex huIndex
    simp only [List.mem_range] at huIndex
    change uIndex < {u_group_count} at huIndex
    interval_cases uIndex <;> first
{row_cases}"""
    definition_scope = (
        "set_option maxRecDepth 100000 in\n" if divisor == 6 else ""
    )
    return f"""{imports}

/-! Generated certified profile audit for divisor {divisor}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

{definition_scope}def z180K30CertifiedProjectiveProfileAuditV97D{divisor} :
    CertifiedNormalizedProjectiveProfileAuditV97 {divisor} where
  uProfiles := {u_profiles_name(divisor)}
  vProfiles := {v_profiles_name(divisor)}
  lookupFor := {lookup_for_name(divisor)}
  uMembers_complete :=
    z180_k30_projective_u_profile_members_complete_v97_d{divisor}
  vMembers_complete :=
    z180_k30_projective_v_profile_members_complete_v97_d{divisor}
  uProfiles_valid := z180_k30_projective_u_profiles_valid_v97_d{divisor}
  vProfiles_valid := z180_k30_projective_v_profiles_valid_v97_d{divisor}
  vProfiles_divisible :=
    z180_k30_projective_v_profiles_divisible_v97_d{divisor}
  cells_covered := by
{cells_proof}

#print axioms z180K30CertifiedProjectiveProfileAuditV97D{divisor}

end Fuglede.Z180K30ExceptionalRawV2
"""


def aggregate_source() -> str:
    imports = "\n".join(
        f"import Fuglede.{divisor_stem(divisor)}"
        for divisor in SUPPORTED_DIVISORS
    )
    imports += (
        "\nimport "
        "Fuglede.Z180K30ExceptionalProjectiveScalarNormalizationAdapterV97"
    )
    return f"""{imports}

/-! Complete V97 profile certificate and the unchanged V89 audit endpoint. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_normalized_projective_profile_audit_v97 :
    Z180K30NormalizedProjectiveProfileAuditV97 := by
  intro divisor hsupported
  rcases hsupported with rfl | rfl | rfl
  · exact ⟨z180K30CertifiedProjectiveProfileAuditV97D3⟩
  · exact ⟨z180K30CertifiedProjectiveProfileAuditV97D4⟩
  · exact ⟨z180K30CertifiedProjectiveProfileAuditV97D6⟩

theorem z180_k30_normalized_projective_scalar_audit_v97 :
    Z180K30NormalizedProjectiveScalarAuditV89 :=
  normalizedProjectiveProfileAudit_to_scalarAudit_v97
    z180_k30_normalized_projective_profile_audit_v97

theorem z180_k30_projective_normalization_v97 :
    Fuglede.Z180K30ExceptionalProjectiveNormalizationV86 :=
  z180_k30_projectiveNormalization_of_scalarAudit_v97
    z180_k30_normalized_projective_scalar_audit_v97

#print axioms z180_k30_normalized_projective_profile_audit_v97
#print axioms z180_k30_normalized_projective_scalar_audit_v97
#print axioms z180_k30_projective_normalization_v97

end Fuglede.Z180K30ExceptionalRawV2
"""


def pilot_source(d3: dict) -> str:
    negative = next(cell for cell in d3["cells"] if cell["value"] != 936)
    positive = next(cell for cell in d3["cells"] if cell["value"] == 936)
    lookup = positive["lookups"][0]
    u_group = d3["uGroups"][lookup["uProfileIndex"]]
    v_group = d3["vGroups"][lookup["vProfileIndex"]]
    U = u_group["members"][lookup["uMemberIndex"]]["set"]
    V = v_group["members"][lookup["vMemberIndex"]]["set"]
    u_profile_values = u_group["profile"]
    v_profile_values = v_group["profile"]
    negative_u_group = d3["uGroups"][negative["uProfileIndex"]]
    negative_v_group = d3["vGroups"][negative["vProfileIndex"]]
    negative_U = negative_u_group["members"][0]["set"]
    negative_V = negative_v_group["members"][0]["set"]
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileCoreV97

/-! Minimal source-only pilot: one U/V profile, one negative cell, one exact positive lookup. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveProfilePilotV97U : RawSet := {lean_set(U)}
def z180K30ProjectiveProfilePilotV97V : RawSet := {lean_set(V)}

theorem z180_k30_projective_profile_pilot_v97_u :
    projectiveUProfileV97 3 z180K30ProjectiveProfilePilotV97U =
      {lean_int_list(u_profile_values)} := by
  decide

theorem z180_k30_projective_profile_pilot_v97_v :
    projectiveVProfileV97 3 z180K30ProjectiveProfilePilotV97V =
      {lean_nat_list(v_profile_values)} := by
  apply projectiveVProfileV97_eq_of_perm_sorted
  · decide
  · decide

theorem z180_k30_projective_profile_pilot_v97_v_divisible :
    projectiveSideDivisibleB_v97 3 z180K30ProjectiveProfilePilotV97V = true := by
  decide

theorem z180_k30_projective_profile_pilot_v97_negative :
    projectiveProfileDotV97
      {lean_int_list(d3['uGroups'][negative['uProfileIndex']]['profile'])}
      {lean_nat_list(d3['vGroups'][negative['vProfileIndex']]['profile'])} =
        {negative['value']} := by
  decide

def z180K30ProjectiveProfilePilotV97NegativeU : RawSet :=
  {lean_set(negative_U)}
def z180K30ProjectiveProfilePilotV97NegativeV : RawSet :=
  {lean_set(negative_V)}

def z180K30ProjectiveProfilePilotV97NegativeUClasses :
    List ProjectiveProfileClassV97 :=
  [⟨{lean_int_list(negative_u_group['profile'])},
    [z180K30ProjectiveProfilePilotV97NegativeU]⟩]

def z180K30ProjectiveProfilePilotV97NegativeVClasses :
    List ProjectiveVProfileClassV97 :=
  [⟨{lean_nat_list(negative_v_group['profile'])},
    [z180K30ProjectiveProfilePilotV97NegativeV]⟩]

theorem z180_k30_projective_profile_pilot_v97_negative_cell :
    projectiveProfileCellCoveredB_v97 3
      z180K30ProjectiveProfilePilotV97NegativeUClasses
      z180K30ProjectiveProfilePilotV97NegativeVClasses [] 0 0 = true := by
  decide

def z180K30ProjectiveProfilePilotV97UClasses :
    List ProjectiveProfileClassV97 :=
  [⟨{lean_int_list(u_profile_values)}, [z180K30ProjectiveProfilePilotV97U]⟩]

def z180K30ProjectiveProfilePilotV97VClasses :
    List ProjectiveVProfileClassV97 :=
  [⟨{lean_nat_list(v_profile_values)}, [z180K30ProjectiveProfilePilotV97V]⟩]

def z180K30ProjectiveProfilePilotV97Lookup :
    ProjectiveProfileWitnessLookupV97 :=
  ⟨0, 0, 0, 0, {lookup['shardIndex']}, {lookup['witnessIndex']}⟩

theorem z180_k30_projective_profile_pilot_v97_positive_lookup :
    projectiveProfileLookupB_v97 3
      z180K30ProjectiveProfilePilotV97UClasses
      z180K30ProjectiveProfilePilotV97VClasses
      z180K30ProjectiveProfilePilotV97Lookup = true := by
  decide

theorem z180_k30_projective_profile_pilot_v97_positive_cell :
    projectiveProfileCellCoveredB_v97 3
      z180K30ProjectiveProfilePilotV97UClasses
      z180K30ProjectiveProfilePilotV97VClasses
      [z180K30ProjectiveProfilePilotV97Lookup] 0 0 = true := by
  decide

#print axioms z180_k30_projective_profile_pilot_v97_u
#print axioms z180_k30_projective_profile_pilot_v97_v
#print axioms z180_k30_projective_profile_pilot_v97_negative
#print axioms z180_k30_projective_profile_pilot_v97_negative_cell
#print axioms z180_k30_projective_profile_pilot_v97_positive_lookup
#print axioms z180_k30_projective_profile_pilot_v97_positive_cell

end Fuglede.Z180K30ExceptionalRawV2
"""


def build_divisor(divisor: int, normalized_entries: dict) -> dict:
    u_choices, v_choices = normalized_choices(divisor)
    u_groups_map: OrderedDict[tuple[int, ...], list] = OrderedDict()
    v_groups_map: OrderedDict[tuple[int, ...], list] = OrderedDict()
    for U in u_choices:
        u_groups_map.setdefault(u_profile(divisor, U), []).append(U)
    for V in v_choices:
        v_groups_map.setdefault(v_profile(divisor, V), []).append(V)

    u_groups: list[dict] = []
    u_location: dict[tuple[int, ...], tuple[int, int]] = {}
    for profile_index, (profile, members) in enumerate(u_groups_map.items()):
        member_records = []
        for member_index, U in enumerate(members):
            name = u_member_name(divisor, profile_index, member_index)
            member_records.append({"name": name, "set": U})
            u_location[U] = (profile_index, member_index)
        u_groups.append({"profile": profile, "members": member_records})

    v_groups: list[dict] = []
    v_location: dict[tuple[int, ...], tuple[int, int]] = {}
    for profile_index, (profile, members) in enumerate(v_groups_map.items()):
        member_records = []
        for member_index, V in enumerate(members):
            name = v_member_name(divisor, profile_index, member_index)
            member_records.append({"name": name, "set": V})
            v_location[V] = (profile_index, member_index)
        v_groups.append({"profile": profile, "members": member_records})

    positive_cells: dict[tuple[int, int], list[dict]] = {}
    cells: list[dict] = []
    survivors: set[tuple[int, tuple[int, ...], tuple[int, ...]]] = set()
    for u_index, u_group in enumerate(u_groups):
        for v_index, v_group in enumerate(v_groups):
            value = profile_dot(u_group["profile"], v_group["profile"])
            lookups: list[dict] = []
            for u_member_index, u_member in enumerate(u_group["members"]):
                for v_member_index, v_member in enumerate(v_group["members"]):
                    U = tuple(u_member["set"])
                    V = tuple(v_member["set"])
                    direct = scalar_direct(U, V)
                    reverse = scalar_direct(V, U)
                    if direct != value or reverse != value:
                        raise SystemExit(
                            f"FAIL CLOSED: bilinear/profile mismatch at d={divisor}"
                        )
                    key = (divisor, U, V)
                    entry = normalized_entries.get(key)
                    if value == 936:
                        if entry is None:
                            raise SystemExit(
                                f"FAIL CLOSED: positive profile cell lacks V87 entry {key}"
                            )
                        survivors.add(key)
                        lookups.append({
                            "uProfileIndex": u_index,
                            "vProfileIndex": v_index,
                            "uMemberIndex": u_member_index,
                            "vMemberIndex": v_member_index,
                            "shardIndex": int(entry["_shardIndex"]),
                            "witnessIndex": int(entry["_witnessIndex"]),
                        })
                    elif entry is not None:
                        raise SystemExit(
                            f"FAIL CLOSED: V87 entry lies in a refuted cell {key}"
                        )
            if lookups:
                positive_cells[(u_index, v_index)] = lookups
            cells.append({
                "uProfileIndex": u_index,
                "vProfileIndex": v_index,
                "value": value,
                "memberPairCount": (
                    len(u_group["members"]) * len(v_group["members"])
                ),
                "lookups": lookups,
            })

    assignments: list[dict] = []
    for group in u_groups:
        for member in group["members"]:
            assignments.append({
                "side": "U", "name": member["name"], "set": member["set"],
                "profile": group["profile"],
            })
    for group in v_groups:
        for member in group["members"]:
            assignments.append({
                "side": "V", "name": member["name"], "set": member["set"],
                "profile": group["profile"],
            })
    return {
        "divisor": divisor,
        "uChoices": u_choices,
        "vChoices": v_choices,
        "uGroups": u_groups,
        "vGroups": v_groups,
        "positiveCells": positive_cells,
        "cells": cells,
        "assignments": assignments,
        "survivors": survivors,
    }


def build_expected() -> tuple[dict[Path, str], dict]:
    catalogue = json.loads(CATALOGUE_PATH.read_text(encoding="utf-8"))
    v87_hashes = authenticate_v87_locations(catalogue["pairs"])
    normalized_entries = {}
    for entry in catalogue["pairs"]:
        if 0 in entry["U"] and 0 in entry["V"]:
            normalized_entries.setdefault(witness_key(entry), entry)
    if len(normalized_entries) != 222:
        raise SystemExit(
            f"FAIL CLOSED: expected 222 normalized V87 entries, got {len(normalized_entries)}"
        )
    positive_encoding = json.dumps(
        sorted(normalized_entries), separators=(",", ":")
    )
    positive_sha = sha256_text(positive_encoding)
    if positive_sha != EXPECTED_POSITIVE_SHA256:
        raise SystemExit(
            f"FAIL CLOSED: positive-set SHA drift: {positive_sha}"
        )

    d4u_manifest, d4u_auth, _ = authenticate_child_manifest(
        D4U_CHILD_MANIFEST,
        REPO_DIR,
        "z180-k30-projective-profile-d4u-algebraic-v97/1",
        {
            (
                "fuglede_lean/Fuglede/"
                "Z180K30ExceptionalProjectiveProfileDataV97D4.lean"
            ),
            "fuglede_lean/Fuglede.lean",
            "scripts/generate_z180_k30_projective_profile_audit_v97.py",
            "scripts/z180_k30_projective_profile_audit_v97.manifest.json",
        },
        False,
    )
    d6_alg_manifest, d6_alg_auth, d6_alg_modules = (
        authenticate_child_manifest(
            D6_ALG_CHILD_MANIFEST,
            REPO_DIR / "fuglede_lean",
            "z180-k30-d6-algebraic-v97/1",
            {
                "Fuglede.lean",
                "Fuglede/"
                "Z180K30ExceptionalProjectiveProfileDataV97D6.lean",
            },
            True,
        )
    )
    d6_valid_manifest, d6_valid_auth, d6_valid_modules = (
        authenticate_child_manifest(
            D6_VALID_CHILD_MANIFEST,
            REPO_DIR / "fuglede_lean",
            "z180-k30-d6-u-validity-v97/1",
            {
                "Fuglede/"
                "Z180K30ExceptionalProjectiveProfileDataV97D6.lean",
                "Fuglede/"
                "Z180K30ExceptionalProjectiveProfileDivisorV97D6.lean",
            },
            True,
        )
    )
    d6_alg_auth["sealedState"] = authenticate_sealed_state(
        D6_ALG_STATE,
        "z180-k30-d6-algebraic-v97-serial-state-v1",
        d6_alg_auth["sha256"],
        d6_alg_modules,
    )
    d6_valid_auth["sealedState"] = authenticate_sealed_state(
        D6_VALID_STATE,
        "z180-k30-d6-u-validity-v97-serial-state-v1",
        d6_valid_auth["sha256"],
        d6_valid_modules,
    )

    expected: dict[Path, str] = {}
    divisor_records = []
    all_survivors = set()
    all_member_modules: list[str] = []
    all_completeness_base_modules: list[str] = []
    all_completeness_bucket_modules: list[str] = []
    all_completeness_aggregate_modules: list[str] = []
    all_data_modules: list[str] = []
    all_row_modules: list[str] = []
    all_divisor_modules: list[str] = []
    divisor_payloads: dict[int, dict] = {}

    for divisor in SUPPORTED_DIVISORS:
        payload = build_divisor(divisor, normalized_entries)
        divisor_payloads[divisor] = payload
        all_survivors.update(payload["survivors"])
        assignment_shards = chunks(payload["assignments"], MEMBER_SHARD_SIZE)
        member_modules = []
        for shard_index, shard in enumerate(assignment_shards):
            stem = member_stem(divisor, shard_index)
            member_modules.append(stem)
            all_member_modules.append(f"Fuglede.{stem}")
            expected[LEAN_DIR / f"{stem}.lean"] = member_source(divisor, shard)

        completeness_records = []
        completeness_modules = []
        for side, groups, canonical in (
            ("U", payload["uGroups"], payload["uChoices"]),
            ("V", payload["vGroups"], payload["vChoices"]),
        ):
            bucket_count = COMPLETENESS_BUCKET_COUNTS[divisor][side]
            grouped_values = [
                tuple(member["set"])
                for group in groups
                for member in group["members"]
            ]
            source_buckets = [[] for _ in range(bucket_count)]
            target_buckets = [[] for _ in range(bucket_count)]
            for values in grouped_values:
                source_buckets[
                    normalized_raw_set_key(values) % bucket_count
                ].append(values)
            for values in canonical:
                target_buckets[
                    normalized_raw_set_key(values) % bucket_count
                ].append(values)
            bucket_sizes = tuple(len(bucket) for bucket in source_buckets)
            if bucket_sizes != tuple(len(bucket) for bucket in target_buckets):
                raise SystemExit(
                    f"FAIL CLOSED: completeness bucket counts differ for "
                    f"d={divisor}, side={side}"
                )
            for bucket, (source_values, target_values) in enumerate(
                zip(source_buckets, target_buckets)
            ):
                if sorted(source_values) != sorted(target_values):
                    raise SystemExit(
                        f"FAIL CLOSED: completeness bucket {bucket} differs "
                        f"for d={divisor}, side={side}"
                    )
            maximum_allowed = 10
            if max(bucket_sizes) > maximum_allowed:
                raise SystemExit(
                    f"FAIL CLOSED: completeness bucket exceeds "
                    f"{maximum_allowed} for d={divisor}, side={side}: "
                    f"{max(bucket_sizes)}"
                )

            base_stem = completeness_base_stem(divisor, side)
            aggregate_stem = completeness_aggregate_stem(divisor, side)
            expected[LEAN_DIR / f"{base_stem}.lean"] = (
                completeness_base_source(
                    divisor, side, groups, member_modules, bucket_count
                )
            )
            all_completeness_base_modules.append(f"Fuglede.{base_stem}")
            bucket_modules = []
            for bucket, bucket_size in enumerate(bucket_sizes):
                stem = completeness_bucket_stem(divisor, side, bucket)
                bucket_modules.append(stem)
                all_completeness_bucket_modules.append(f"Fuglede.{stem}")
                expected[LEAN_DIR / f"{stem}.lean"] = (
                    completeness_bucket_source(
                        divisor, side, bucket, bucket_size
                    )
                )
            expected[LEAN_DIR / f"{aggregate_stem}.lean"] = (
                completeness_aggregate_source(
                    divisor, side, bucket_count
                )
            )
            all_completeness_aggregate_modules.append(
                f"Fuglede.{aggregate_stem}"
            )
            completeness_modules.append(aggregate_stem)
            completeness_records.append({
                "side": side,
                "candidateCount": len(canonical),
                "bucketCount": bucket_count,
                "bucketSizes": list(bucket_sizes),
                "maxBucketSize": max(bucket_sizes),
                "baseModule": f"Fuglede.{base_stem}",
                "bucketModules": [
                    f"Fuglede.{module}" for module in bucket_modules
                ],
                "aggregateModule": f"Fuglede.{aggregate_stem}",
            })
        expected[LEAN_DIR / f"{data_stem(divisor)}.lean"] = data_source(
            divisor, payload["uGroups"], payload["vGroups"],
            completeness_modules,
            payload["positiveCells"],
        )
        all_data_modules.append(f"Fuglede.{data_stem(divisor)}")
        for u_index in range(len(payload["uGroups"])):
            stem = row_stem(divisor, u_index)
            expected[LEAN_DIR / f"{stem}.lean"] = row_source(
                divisor, u_index, len(payload["vGroups"]),
                payload["positiveCells"],
            )
            all_row_modules.append(f"Fuglede.{stem}")
        expected[LEAN_DIR / f"{divisor_stem(divisor)}.lean"] = divisor_source(
            divisor, len(payload["uGroups"])
        )
        all_divisor_modules.append(f"Fuglede.{divisor_stem(divisor)}")

        divisor_records.append({
            "divisor": divisor,
            "uniqueUChoices": len(payload["uChoices"]),
            "uniqueVChoices": len(payload["vChoices"]),
            "uProfileCount": len(payload["uGroups"]),
            "vProfileCount": len(payload["vGroups"]),
            "profileCellCount": len(payload["cells"]),
            "positiveCellCount": sum(
                cell["value"] == 936 for cell in payload["cells"]
            ),
            "positivePairCount": len(payload["survivors"]),
            "memberCertificateCount": len(payload["assignments"]),
            "memberShardCount": len(assignment_shards),
            "completenessPartitions": completeness_records,
            "cells": payload["cells"],
        })

    if all_survivors != set(normalized_entries):
        raise SystemExit("FAIL CLOSED: V97 survivors differ from normalized V87")

    expected[LEAN_DIR / "Z180K30ExceptionalProjectiveProfileD3PilotV97.lean"] = (
        pilot_source(divisor_payloads[3])
    )
    expected[LEAN_DIR / "Z180K30ExceptionalProjectiveProfileAggregateV97.lean"] = (
        aggregate_source()
    )

    # Bucket and intermediate aggregate sources are derivable but dormant: the
    # public artifact ships only generated modules reachable from the endpoint.
    dormant_modules = [
        "Fuglede.Z180K30ExceptionalProjectiveProfileD3PilotV97",
        *all_completeness_bucket_modules,
        *all_completeness_aggregate_modules,
    ]
    removed_dormant = sum(
        expected.pop(source_for_module(module), None) is not None
        for module in dormant_modules
    )
    if removed_dormant != len(dormant_modules):
        raise SystemExit("FAIL CLOSED: dormant generated-module inventory drift")

    d3u_modules = [
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD3UAlgebraicPilotV97"
    ]
    d3v_modules = [
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD3VIndexPermBasePilotV97",
        *[
            "Fuglede."
            "Z180K30ExceptionalProjectiveProfileD3VIndexPerm"
            f"B{index:02d}PilotV97"
            for index in range(64)
        ],
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD3VIndexPermPilotV97",
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD3VAlgebraicEnumerationPilotV97",
    ]
    d4u_modules = topo_sort_modules(d4u_manifest["outputs"])
    d4v_modules = [
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD4VAlgebraicCorePilotV97",
        *[
            "Fuglede."
            "Z180K30ExceptionalProjectiveProfileD4VAlgebraicLeaf"
            f"{index:02d}PilotV97"
            for index in range(8)
        ],
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD4VAlgebraicAggregatePilotV97",
    ]
    external_algebraic_modules = [
        *d3u_modules,
        *d3v_modules,
        *d4u_modules,
        *d4v_modules,
        *d6_alg_modules,
    ]
    if (
        len(external_algebraic_modules) != 757
        or len(set(external_algebraic_modules)) != 757
    ):
        raise SystemExit("FAIL CLOSED: external algebraic closure is not 757")
    external_algebraic_sources = {
        source_for_module(module): source_for_module(module).read_text(
            encoding="utf-8"
        )
        for module in external_algebraic_modules
    }
    external_algebraic_hashes = {
        str(path.relative_to(REPO_DIR)).replace("\\", "/"):
            sha256_bytes(path.read_bytes())
        for path in external_algebraic_sources
    }
    simple_external_generators = {
        str(path.relative_to(REPO_DIR)).replace("\\", "/"):
            sha256_bytes(path.read_bytes())
        for path in (D3U_GENERATOR, D3V_GENERATOR, D4V_GENERATOR)
    }
    external_checker_modules = [
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD3UAlgebraicPilotV97",
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD3VAlgebraicEnumerationPilotV97",
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD4UAlgebraicAggregatePilotV97",
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD4VAlgebraicAggregatePilotV97",
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD6UAlgebraicBridgePilotV97",
        "Fuglede."
        "Z180K30ExceptionalProjectiveProfileD6VAlgebraicPilotV97",
    ]
    external_checker_set = set(external_checker_modules)
    if not external_checker_set <= set(external_algebraic_modules):
        raise SystemExit("FAIL CLOSED: external checker root absent from closure")
    external_build_only_modules = [
        module for module in external_algebraic_modules
        if module not in external_checker_set
    ]
    if len(external_build_only_modules) != 751:
        raise SystemExit("FAIL CLOSED: external build-only closure is not 751")

    forbidden_patterns = {
        "sorry": re.compile(r"\bsorry\b"),
        "axiom": re.compile(r"\baxiom\b"),
        "native_decide": re.compile(r"\bnative_decide\b"),
        "unsafe": re.compile(r"\bunsafe\b"),
        "choose": re.compile(r"\bchoose\b"),
        "drop": re.compile(r"(?:\.|\b)drop\b"),
        "take": re.compile(r"(?:\.|\b)take\b"),
    }
    audited_sources = dict(expected)
    audited_sources.update(external_algebraic_sources)
    for source_name in CORE_SOURCES:
        source_path = LEAN_DIR / source_name
        audited_sources[source_path] = source_path.read_text(encoding="utf-8")
    completeness_core_path = LEAN_DIR / COMPLETENESS_CORE_SOURCE
    audited_sources[completeness_core_path] = (
        completeness_core_path.read_text(encoding="utf-8")
    )
    for path, source in audited_sources.items():
        found = [name for name, pattern in forbidden_patterns.items()
                 if pattern.search(source)]
        if found:
            raise SystemExit(
                f"FAIL CLOSED: forbidden constructs in {path.name}: {found}"
            )

    generated_hashes = {
        str(path.relative_to(REPO_DIR)).replace("\\", "/"): sha256_text(source)
        for path, source in sorted(expected.items(), key=lambda item: str(item[0]))
    }
    core_hashes = {
        str((LEAN_DIR / name).relative_to(REPO_DIR)).replace("\\", "/"):
            sha256_bytes((LEAN_DIR / name).read_bytes())
        for name in CORE_SOURCES
    }
    core_hashes[
        str(completeness_core_path.relative_to(REPO_DIR)).replace("\\", "/")
    ] = sha256_bytes(completeness_core_path.read_bytes())
    compile_sequence = [
        "Fuglede.Z180K30ExceptionalProjectiveHistogramCoreV97",
        "Fuglede.Z180K30ExceptionalProjectiveProfileCoreV97",
        "Fuglede.Z180K30ExceptionalProjectiveProfileBridgeV97",
        "Fuglede.Z180K30ExceptionalProjectiveScalarNormalizationAdapterV97",
        *all_member_modules,
        "Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessPartitionCoreV97",
        *all_completeness_base_modules,
        *external_algebraic_modules,
        *all_data_modules,
        *all_row_modules,
        *all_divisor_modules,
        "Fuglede.Z180K30ExceptionalProjectiveProfileAggregateV97",
    ]
    if len(compile_sequence) != 946 or len(set(compile_sequence)) != 946:
        raise SystemExit("FAIL CLOSED: active compile sequence is not unique 946")
    compile_positions = {
        module: index for index, module in enumerate(compile_sequence)
    }
    import_pattern = re.compile(r"^import (Fuglede\.\S+)$", re.M)
    generated_by_module = {
        module_from_child_source(
            str(path.relative_to(REPO_DIR)).replace("\\", "/")
        ): source
        for path, source in expected.items()
    }
    compile_sources = dict(generated_by_module)
    compile_sources.update({
        module: external_algebraic_sources[source_for_module(module)]
        for module in external_algebraic_modules
    })
    for source_name in (*CORE_SOURCES, COMPLETENESS_CORE_SOURCE):
        source_path = LEAN_DIR / source_name
        module = module_from_child_source(
            str(source_path.relative_to(REPO_DIR)).replace("\\", "/")
        )
        compile_sources[module] = source_path.read_text(encoding="utf-8")
    if set(compile_sources) & set(compile_sequence) != set(compile_sequence):
        raise SystemExit("FAIL CLOSED: active compile source is unresolved")
    order_violations = []
    for module in compile_sequence:
        for dependency in import_pattern.findall(compile_sources[module]):
            if (
                dependency in compile_positions
                and compile_positions[dependency] >= compile_positions[module]
            ):
                order_violations.append((module, dependency))
    if order_violations:
        raise SystemExit(
            "FAIL CLOSED: active compile sequence is not topological: "
            f"{order_violations[:3]}"
        )
    handwritten_modules = [
        *compile_sequence[:4],
        "Fuglede.Z180K30ExceptionalProjectiveProfileCompletenessPartitionCoreV97",
    ]
    checker_modules = [
        *handwritten_modules,
        *all_completeness_base_modules,
        *external_checker_modules,
        *all_data_modules,
        *all_divisor_modules,
        "Fuglede.Z180K30ExceptionalProjectiveProfileAggregateV97",
    ]
    if len(checker_modules) != 24 or len(set(checker_modules)) != 24:
        raise SystemExit("FAIL CLOSED: checker root partition is not unique 24")
    manifest = {
        "schema": "z180-k30-projective-profile-audit-v97/v1",
        "generator": str(Path(__file__).relative_to(REPO_DIR)).replace("\\", "/"),
        "generatorSha256": sha256_bytes(Path(__file__).read_bytes()),
        "catalogue": str(CATALOGUE_PATH.relative_to(REPO_DIR)).replace("\\", "/"),
        "catalogueSha256": sha256_bytes(CATALOGUE_PATH.read_bytes()),
        "positiveSetCanonicalEncoding": "sorted compact JSON [divisor,U,V]",
        "positiveSetSha256": positive_sha,
        "v87OrderedSourcesSha256": v87_hashes,
        "coreSourcesSha256": core_hashes,
        "authenticatedChildManifests": {
            "d4uAlgebraic": d4u_auth,
            "d6Algebraic": d6_alg_auth,
            "d6UValidity": d6_valid_auth,
        },
        "unmanifestedExternalGeneratorsSha256": (
            simple_external_generators
        ),
        "externalAlgebraicSourcesSha256": external_algebraic_hashes,
        "forbiddenConstructs": list(forbidden_patterns),
        "memberShardSize": MEMBER_SHARD_SIZE,
        "divisors": divisor_records,
        "totals": {
            "uniquePairsRepresented": sum(
                record["uniqueUChoices"] * record["uniqueVChoices"]
                for record in divisor_records
            ),
            "profileCells": sum(record["profileCellCount"]
                                for record in divisor_records),
            "positiveCells": sum(record["positiveCellCount"]
                                  for record in divisor_records),
            "exactV87Pointers": sum(record["positivePairCount"]
                                     for record in divisor_records),
            "memberCertificates": sum(record["memberCertificateCount"]
                                      for record in divisor_records),
            "memberShards": len(all_member_modules),
            "completenessBaseModules": len(all_completeness_base_modules),
            "completenessBucketModules": len(all_completeness_bucket_modules),
            "completenessAggregateModules": len(
                all_completeness_aggregate_modules
            ),
            "dormantCompletenessBucketModules": len(
                all_completeness_bucket_modules
            ),
            "dormantCompletenessAggregateModules": len(
                all_completeness_aggregate_modules
            ),
            "externalAlgebraicModules": len(external_algebraic_modules),
            "authenticatedOutOfPlanD6ValidityModules": len(
                d6_valid_modules
            ),
            "activeCompileModules": len(compile_sequence),
            "rowModules": len(all_row_modules),
            "generatedLeanFiles": len(expected),
        },
        "pilot": {
            "module": "Fuglede.Z180K30ExceptionalProjectiveProfileD3PilotV97",
            "shippedInEndpointClosure": False,
            "compileAfter": [
                "Fuglede.Z180K30ExceptionalProjectiveHistogramCoreV97",
                "Fuglede.Z180K30ExceptionalProjectiveProfileCoreV97",
            ],
            "contents": [
                "one d=3 U profile", "one d=3 V profile and divisibility",
                "one negative cell certificate",
                "one exact positive V87 lookup and cell certificate",
            ],
        },
        "compileSequence": compile_sequence,
        "serialReplayPlan": {
            "schema": "z180-k30-projective-profile-v97-serial-plan/v1",
            "maxConcurrentLeanProcesses": 1,
            "memoryCapBytesPerLean": 3489660928,
            "buildOnlyLeafModules": True,
            "handwrittenModules": handwritten_modules,
            "buildOnlyMemberModules": all_member_modules,
            "checkerCompletenessBaseModules": all_completeness_base_modules,
            "externalAlgebraicModules": external_algebraic_modules,
            "buildOnlyExternalAlgebraicModules": (
                external_build_only_modules
            ),
            "checkerExternalAlgebraicModules": external_checker_modules,
            "authenticatedOutOfPlanModules": d6_valid_modules,
            "authenticatedOutOfPlanAggregateModule": (
                "Fuglede."
                "Z180K30ExceptionalProjectiveProfile"
                "D6UValidityAggregatePilotV97"
            ),
            "checkerDataModules": all_data_modules,
            "buildOnlyCellModules": all_row_modules,
            "checkerDivisorModules": all_divisor_modules,
            "checkerFinalModules": [
                "Fuglede.Z180K30ExceptionalProjectiveProfileAggregateV97"
            ],
            "checkerModules": checker_modules,
            "orderedModules": compile_sequence,
            "d6DataModule": (
                "Fuglede.Z180K30ExceptionalProjectiveProfileDataV97D6"
            ),
            "auditRoot": "audit/z180_k30_projective_profile_v97_batch",
            "pauseRequest": (
                "audit/z180_k30_projective_profile_v97_batch/pause.request"
            ),
        },
        "endpointModule": (
            "Fuglede.Z180K30ExceptionalProjectiveProfileAggregateV97"
        ),
        "endpointTheorem": "z180_k30_normalized_projective_scalar_audit_v97",
        "endpointType": "Z180K30NormalizedProjectiveScalarAuditV89",
        "normalizationAdapterTheorem": (
            "z180_k30_projectiveNormalization_of_scalarAudit_v97"
        ),
        "normalizationEndpointTheorem": (
            "z180_k30_projective_normalization_v97"
        ),
        "generatedFilesSha256": generated_hashes,
    }
    return expected, manifest


def generated_candidates() -> set[Path]:
    patterns = [
        "Z180K30ExceptionalProjectiveProfileMembersV97*.lean",
        "Z180K30ExceptionalProjectiveProfileCompletenessV97*.lean",
        "Z180K30ExceptionalProjectiveProfileDataV97*.lean",
        "Z180K30ExceptionalProjectiveProfileCellsV97*.lean",
        "Z180K30ExceptionalProjectiveProfileDivisorV97*.lean",
        "Z180K30ExceptionalProjectiveProfileAggregateV97.lean",
        "Z180K30ExceptionalProjectiveProfileD3PilotV97.lean",
    ]
    result = set()
    for pattern in patterns:
        result.update(LEAN_DIR.glob(pattern))
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--replace-generated", action="store_true")
    args = parser.parse_args()
    expected, manifest = build_expected()
    manifest_source = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    existing = generated_candidates()
    stale = sorted(existing - set(expected))
    divergent = sorted(
        path for path, source in expected.items()
        if path.exists() and path.read_text(encoding="utf-8") != source
    )
    manifest_divergent = (
        MANIFEST_PATH.exists() and
        MANIFEST_PATH.read_text(encoding="utf-8") != manifest_source
    )
    drift = bool(stale or divergent or manifest_divergent)
    if drift and not (args.write and args.replace_generated):
        raise SystemExit(
            "FAIL CLOSED: V97 generated tree drift; "
            f"stale={len(stale)}, divergent={len(divergent)}, "
            f"manifestDivergent={manifest_divergent}"
        )
    if args.write:
        if stale and not args.replace_generated:
            raise SystemExit("FAIL CLOSED: stale V97 files require --replace-generated")
        for path in stale:
            path.unlink()
        for path, source in expected.items():
            if not path.exists() or path.read_text(encoding="utf-8") != source:
                path.write_text(source, encoding="utf-8", newline="\n")
        MANIFEST_PATH.write_text(manifest_source, encoding="utf-8", newline="\n")
        print(
            "generated isolated V97 profile DAG: "
            f"{manifest['totals']['profileCells']} cells, "
            f"{manifest['totals']['exactV87Pointers']} exact pointers, "
            f"{manifest['totals']['generatedLeanFiles']} Lean files"
        )
        return
    missing = [path for path in expected if not path.exists()]
    divergent_hashes = [
        path for path, source in expected.items()
        if path.exists() and sha256_text(path.read_text(encoding="utf-8")) !=
        sha256_text(source)
    ]
    if missing or divergent_hashes or not MANIFEST_PATH.exists():
        raise SystemExit(
            "FAIL CLOSED: V97 tree incomplete; "
            f"missing={len(missing)}, divergent={len(divergent_hashes)}, "
            f"missingManifest={not MANIFEST_PATH.exists()}"
        )
    if MANIFEST_PATH.read_text(encoding="utf-8") != manifest_source:
        raise SystemExit("FAIL CLOSED: V97 manifest drift")
    print("PASS: isolated V97 profile DAG and manifest match exactly")


if __name__ == "__main__":
    main()
