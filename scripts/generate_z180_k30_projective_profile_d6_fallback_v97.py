#!/usr/bin/env python3
"""Generate the isolated D6 profile-completeness fallback for V97.

The active V97 data module proves one permutation of 2,306 U candidates in a
single decision.  This fallback partitions the same two enumerations into 32
deterministic hash buckets.  Each generated leaf decides a permutation of at
most 91 elements; the aggregate reconstructs the full permutation with
`List.filter_append_perm`.

Only files whose names contain `D6CompletenessFallback` and the separate
fallback manifest are ever written.  The active V97 generator, generated DAG,
manifest, and replay state are deliberately outside this script's write set.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import OrderedDict
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_DIR = SCRIPT_DIR.parent
LEAN_DIR = REPO_DIR / "fuglede_lean" / "Fuglede"
MANIFEST_PATH = (
    SCRIPT_DIR / "z180_k30_projective_profile_d6_fallback_v97.manifest.json"
)
ACTIVE_GENERATOR_PATH = (
    SCRIPT_DIR / "generate_z180_k30_projective_profile_audit_v97.py"
)

DIVISOR = 6
BUCKET_COUNT = 32
MEMBER_SHARD_SIZE = 20
EXPECTED_U_COUNT = 2306
EXPECTED_PROFILE_SIZES = (1, 400, 450, 72, 400, 450, 72, 200, 225, 36)
EXPECTED_BUCKET_SIZES = (
    64, 72, 63, 74, 53, 68, 65, 79,
    67, 84, 62, 69, 81, 90, 74, 83,
    79, 73, 69, 91, 67, 81, 70, 79,
    57, 78, 74, 73, 64, 78, 51, 74,
)

BASE_STEM = "Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackBaseV97"
AGGREGATE_STEM = (
    "Z180K30ExceptionalProjectiveProfileD6CompletenessFallbackAggregateV97"
)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def lean_list(values) -> str:
    return "[" + ", ".join(str(int(value)) for value in values) + "]"


def wrapped_list(terms: list[str], indent: str = "  ", width: int = 92) -> str:
    lines: list[str] = []
    current = indent + "["
    for index, term in enumerate(terms):
        token = term + ("," if index + 1 < len(terms) else "")
        if len(current) + 1 + len(token) > width and current != indent + "[":
            lines.append(current)
            current = indent + " " + token
        else:
            current += ("" if current.endswith("[") else " ") + token
    current += "]"
    lines.append(current)
    return "\n".join(lines)


def normalized_choice_occurrences() -> list[tuple[int, ...]]:
    modulus = 36 // DIVISOR
    selections = [[residue] for residue in range(modulus)] + [
        [first, second]
        for first in range(modulus)
        for second in range(modulus)
    ]
    occurrences: list[tuple[int, ...]] = []
    for selection in selections:
        domain = [
            value for value in range(36)
            if any(value % modulus == residue for residue in selection)
        ]
        occurrences.extend(
            tuple(values)
            for values in itertools.combinations(domain, 6)
            if 0 in values
        )
    return occurrences


def normalized_u_choices() -> list[tuple[int, ...]]:
    return list(dict.fromkeys(normalized_choice_occurrences()))


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


def u_profile(values: tuple[int, ...]) -> tuple[int, ...]:
    differences = ordered_differences(values)
    return tuple(
        sum(zeta_scalar_zero(outer * inner) for outer in differences)
        if inner % DIVISOR == 0 else 0
        for inner in range(36)
    )


def raw_set_key(values: tuple[int, ...]) -> int:
    result = 0
    for value in values:
        result = (37 * result + value + 1) % 65521
    return result


def u_member_name(profile_index: int, member_index: int) -> str:
    return f"z180K30ProfileV97D6U{profile_index:02d}M{member_index:04d}"


def member_stem(shard_index: int) -> str:
    return f"Z180K30ExceptionalProjectiveProfileMembersV97D6S{shard_index:03d}"


def bucket_stem(bucket: int) -> str:
    return (
        "Z180K30ExceptionalProjectiveProfileD6CompletenessFallback"
        f"B{bucket:02d}V97"
    )


def source_remainder(bucket: int) -> str:
    return f"z180K30ProjectiveD6FallbackSourceRemainderV97B{bucket:02d}"


def target_remainder(bucket: int) -> str:
    return f"z180K30ProjectiveD6FallbackTargetRemainderV97B{bucket:02d}"


def source_bucket(bucket: int) -> str:
    return f"z180K30ProjectiveD6FallbackSourceBucketV97B{bucket:02d}"


def target_bucket(bucket: int) -> str:
    return f"z180K30ProjectiveD6FallbackTargetBucketV97B{bucket:02d}"


def bucket_theorem(bucket: int) -> str:
    return f"z180_k30_projective_d6_fallback_bucket_v97_b{bucket:02d}"


def build_model() -> dict:
    canonical = normalized_u_choices()
    if len(canonical) != EXPECTED_U_COUNT:
        raise SystemExit(
            f"FAIL CLOSED: expected {EXPECTED_U_COUNT} D6 U choices, "
            f"got {len(canonical)}"
        )

    grouped_map: OrderedDict[tuple[int, ...], list[tuple[int, ...]]] = OrderedDict()
    for candidate in canonical:
        grouped_map.setdefault(u_profile(candidate), []).append(candidate)
    groups = list(grouped_map.values())
    profile_sizes = tuple(len(group) for group in groups)
    if profile_sizes != EXPECTED_PROFILE_SIZES:
        raise SystemExit(
            f"FAIL CLOSED: D6 U profile sizes drifted: {profile_sizes}"
        )

    source_names: list[str] = []
    source_values: list[tuple[int, ...]] = []
    for profile_index, group in enumerate(groups):
        for member_index, candidate in enumerate(group):
            source_names.append(u_member_name(profile_index, member_index))
            source_values.append(candidate)
    if len(source_names) != EXPECTED_U_COUNT:
        raise SystemExit("FAIL CLOSED: grouped D6 U count drifted")

    source_bucket_values = [[] for _ in range(BUCKET_COUNT)]
    target_bucket_values = [[] for _ in range(BUCKET_COUNT)]
    for candidate in source_values:
        source_bucket_values[raw_set_key(candidate) % BUCKET_COUNT].append(candidate)
    for candidate in canonical:
        target_bucket_values[raw_set_key(candidate) % BUCKET_COUNT].append(candidate)
    source_sizes = tuple(map(len, source_bucket_values))
    target_sizes = tuple(map(len, target_bucket_values))
    if source_sizes != EXPECTED_BUCKET_SIZES or target_sizes != EXPECTED_BUCKET_SIZES:
        raise SystemExit(
            "FAIL CLOSED: D6 fallback bucket census drifted: "
            f"source={source_sizes}, target={target_sizes}"
        )
    for bucket in range(BUCKET_COUNT):
        if sorted(source_bucket_values[bucket]) != sorted(target_bucket_values[bucket]):
            raise SystemExit(
                f"FAIL CLOSED: D6 fallback bucket {bucket} is not extensionally equal"
            )

    return {
        "canonical": canonical,
        "sourceNames": source_names,
        "sourceValues": source_values,
        "profileSizes": profile_sizes,
        "bucketSizes": source_sizes,
    }


def base_source(model: dict) -> str:
    shard_count = (EXPECTED_U_COUNT + 1 + MEMBER_SHARD_SIZE - 1) // MEMBER_SHARD_SIZE
    imports = "\n".join(
        f"import Fuglede.{member_stem(index)}" for index in range(shard_count)
    )
    source_names = wrapped_list(model["sourceNames"])
    declarations: list[str] = []
    declarations.append("""
def z180K30ProjectiveD6FallbackPredicateV97
    (bucket : Nat) (U : RawSet) : Bool :=
  normalizedProjectiveRawSetKeyV89 U % 32 == bucket

def z180K30ProjectiveD6FallbackSourceGroupedV97 : List RawSet :=
SOURCE_NAMES

def z180K30ProjectiveD6FallbackSourceRemainderV97B00 : List RawSet :=
  z180K30ProjectiveD6FallbackSourceGroupedV97

def z180K30ProjectiveD6FallbackTargetRemainderV97B00 : List RawSet :=
  normalizedProjectiveUniqueUChoicesV89 6
""".replace("SOURCE_NAMES", source_names).strip())

    for bucket in range(BUCKET_COUNT - 1):
        declarations.append(f"""
def {source_bucket(bucket)} : List RawSet :=
  ({source_remainder(bucket)}).filter
    (z180K30ProjectiveD6FallbackPredicateV97 {bucket})

def {target_bucket(bucket)} : List RawSet :=
  ({target_remainder(bucket)}).filter
    (z180K30ProjectiveD6FallbackPredicateV97 {bucket})

def {source_remainder(bucket + 1)} : List RawSet :=
  ({source_remainder(bucket)}).filter fun U =>
    !(z180K30ProjectiveD6FallbackPredicateV97 {bucket} U)

def {target_remainder(bucket + 1)} : List RawSet :=
  ({target_remainder(bucket)}).filter fun U =>
    !(z180K30ProjectiveD6FallbackPredicateV97 {bucket} U)
""".strip())

    declarations.append(f"""
def {source_bucket(BUCKET_COUNT - 1)} : List RawSet :=
  {source_remainder(BUCKET_COUNT - 1)}

def {target_bucket(BUCKET_COUNT - 1)} : List RawSet :=
  {target_remainder(BUCKET_COUNT - 1)}
""".strip())

    declarations.append(f"""
def z180K30ProjectiveD6FallbackSourceTailV97B31 : List RawSet :=
  {source_bucket(BUCKET_COUNT - 1)}

def z180K30ProjectiveD6FallbackTargetTailV97B31 : List RawSet :=
  {target_bucket(BUCKET_COUNT - 1)}
""".strip())
    for bucket in reversed(range(BUCKET_COUNT - 1)):
        declarations.append(f"""
def z180K30ProjectiveD6FallbackSourceTailV97B{bucket:02d} : List RawSet :=
  {source_bucket(bucket)} ++
    z180K30ProjectiveD6FallbackSourceTailV97B{bucket + 1:02d}

def z180K30ProjectiveD6FallbackTargetTailV97B{bucket:02d} : List RawSet :=
  {target_bucket(bucket)} ++
    z180K30ProjectiveD6FallbackTargetTailV97B{bucket + 1:02d}
""".strip())

    return f"""{imports}

/-!
Generated, isolated fallback data for D6 U-profile completeness.

The 2,306-element grouped and canonical lists are split by the existing V89
raw-set key modulo 32.  Bucket 31 is the residual after filters 0 through 30,
so the aggregate needs no arithmetic exhaustiveness theorem.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

{chr(10).join(declarations)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def bucket_source(bucket: int, expected_size: int) -> str:
    return f"""import Fuglede.{BASE_STEM}

/-! Isolated D6 completeness fallback bucket {bucket}; exact size {expected_size}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
theorem {bucket_theorem(bucket)} :
    ({source_bucket(bucket)}).Perm
      {target_bucket(bucket)} := by
  decide

end Fuglede.Z180K30ExceptionalRawV2
"""


def append_expression(names: list[str]) -> str:
    result = names[-1]
    for name in reversed(names[:-1]):
        result = f"({name} ++ {result})"
    return result


def aggregate_source() -> str:
    imports = "\n".join(
        f"import Fuglede.{bucket_stem(bucket)}" for bucket in range(BUCKET_COUNT)
    )
    source_tails = {
        bucket: f"z180K30ProjectiveD6FallbackSourceTailV97B{bucket:02d}"
        for bucket in range(BUCKET_COUNT)
    }
    target_tails = {
        bucket: f"z180K30ProjectiveD6FallbackTargetTailV97B{bucket:02d}"
        for bucket in range(BUCKET_COUNT)
    }

    proof_lines: list[str] = []
    final_bucket = BUCKET_COUNT - 1
    proof_lines.extend([
        f"  have hSource{final_bucket:02d} :",
        f"      {source_tails[final_bucket]}.Perm {source_remainder(final_bucket)} := by",
        f"    rfl",
        f"  have hTarget{final_bucket:02d} :",
        f"      {target_tails[final_bucket]}.Perm {target_remainder(final_bucket)} := by",
        f"    rfl",
        f"  have hBuckets{final_bucket:02d} :",
        f"      {source_tails[final_bucket]}.Perm {target_tails[final_bucket]} := by",
        f"    exact {bucket_theorem(final_bucket)}",
    ])

    for bucket in reversed(range(BUCKET_COUNT - 1)):
        proof_lines.extend([
            f"  have hSourceSplit{bucket:02d} :",
            f"      ({source_bucket(bucket)} ++ {source_remainder(bucket + 1)}).Perm",
            f"        {source_remainder(bucket)} := by",
            f"    simpa only [{source_bucket(bucket)}, {source_remainder(bucket + 1)}] using",
            "      (List.filter_append_perm",
            f"        (z180K30ProjectiveD6FallbackPredicateV97 {bucket})",
            f"        {source_remainder(bucket)})",
            f"  have hTargetSplit{bucket:02d} :",
            f"      ({target_bucket(bucket)} ++ {target_remainder(bucket + 1)}).Perm",
            f"        {target_remainder(bucket)} := by",
            f"    simpa only [{target_bucket(bucket)}, {target_remainder(bucket + 1)}] using",
            "      (List.filter_append_perm",
            f"        (z180K30ProjectiveD6FallbackPredicateV97 {bucket})",
            f"        {target_remainder(bucket)})",
            f"  have hSource{bucket:02d} :",
            f"      {source_tails[bucket]}.Perm {source_remainder(bucket)} := by",
            f"    change ({source_bucket(bucket)} ++ {source_tails[bucket + 1]}).Perm _",
            "    exact",
            f"      ((List.Perm.refl {source_bucket(bucket)}).append hSource{bucket + 1:02d}).trans",
            f"        hSourceSplit{bucket:02d}",
            f"  have hTarget{bucket:02d} :",
            f"      {target_tails[bucket]}.Perm {target_remainder(bucket)} := by",
            f"    change ({target_bucket(bucket)} ++ {target_tails[bucket + 1]}).Perm _",
            "    exact",
            f"      ((List.Perm.refl {target_bucket(bucket)}).append hTarget{bucket + 1:02d}).trans",
            f"        hTargetSplit{bucket:02d}",
            f"  have hBuckets{bucket:02d} :",
            f"      {source_tails[bucket]}.Perm {target_tails[bucket]} := by",
            f"    change ({source_bucket(bucket)} ++ {source_tails[bucket + 1]}).Perm",
            f"      ({target_bucket(bucket)} ++ {target_tails[bucket + 1]})",
            "    exact",
            f"      {bucket_theorem(bucket)}.append hBuckets{bucket + 1:02d}",
        ])

    proof_lines.append(
        "  exact hSource00.symm.trans (hBuckets00.trans hTarget00)"
    )

    return f"""{imports}

/-! Structural replay of the 32 isolated D6 completeness buckets. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_projective_u_profile_members_complete_fallback_v97_d6 :
    z180K30ProjectiveD6FallbackSourceGroupedV97.Perm
      normalizedProjectiveUniqueUChoicesV89 6 := by
{chr(10).join(proof_lines)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def build_expected() -> tuple[dict[Path, str], dict]:
    model = build_model()
    expected: dict[Path, str] = {
        LEAN_DIR / f"{BASE_STEM}.lean": base_source(model),
        LEAN_DIR / f"{AGGREGATE_STEM}.lean": aggregate_source(),
    }
    for bucket, size in enumerate(model["bucketSizes"]):
        expected[LEAN_DIR / f"{bucket_stem(bucket)}.lean"] = bucket_source(bucket, size)

    manifest = {
        "schema": "z180-k30-projective-profile-d6-completeness-fallback-v97/v1",
        "generator": str(ACTIVE_GENERATOR_PATH.relative_to(REPO_DIR)).replace("\\", "/"),
        "activeGeneratorSha256": sha256_bytes(ACTIVE_GENERATOR_PATH.read_bytes()),
        "fallbackGenerator": str(Path(__file__).resolve().relative_to(REPO_DIR)).replace("\\", "/"),
        "fallbackGeneratorSha256": sha256_bytes(Path(__file__).resolve().read_bytes()),
        "d6UCount": EXPECTED_U_COUNT,
        "profileSizes": list(model["profileSizes"]),
        "bucketCount": BUCKET_COUNT,
        "bucketSizes": list(model["bucketSizes"]),
        "maxBucketSize": max(model["bucketSizes"]),
        "leanFiles": {
            str(path.relative_to(REPO_DIR)).replace("\\", "/"): sha256_text(source)
            for path, source in sorted(expected.items())
        },
        "compileSequence": [
            str((LEAN_DIR / f"{BASE_STEM}.lean").relative_to(REPO_DIR)).replace("\\", "/"),
            *[
                str((LEAN_DIR / f"{bucket_stem(bucket)}.lean").relative_to(REPO_DIR)).replace("\\", "/")
                for bucket in range(BUCKET_COUNT)
            ],
            str((LEAN_DIR / f"{AGGREGATE_STEM}.lean").relative_to(REPO_DIR)).replace("\\", "/"),
        ],
    }
    return expected, manifest


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--replace-generated", action="store_true")
    arguments = parser.parse_args()
    expected, manifest = build_expected()
    manifest_source = json.dumps(manifest, indent=2, sort_keys=True) + "\n"

    if arguments.write:
        for path, source in expected.items():
            if path.exists() and not arguments.replace_generated:
                raise SystemExit(f"FAIL CLOSED: refusing to replace {path}")
            path.write_text(source, encoding="utf-8", newline="\n")
        if MANIFEST_PATH.exists() and not arguments.replace_generated:
            raise SystemExit(f"FAIL CLOSED: refusing to replace {MANIFEST_PATH}")
        MANIFEST_PATH.write_text(manifest_source, encoding="utf-8", newline="\n")
        print(
            "WROTE isolated D6 fallback: "
            f"{len(expected)} Lean files, {EXPECTED_U_COUNT} candidates, "
            f"{BUCKET_COUNT} buckets, max bucket {max(EXPECTED_BUCKET_SIZES)}"
        )
        return

    failures: list[str] = []
    for path, source in expected.items():
        if not path.exists():
            failures.append(f"missing {path}")
        elif path.read_text(encoding="utf-8") != source:
            failures.append(f"drift {path}")
    if not MANIFEST_PATH.exists():
        failures.append(f"missing {MANIFEST_PATH}")
    elif MANIFEST_PATH.read_text(encoding="utf-8") != manifest_source:
        failures.append(f"drift {MANIFEST_PATH}")
    if failures:
        raise SystemExit("FAIL CLOSED:\n" + "\n".join(failures))
    print(
        "PASS isolated D6 fallback: "
        f"{len(expected)} Lean files, {EXPECTED_U_COUNT} candidates, "
        f"bucket sizes {list(EXPECTED_BUCKET_SIZES)}"
    )


if __name__ == "__main__":
    main()
