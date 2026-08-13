#!/usr/bin/env python3
"""Generate exact literal V89 audit leaves, failing closed on any drift.

Each generated leaf contains only a small, divisor-specific number of literal
pairs.  Lean never rebuilds,
filters, chooses, drops, takes, or deduplicates the global candidate space in
a leaf.  An independent evaluator authenticates both scalar orientations and
requires every coefficient-zero survivor to be an exact normalized V87 pair.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_DIR = SCRIPT_DIR.parent
LEAN_DIR = REPO_DIR / "fuglede_lean" / "Fuglede"
CATALOGUE_PATH = SCRIPT_DIR / "z180_k30_exceptional_literal_pairs.json"
MANIFEST_PATH = SCRIPT_DIR / "z180_k30_projective_scalar_audit_v89.manifest.json"

PREFIX = "Z180K30ExceptionalProjectiveScalarV89"
DATA_PREFIX = "Z180K30ExceptionalProjectiveLiteralDataV89"
# Cartesian group sizes.  A build-only isolated replay of the original d=3
# cap-20 worst case peaked at 3,155,304,448 bytes and passed beneath the
# authenticated 3.25 GiB cap.  The measured worst d=4 and positive d=6 leaves
# likewise pass at 20.  These values are authenticated in the manifest below.
GROUP_SIZES = {3: (5, 4), 4: (20, 1), 6: (20, 1)}
PAIR_CAPS = {
    divisor: u_size * v_size
    for divisor, (u_size, v_size) in GROUP_SIZES.items()
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def chunks(values: list, size: int) -> list[list]:
    return [values[index:index + size] for index in range(0, len(values), size)]


def normalized_choice_occurrences(
    divisor: int,
) -> tuple[list[tuple[int, ...]], list[tuple[int, ...]]]:
    base = [value for value in range(36) if value % divisor == 0]
    v_choices = [
        values for values in itertools.combinations(base, 6) if 0 in values
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
            values for values in itertools.combinations(domain, 6) if 0 in values
        )
    return u_occurrences, v_choices


def normalized_choices(
    divisor: int,
) -> tuple[list[tuple[int, ...]], list[tuple[int, ...]]]:
    u_occurrences, v_occurrences = normalized_choice_occurrences(divisor)
    # First-occurrence order is exactly List.eraseDups order.
    return list(dict.fromkeys(u_occurrences)), list(dict.fromkeys(v_occurrences))


def difference_counts(values: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * 36
    for left in values:
        for right in values:
            result[(left + 36 - right) % 36] += 1
    return tuple(result)


def zeta_coefficient_zero(exponent: int) -> int:
    residue = exponent % 36
    if residue in (0, 30):
        return 1
    if residue in (12, 18):
        return -1
    return 0


def gram_trace_coefficient_zero(
    left_counts: tuple[int, ...], right_counts: tuple[int, ...]
) -> int:
    return sum(
        left_count * right_count * zeta_coefficient_zero(left * right)
        for left, left_count in enumerate(left_counts)
        for right, right_count in enumerate(right_counts)
        if left_count and right_count
    )


def lean_set(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def lean_pair(pair: tuple[tuple[int, ...], tuple[int, ...]]) -> str:
    return f"({lean_set(pair[0])}, {lean_set(pair[1])})"


def lean_list(values: list, render, indent: str = "  ") -> str:
    if not values:
        return "[]"
    return "[\n" + ",\n".join(indent + render(value) for value in values) + "\n]"


def lean_groups(groups: list[list[tuple[int, ...]]]) -> str:
    return lean_list(groups, lambda group: lean_list(group, lean_set, "      "), "    ")


def data_stem(divisor: int) -> str:
    return f"{DATA_PREFIX}D{divisor}"


def leaf_stem(divisor: int, index: int) -> str:
    return f"{PREFIX}D{divisor}B{index:03d}"


def leaf_name(divisor: int, index: int, suffix: str) -> str:
    return f"z180K30ProjectiveScalarV89D{divisor}B{index:03d}{suffix}"


def divisor_stem(divisor: int) -> str:
    return f"{PREFIX}D{divisor}"


def row_stem(divisor: int, u_index: int) -> str:
    return f"{PREFIX}D{divisor}U{u_index:03d}"


def row_lookup_name(divisor: int, u_index: int) -> str:
    return f"z180K30ProjectiveLiteralRowLookupV89D{divisor}U{u_index:03d}"


def row_theorem(divisor: int, u_index: int) -> str:
    return f"z180_k30_projective_literal_row_audit_v89_d{divisor}_u{u_index:03d}"


def divisor_theorem(divisor: int) -> str:
    return f"z180_k30_certified_projective_literal_audit_v89_d{divisor}"


def witness_key_from_json(pair: dict) -> tuple[int, tuple[int, ...], tuple[int, ...]]:
    return (
        int(pair["divisor"]),
        tuple(sorted(int(value) for value in pair["U"])),
        tuple(sorted(int(value) for value in pair["V"])),
    )


def lean_lookup(pair: dict) -> str:
    return f"⟨{int(pair['_shardIndex'])}, {int(pair['_witnessIndex'])}⟩"


def u_group_name(divisor: int, index: int) -> str:
    return f"z180K30ProjectiveLiteralUGroupV89D{divisor}G{index:03d}"


def v_group_name(divisor: int, index: int) -> str:
    return f"z180K30ProjectiveLiteralVGroupV89D{divisor}G{index:03d}"


def lookup_for_name(divisor: int) -> str:
    return f"z180K30ProjectiveLiteralLookupForV89D{divisor}"


def data_source(divisor: int, u_groups: list[list], v_groups: list[list]) -> str:
    u_getters = "\n\n".join(
        f"""theorem {u_group_name(divisor, index)} :
    z180K30ProjectiveLiteralUGroupsV89D{divisor}.getD {index} [] =
      {lean_list(group, lean_set, '      ')} := by
  decide"""
        for index, group in enumerate(u_groups)
    )
    v_getters = "\n\n".join(
        f"""theorem {v_group_name(divisor, index)} :
    z180K30ProjectiveLiteralVGroupsV89D{divisor}.getD {index} [] =
      {lean_list(group, lean_set, '      ')} := by
  decide"""
        for index, group in enumerate(v_groups)
    )
    return f"""import Fuglede.Z180K30ExceptionalProjectiveLiteralLeafCoreV89

/-! Generated literal marginal groups; authenticated by the V89 manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def z180K30ProjectiveLiteralUGroupsV89D{divisor} : List (List RawSet) :=
{lean_groups(u_groups)}

def z180K30ProjectiveLiteralVGroupsV89D{divisor} : List (List RawSet) :=
{lean_groups(v_groups)}

{u_getters}

{v_getters}

end Fuglede.Z180K30ExceptionalRawV2
"""


def leaf_source(
    divisor: int,
    index: int,
    u_index: int,
    v_index: int,
    u_group: list[tuple[int, ...]],
    v_group: list[tuple[int, ...]],
    pairs: list[tuple[tuple[int, ...], tuple[int, ...]]],
    positive_witnesses: list[dict],
) -> str:
    pairs_name = leaf_name(divisor, index, "Pairs")
    u_name = leaf_name(divisor, index, "UGroup")
    v_name = leaf_name(divisor, index, "VGroup")
    lookup_name = leaf_name(divisor, index, "Lookups")
    pair_eq = leaf_name(divisor, index, "Pairs_eq")
    audit = leaf_name(divisor, index, "Audit")
    witness_by_pair = {
        witness_key_from_json(entry)[1:]: entry for entry in positive_witnesses
    }
    pair_declarations: list[str] = []
    pair_proofs: list[str] = []
    covered_names: list[str] = []
    refuted_names: list[str] = []
    has_positive = bool(positive_witnesses)
    for pair_index, pair in enumerate(pairs):
        pair_name = leaf_name(divisor, index, f"Pair{pair_index:02d}")
        covered_name = leaf_name(divisor, index, f"Pair{pair_index:02d}Covered")
        pair_declarations.append(
            f"def {pair_name} : RawSet × RawSet := {lean_pair(pair)}"
        )
        witness_entry = witness_by_pair.get(pair)
        if witness_entry is None:
            refuted_name = leaf_name(
                divisor, index, f"Pair{pair_index:02d}Refuted"
            )
            refuted_names.append(refuted_name)
            refuted_proof = f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem {refuted_name} :
    normalizedProjectiveScalarBothRefutedB_v89 {pair_name} = true := by
  decide"""
            if has_positive:
                covered_names.append(covered_name)
                refuted_proof += f"""

theorem {covered_name} :
    normalizedProjectiveLiteralCoveredB_v89
      {divisor} {lookup_name} {pair_name} = true := by
  simp [normalizedProjectiveLiteralCoveredB_v89, {refuted_name}]"""
            pair_proofs.append(refuted_proof)
        else:
            covered_names.append(covered_name)
            lookup = lean_lookup(witness_entry)
            witnessed_name = leaf_name(
                divisor, index, f"Pair{pair_index:02d}Witnessed"
            )
            pair_proofs.append(f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem {witnessed_name} :
    normalizedProjectiveExplicitWitnessLookupB_v89
      {divisor} {pair_name} {lookup} = true := by
  decide

theorem {covered_name} :
    normalizedProjectiveLiteralCoveredB_v89
      {divisor} {lookup_name} {pair_name} = true := by
  simp [normalizedProjectiveLiteralCoveredB_v89,
    {lookup_name}, {witnessed_name}]""")
    pairs_by_name = lean_list(
        list(range(len(pairs))),
        lambda pair_index: leaf_name(divisor, index, f"Pair{pair_index:02d}"),
    )
    if has_positive:
        import_module = "Z180K30ExceptionalProjectiveLiteralAuditV89"
        lookup_definition = f"""def {lookup_name} :
    List NormalizedProjectiveExplicitWitnessLookupV89 :=
{lean_list(positive_witnesses, lean_lookup)}"""
        audit_statement = f"""{pairs_name}.all
      (normalizedProjectiveLiteralCoveredB_v89 {divisor} {lookup_name}) = true"""
        audit_simp_names = covered_names
    else:
        import_module = "Z180K30ExceptionalProjectiveLiteralLeafCoreV89"
        lookup_definition = ""
        audit_statement = (
            f"{pairs_name}.all normalizedProjectiveScalarBothRefutedB_v89 = true"
        )
        audit_simp_names = refuted_names
    aggregate_simp = ",\n    ".join(audit_simp_names)
    return f"""import Fuglede.{import_module}

/-! Generated exact literal scalar-audit leaf; authenticated by the manifest. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def {u_name} : List RawSet :=
{lean_list(u_group, lean_set)}

def {v_name} : List RawSet :=
{lean_list(v_group, lean_set)}

{chr(10).join(pair_declarations)}

def {pairs_name} : List (RawSet × RawSet) :=
{pairs_by_name}

{lookup_definition}

theorem {pair_eq} :
    {pairs_name} =
      normalizedProjectiveLiteralCartesianPairsV89
        {u_name} {v_name} := by
  decide

{chr(10).join(pair_proofs)}

theorem {audit} :
    {audit_statement} := by
  simp [{pairs_name},
    {aggregate_simp}]

#print axioms {audit}

end Fuglede.Z180K30ExceptionalRawV2
"""


def row_source(
    divisor: int,
    u_index: int,
    v_groups: list[list],
    positive_by_index: dict[int, bool],
) -> str:
    indices = [u_index * len(v_groups) + v_index
               for v_index in range(len(v_groups))]
    imports = "\n".join(
        f"import Fuglede.{leaf_stem(divisor, index)}" for index in indices
    )
    imports += f"\nimport Fuglede.{data_stem(divisor)}"
    lookup_clauses = "\n".join(
        f"  | {v_index} => " + (
            leaf_name(divisor, index, "Lookups")
            if positive_by_index[index] else "[]"
        )
        for v_index, index in enumerate(indices)
    )
    branches: list[str] = []
    for v_index, index in enumerate(indices):
        if positive_by_index[index]:
            closing = [
                f"    simpa [{row_lookup_name(divisor, u_index)}] using",
                f"      {leaf_name(divisor, index, 'Audit')}",
            ]
        else:
            closing = [
                f"    apply normalizedProjectiveLiteralAudit_of_refutations_v89",
                f"    exact {leaf_name(divisor, index, 'Audit')}",
            ]
        branches.extend([
            f"  · rw [{u_group_name(divisor, u_index)},",
            f"      {v_group_name(divisor, v_index)},",
            f"      ← {leaf_name(divisor, index, 'Pairs_eq')}]",
            *closing,
        ])
    return f"""{imports}

/-! Generated row aggregate for divisor {divisor}, U group {u_index}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def {row_lookup_name(divisor, u_index)} : Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
{lookup_clauses}
  | _ => []

theorem {row_theorem(divisor, u_index)}
    (vIndex : Nat)
    (hvIndex : vIndex < z180K30ProjectiveLiteralVGroupsV89D{divisor}.length) :
    (normalizedProjectiveLiteralCartesianPairsV89
      (z180K30ProjectiveLiteralUGroupsV89D{divisor}.getD {u_index} [])
      (z180K30ProjectiveLiteralVGroupsV89D{divisor}.getD vIndex [])).all
        (normalizedProjectiveLiteralCoveredB_v89 {divisor}
          ({row_lookup_name(divisor, u_index)} vIndex)) = true := by
  interval_cases vIndex
{chr(10).join(branches)}

#print axioms {row_theorem(divisor, u_index)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def divisor_source(
    divisor: int,
    u_groups: list[list],
    v_groups: list[list],
) -> str:
    imports = "\n".join(
        f"import Fuglede.{row_stem(divisor, u_index)}"
        for u_index in range(len(u_groups))
    )
    imports += f"\nimport Fuglede.{data_stem(divisor)}"
    lookup_clauses = "\n".join(
        f"  | {u_index}, vIndex => "
        f"{row_lookup_name(divisor, u_index)} vIndex"
        for u_index in range(len(u_groups))
    )
    branches: list[str] = []
    for u_index in range(len(u_groups)):
        branches.extend([
            f"    · simpa [{lookup_for_name(divisor)}] using",
            f"        {row_theorem(divisor, u_index)} vIndex hvIndex",
        ])
    return f"""{imports}

/-! Generated complete literal audit for divisor {divisor}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def {lookup_for_name(divisor)} : Nat → Nat →
    List NormalizedProjectiveExplicitWitnessLookupV89
{lookup_clauses}
  | _, _ => []

def {divisor_theorem(divisor)} :
    CertifiedNormalizedProjectiveLiteralAuditV89 {divisor} where
  uGroups := z180K30ProjectiveLiteralUGroupsV89D{divisor}
  vGroups := z180K30ProjectiveLiteralVGroupsV89D{divisor}
  lookupFor := {lookup_for_name(divisor)}
  uGroups_complete := by decide
  vGroups_complete := by decide
  audited := by
    intro uIndex huIndex vIndex hvIndex
    interval_cases uIndex
{chr(10).join(branches)}

#print axioms {divisor_theorem(divisor)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def aggregate_source() -> str:
    imports = "\n".join(
        f"import Fuglede.{divisor_stem(divisor)}" for divisor in GROUP_SIZES
    )
    imports += "\nimport Fuglede.Z180K30ExceptionalProjectiveNormalizationFromAuditV89"
    return f"""{imports}

/-! Complete literal audit over every normalized projective pair. -/

namespace Fuglede.Z180K30ExceptionalRawV2

theorem z180_k30_normalized_projective_scalar_audit_v89 :
    Z180K30NormalizedProjectiveLiteralAuditV89 := by
  intro divisor hsupported
  rcases hsupported with rfl | rfl | rfl
  · exact ⟨{divisor_theorem(3)}⟩
  · exact ⟨{divisor_theorem(4)}⟩
  · exact ⟨{divisor_theorem(6)}⟩

#print axioms z180_k30_normalized_projective_scalar_audit_v89

theorem z180_k30_exceptional_projective_normalization_v89 :
    Fuglede.Z180K30ExceptionalProjectiveNormalizationV86 :=
  z180_k30_projectiveNormalization_of_normalizedAudit_v89
    z180_k30_normalized_projective_scalar_audit_v89

#print axioms z180_k30_exceptional_projective_normalization_v89

end Fuglede.Z180K30ExceptionalRawV2
"""


def authenticate_v87_locations(catalogue_pairs: list[dict]) -> dict[str, str]:
    """Match every JSON record to its exact compiled shard source location."""
    pattern = re.compile(
        r"⟨\[([^\]]*)\],\s*\[([^\]]*)\],\s*"
        r"(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩",
        re.S,
    )
    source_hashes: dict[str, str] = {}
    cursor = 0
    for shard_index in range(66):
        path = LEAN_DIR / f"Z180K30ExceptionalLiteralWitnessV87Shard{shard_index:02d}.lean"
        source = path.read_text(encoding="utf-8")
        source_hashes[str(path.relative_to(REPO_DIR)).replace("\\", "/")] = (
            sha256_text(source)
        )
        parsed = pattern.findall(source)
        if len(parsed) != 24:
            raise SystemExit(
                "FAIL CLOSED: expected 24 V87 witnesses in "
                f"shard {shard_index}, got {len(parsed)}"
            )
        for witness_index, fields in enumerate(parsed):
            if cursor >= len(catalogue_pairs):
                raise SystemExit("FAIL CLOSED: V87 shard sources exceed JSON catalogue")
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
                    "FAIL CLOSED: JSON/V87 source mismatch at "
                    f"catalogue index {cursor}, shard {shard_index}, "
                    f"witness {witness_index}"
                )
            entry["_shardIndex"] = shard_index
            entry["_witnessIndex"] = witness_index
            cursor += 1
    if cursor != len(catalogue_pairs):
        raise SystemExit(
            "FAIL CLOSED: V87 shard/source count differs from catalogue: "
            f"source={cursor}, catalogue={len(catalogue_pairs)}"
        )
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
        raise SystemExit(
            "FAIL CLOSED: expected 66 ordered V87 aggregate entries, "
            f"got {len(aggregate_entries)}"
        )
    for shard_index, (divisor_text, witness_shard, proof_shard) in enumerate(
        aggregate_entries
    ):
        shard_pairs = catalogue_pairs[24 * shard_index:24 * (shard_index + 1)]
        shard_divisors = {int(entry["divisor"]) for entry in shard_pairs}
        if shard_divisors != {int(divisor_text)}:
            raise SystemExit(
                "FAIL CLOSED: V87 aggregate divisor disagrees with catalogue at "
                f"shard {shard_index}: aggregate={divisor_text}, "
                f"catalogue={sorted(shard_divisors)}"
            )
        if int(witness_shard) != shard_index or int(proof_shard) != shard_index:
            raise SystemExit(
                "FAIL CLOSED: V87 aggregate shard order drift at position "
                f"{shard_index}: witness={witness_shard}, proof={proof_shard}"
            )
    source_hashes[str(aggregate_path.relative_to(REPO_DIR)).replace("\\", "/")] = (
        sha256_text(aggregate_source)
    )
    return source_hashes


def build_expected() -> tuple[dict[Path, str], dict]:
    catalogue = json.loads(CATALOGUE_PATH.read_text(encoding="utf-8"))
    shard_source_hashes = authenticate_v87_locations(catalogue["pairs"])
    normalized_entries: dict[
        tuple[int, tuple[int, ...], tuple[int, ...]], dict
    ] = {}
    for pair in catalogue["pairs"]:
        if 0 not in pair["U"] or 0 not in pair["V"]:
            continue
        key = witness_key_from_json(pair)
        normalized_entries.setdefault(key, pair)
    if len(normalized_entries) != 222:
        raise SystemExit(
            "FAIL CLOSED: expected 222 normalized catalogue pairs, "
            f"got {len(normalized_entries)}"
        )

    expected: dict[Path, str] = {}
    divisor_data: list[dict] = []
    all_survivors: set[tuple[int, tuple[int, ...], tuple[int, ...]]] = set()

    for divisor, (u_size, v_size) in GROUP_SIZES.items():
        u_choices, v_choices = normalized_choices(divisor)
        u_groups = chunks(u_choices, u_size)
        v_groups = chunks(v_choices, v_size)
        expected[LEAN_DIR / f"{data_stem(divisor)}.lean"] = data_source(
            divisor, u_groups, v_groups
        )
        differences = {
            values: difference_counts(values) for values in u_choices + v_choices
        }
        leaf_records: list[dict] = []
        pair_union: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
        for u_index, u_group in enumerate(u_groups):
            for v_index, v_group in enumerate(v_groups):
                index = u_index * len(v_groups) + v_index
                pairs = [(U, V) for V in v_group for U in u_group]
                if not pairs or len(pairs) > PAIR_CAPS[divisor]:
                    raise SystemExit(
                        f"FAIL CLOSED: invalid literal leaf d={divisor} b={index}: "
                        f"{len(pairs)} pairs"
                    )
                pair_union.update(pairs)
                negatives: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
                positives: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
                witnesses: list[dict] = []
                forward_values: list[int] = []
                reverse_values: list[int] = []
                for U, V in pairs:
                    forward = gram_trace_coefficient_zero(
                        differences[U], differences[V]
                    )
                    reverse = gram_trace_coefficient_zero(
                        differences[V], differences[U]
                    )
                    forward_values.append(forward)
                    reverse_values.append(reverse)
                    key = (divisor, U, V)
                    if forward == 936 or reverse == 936:
                        if forward != 936 or reverse != 936:
                            raise SystemExit(
                                "FAIL CLOSED: scalar orientation asymmetry at "
                                f"d={divisor}, U={U}, V={V}"
                            )
                        entry = normalized_entries.get(key)
                        if entry is None:
                            raise SystemExit(
                                "FAIL CLOSED: scalar survivor has no V87 witness: "
                                f"{key}"
                            )
                        positives.append((U, V))
                        witnesses.append(entry)
                        all_survivors.add(key)
                    else:
                        negatives.append((U, V))
                expected[LEAN_DIR / f"{leaf_stem(divisor, index)}.lean"] = (
                    leaf_source(
                        divisor, index, u_index, v_index,
                        u_group, v_group, pairs, witnesses,
                    )
                )
                leaf_records.append({
                    "blockIndex": index,
                    "uGroupIndex": u_index,
                    "vGroupIndex": v_index,
                    "pairCount": len(pairs),
                    "refutedPairCount": len(negatives),
                    "witnessedPairCount": len(positives),
                    "explicitWitnessLocations": [
                        {
                            "shardIndex": int(entry["_shardIndex"]),
                            "witnessIndex": int(entry["_witnessIndex"]),
                            "pairSha256": sha256_text(json.dumps([
                                sorted(int(value) for value in entry["U"]),
                                sorted(int(value) for value in entry["V"]),
                            ])),
                        }
                        for entry in witnesses
                    ],
                    "forwardScalarMin": min(forward_values),
                    "forwardScalarMax": max(forward_values),
                    "reverseScalarMin": min(reverse_values),
                    "reverseScalarMax": max(reverse_values),
                    "pairsSha256": sha256_text(json.dumps(pairs)),
                    "module": f"Fuglede.{leaf_stem(divisor, index)}",
                    "auditTheorem": leaf_name(divisor, index, "Audit"),
                })
        for u_index in range(len(u_groups)):
            expected[LEAN_DIR / f"{row_stem(divisor, u_index)}.lean"] = (
                row_source(
                    divisor, u_index, v_groups,
                    {
                        leaf["blockIndex"]: leaf["witnessedPairCount"] > 0
                        for leaf in leaf_records
                    },
                )
            )
        expected[LEAN_DIR / f"{divisor_stem(divisor)}.lean"] = divisor_source(
            divisor, u_groups, v_groups
        )
        expected_pairs = {(U, V) for U in u_choices for V in v_choices}
        if pair_union != expected_pairs:
            raise SystemExit(
                f"FAIL CLOSED: literal groups do not partition d={divisor} pairs"
            )
        divisor_data.append({
            "divisor": divisor,
            "uGroupSizeCap": u_size,
            "vGroupSizeCap": v_size,
            "uGroupCount": len(u_groups),
            "vGroupCount": len(v_groups),
            "leafCount": len(leaf_records),
            "rowAggregateCount": len(u_groups),
            "uniqueUChoices": len(u_choices),
            "uniqueVChoices": len(v_choices),
            "uniquePairs": len(expected_pairs),
            "pairCountMin": min(item["pairCount"] for item in leaf_records),
            "pairCountMax": max(item["pairCount"] for item in leaf_records),
            "coefficientZeroSurvivors": sum(
                item["witnessedPairCount"] for item in leaf_records
            ),
            "coefficientZeroRefutations": sum(
                item["refutedPairCount"] for item in leaf_records
            ),
            "leaves": leaf_records,
        })

    if all_survivors != set(normalized_entries):
        missing = sorted(set(normalized_entries) - all_survivors)[:3]
        extra = sorted(all_survivors - set(normalized_entries))[:3]
        raise SystemExit(
            "FAIL CLOSED: coefficient-zero survivors differ from normalized V87 "
            f"catalogue; missing={missing}, extra={extra}"
        )

    forbidden_leaf_patterns = {
        "choose": re.compile(r"\bchoose\b"),
        "drop": re.compile(r"(?:\.|\b)drop\b"),
        "take": re.compile(r"(?:\.|\b)take\b"),
        "filter": re.compile(r"(?:\.|\b)filter\b"),
        "eraseDups": re.compile(r"\beraseDups\b"),
    }
    for divisor_data_item in divisor_data:
        for leaf in divisor_data_item["leaves"]:
            module_path = LEAN_DIR / (
                leaf["module"].removeprefix("Fuglede.") + ".lean"
            )
            source = expected[module_path]
            found = [
                name for name, pattern in forbidden_leaf_patterns.items()
                if pattern.search(source)
            ]
            if found:
                raise SystemExit(
                    "FAIL CLOSED: forbidden global-enumeration operation in "
                    f"literal leaf {leaf['module']}: {found}"
                )

    expected[LEAN_DIR / f"{PREFIX}Aggregate.lean"] = aggregate_source()
    leaf_modules = [
        leaf["module"]
        for divisor_item in divisor_data
        for leaf in divisor_item["leaves"]
    ]
    row_modules = [
        f"Fuglede.{row_stem(divisor_item['divisor'], u_index)}"
        for divisor_item in divisor_data
        for u_index in range(divisor_item["rowAggregateCount"])
    ]
    serial_batch_size = 8
    leaf_batches = [
        leaf_modules[index:index + serial_batch_size]
        for index in range(0, len(leaf_modules), serial_batch_size)
    ]
    row_batches = [
        row_modules[index:index + serial_batch_size]
        for index in range(0, len(row_modules), serial_batch_size)
    ]
    generated_hashes = {
        str(path.relative_to(REPO_DIR)).replace("\\", "/"): sha256_text(source)
        for path, source in sorted(expected.items(), key=lambda item: str(item[0]))
    }
    bridge_source_names = [
        "Z180K30ExceptionalProjectiveNormalizationV86.lean",
        "Z180K30ExceptionalProjectiveNormalizedCoreV88.lean",
        "Z180K30ExceptionalProjectiveAffineInverseV89.lean",
        "Z180K30ExceptionalProjectiveEnumerationBridgeV89.lean",
        "Z180K30ExceptionalProjectiveScalarZeroV89.lean",
        "Z180K30ExceptionalProjectiveLiteralLeafCoreV89.lean",
        "Z180K30ExceptionalProjectiveLiteralAuditV89.lean",
        "Z180K30ExceptionalProjectiveNormalizationFromAuditV89.lean",
    ]
    bridge_source_hashes = {
        str((LEAN_DIR / name).relative_to(REPO_DIR)).replace("\\", "/"):
            sha256_bytes((LEAN_DIR / name).read_bytes())
        for name in bridge_source_names
    }
    manifest = {
        "schema": "z180-k30-projective-scalar-audit-v89/v5-literal-adaptive-cap",
        "generator": str(Path(__file__).resolve().relative_to(REPO_DIR)).replace(
            "\\", "/"
        ),
        "generatorSha256": sha256_bytes(Path(__file__).read_bytes()),
        "catalogue": str(CATALOGUE_PATH.relative_to(REPO_DIR)).replace("\\", "/"),
        "catalogueSha256": sha256_bytes(CATALOGUE_PATH.read_bytes()),
        "v87OrderedSourcesSha256": shard_source_hashes,
        "bridgeSourcesSha256": bridge_source_hashes,
        "leafPairCap": max(PAIR_CAPS.values()),
        "leafPairCapsByDivisor": {
            str(divisor): PAIR_CAPS[divisor] for divisor in GROUP_SIZES
        },
        "leafEvaluation": (
            "exact literal pairs; scalar negatives; exact V87 shard/witness indices"
        ),
        "forbiddenLeafOperations": ["choose", "drop", "take", "filter", "eraseDups"],
        "divisors": divisor_data,
        "totals": {
            "uniquePairs": sum(item["uniquePairs"] for item in divisor_data),
            "literalLeaves": sum(item["leafCount"] for item in divisor_data),
            "rowAggregates": sum(
                item["rowAggregateCount"] for item in divisor_data
            ),
            "coefficientZeroSurvivors": len(all_survivors),
            "coefficientZeroRefutations": sum(
                item["coefficientZeroRefutations"] for item in divisor_data
            ),
            "generatedLeanFiles": len(expected),
        },
        "serialReplayPlan": {
            "maxConcurrentLeanProcesses": 1,
            "workingDirectory": "fuglede_lean",
            "lakeBuildExtraArgs": [],
            "serializationMethod": (
                "invoke one lake build target at a time; Lake 5.0 has no jobs flag"
            ),
            "memoryCapBytesPerLean": 3489660928,
            "leafBatchSize": serial_batch_size,
            "leafBatches": leaf_batches,
            "dataModules": [
                f"Fuglede.{data_stem(divisor)}" for divisor in GROUP_SIZES
            ],
            "rowBatches": row_batches,
            "divisorModules": [
                f"Fuglede.{divisor_stem(divisor)}" for divisor in GROUP_SIZES
            ],
            "bridgeModule": (
                "Fuglede.Z180K30ExceptionalProjectiveNormalizationFromAuditV89"
            ),
            "finalModule": f"Fuglede.{PREFIX}Aggregate",
            "checkerPolicy": (
                "build-only for authenticated finite leaf modules; individual "
                "leanchecker for LeafCore, LiteralAudit, row aggregates, divisor "
                "aggregates, normalization bridge, and final root; final/root "
                "leanchecker transitively validates imported leaf oleans"
            ),
            "buildOnlyLeafModules": True,
        },
        "generatedFilesSha256": generated_hashes,
    }
    return expected, manifest


def generated_candidates() -> set[Path]:
    return (
        set(LEAN_DIR.glob(f"{PREFIX}*.lean")) |
        set(LEAN_DIR.glob(f"{DATA_PREFIX}*.lean"))
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument(
        "--replace-generated", action="store_true",
        help="replace a previously exact generated tree after configuration change",
    )
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
            "FAIL CLOSED: generated tree drift/configuration change detected; "
            "review, then pass --write --replace-generated\n"
            f"stale={len(stale)}, divergent={len(divergent)}, "
            f"manifestDivergent={manifest_divergent}"
        )
    if args.write:
        if args.replace_generated:
            for path in stale:
                path.unlink()
        for path, source in expected.items():
            if not path.exists() or path.read_text(encoding="utf-8") != source:
                path.write_text(source, encoding="utf-8", newline="\n")
        MANIFEST_PATH.write_text(manifest_source, encoding="utf-8", newline="\n")
        print(
            f"generated exact literal tree: {manifest['totals']['literalLeaves']} "
            f"leaves, {manifest['totals']['generatedLeanFiles']} Lean files, "
            "adaptive caps " + ", ".join(
                f"d{divisor}={PAIR_CAPS[divisor]}"
                for divisor in GROUP_SIZES
            )
        )
        return

    missing = [path for path in expected if not path.exists()]
    divergent_hashes = [
        path for path, source in expected.items()
        if path.exists() and sha256_text(path.read_text(encoding="utf-8")) != sha256_text(source)
    ]
    if missing or divergent_hashes or not MANIFEST_PATH.exists():
        raise SystemExit(
            "FAIL CLOSED: generated tree incomplete or divergent; "
            f"missing={len(missing)}, divergent={len(divergent_hashes)}, "
            f"missingManifest={not MANIFEST_PATH.exists()}"
        )
    print("PASS: literal scalar V89 generated tree and manifest match exactly")


if __name__ == "__main__":
    main()
