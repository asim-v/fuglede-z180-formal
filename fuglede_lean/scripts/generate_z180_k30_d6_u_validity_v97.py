#!/usr/bin/env python3
"""Generate an authenticated, bounded D6 U-profile-validity proof DAG.

This generator owns the bounded validity proof family.  It reads the existing
D6 member certificates and the canonical DataD6 census, but never writes either
of them.  The final aggregate reuses the canonical DataD6 profile list instead
of introducing a second owner.  No Lean process is started by this script.
"""

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
GENERATED = ROOT / "generated"
CORE_INPUT = FUGLEDE / "Z180K30ExceptionalProjectiveProfileCoreV97.lean"
LEGACY_DATA = FUGLEDE / "Z180K30ExceptionalProjectiveProfileDataV97D6.lean"
DIVISOR = FUGLEDE / "Z180K30ExceptionalProjectiveProfileDivisorV97D6.lean"
CORE = FUGLEDE / "Z180K30ExceptionalProjectiveProfileD6UValidityCorePilotV97.lean"
STALE_DATA = (
    FUGLEDE / "Z180K30ExceptionalProjectiveProfileD6UValidityDataPilotV97.lean"
)
AGGREGATE = (
    FUGLEDE
    / "Z180K30ExceptionalProjectiveProfileD6UValidityAggregatePilotV97.lean"
)
MANIFEST = GENERATED / "z180_k30_d6_u_validity_v97.manifest.json"

MEMBER_GLOB = "Z180K30ExceptionalProjectiveProfileMembersV97D6S*.lean"
MEMBER_MODULE_RE = re.compile(
    r"Z180K30ExceptionalProjectiveProfileMembersV97D6S(\d{3})\.lean\Z"
)
U_NAME_RE = re.compile(r"z180K30ProfileV97D6U(\d{2})M(\d{4})\Z")
U_DEF_RE = re.compile(
    r"\bdef\s+(z180K30ProfileV97D6U\d{2}M\d{4})\s*:\s*RawSet\s*:=\s*"
    r"\[([^]]*)\]"
)
U_PROFILE_RE = re.compile(
    r"@\[simp\]\s*theorem\s+"
    r"(z180K30ProfileV97D6U\d{2}M\d{4})_profile\s*:\s*"
    r"projectiveUProfileV97\s+6\s+\1\s*=\s*"
    r"\[([^]]*)\]\s*:=\s*by"
)
FORBIDDEN_LEAN = re.compile(
    r"\b(?:native_decide|unsafe|sorry|axiom|choose|drop|take|decide|simp)\b"
)
MOJIBAKE = re.compile(r"(?:\ufffd|\u00c2|\u00e2)")
EXPECTED_CLASS_COUNTS = (1, 400, 450, 72, 400, 450, 72, 200, 225, 36)
EXPECTED_LEAF_COUNTS = (1, 20, 23, 4, 20, 23, 4, 10, 12, 2)
EXPECTED_SHARD_COUNT = 116
EXPECTED_MEMBER_COUNT = 2306
LEAF_SIZE = 20


@dataclass(frozen=True)
class Member:
    name: str
    u_class: int
    member_index: int
    raw_value: tuple[int, ...]
    profile: tuple[int, ...]
    shard: int
    shard_path: Path


@dataclass(frozen=True)
class Leaf:
    u_class: int
    chunk: int
    members: tuple[Member, ...]

    @property
    def tag(self) -> str:
        return f"U{self.u_class:02d}C{self.chunk:02d}"

    @property
    def module(self) -> str:
        return (
            "Z180K30ExceptionalProjectiveProfileD6UValidityLeaf"
            f"{self.tag}PilotV97"
        )

    @property
    def path(self) -> Path:
        return FUGLEDE / f"{self.module}.lean"

    @property
    def members_def(self) -> str:
        return f"z180K30ProjectiveD6UValidityMembers{self.tag}PilotV97"

    @property
    def forall_theorem(self) -> str:
        return (
            f"z180_k30_projective_d6_u_validity_members_{self.tag.lower()}_"
            "forall_pilot_v97"
        )


def group_module(u_class: int) -> str:
    return (
        "Z180K30ExceptionalProjectiveProfileD6UValidityGroup"
        f"U{u_class:02d}PilotV97"
    )


def group_path(u_class: int) -> Path:
    return FUGLEDE / f"{group_module(u_class)}.lean"


def profile_def(u_class: int) -> str:
    return f"z180K30ProjectiveD6UValidityProfileU{u_class:02d}PilotV97"


def group_members_def(u_class: int) -> str:
    return f"z180K30ProjectiveD6UValidityMembersU{u_class:02d}PilotV97"


def group_class_def(u_class: int) -> str:
    return f"z180K30ProjectiveD6UValidityClassU{u_class:02d}PilotV97"


def group_forall_theorem(u_class: int) -> str:
    return (
        f"z180_k30_projective_d6_u_validity_members_u{u_class:02d}_"
        "forall_pilot_v97"
    )


def group_valid_theorem(u_class: int) -> str:
    return (
        f"z180_k30_projective_d6_u_validity_class_u{u_class:02d}_"
        "valid_pilot_v97"
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def lean_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def lean_name_list(names: tuple[str, ...]) -> str:
    return "[" + ", ".join(names) + "]"


def parse_ints(body: str, context: str) -> tuple[int, ...]:
    pieces = [piece.strip() for piece in body.split(",") if piece.strip()]
    try:
        return tuple(int(piece) for piece in pieces)
    except ValueError as error:
        raise RuntimeError(f"nonliteral integer in {context}") from error


def bracketed_body(text: str, marker: str) -> str:
    start = text.find(marker)
    if start < 0:
        raise RuntimeError(f"missing marker {marker!r}")
    assign = text.find(":=", start)
    left = text.find("[", assign)
    if assign < 0 or left < 0:
        raise RuntimeError(f"missing list body after {marker!r}")
    depth = 0
    for index in range(left, len(text)):
        if text[index] == "[":
            depth += 1
        elif text[index] == "]":
            depth -= 1
            if depth == 0:
                return text[left + 1 : index]
    raise RuntimeError(f"unterminated list body after {marker!r}")


def split_top_level_entries(body: str) -> tuple[str, ...]:
    entries: list[str] = []
    square = 0
    angle = 0
    start: int | None = None
    for index, char in enumerate(body):
        if char == "[":
            square += 1
        elif char == "]":
            square -= 1
        elif char == "\u27e8":
            if angle == 0 and square == 0:
                start = index
            angle += 1
        elif char == "\u27e9":
            angle -= 1
            if angle == 0 and start is not None:
                entries.append(body[start : index + 1])
                start = None
        if square < 0 or angle < 0:
            raise RuntimeError("unbalanced legacy DataD6 census")
    if square != 0 or angle != 0 or start is not None:
        raise RuntimeError("unbalanced legacy DataD6 census at EOF")
    return tuple(entries)


def parse_legacy_census() -> tuple[tuple[tuple[int, ...], tuple[str, ...]], ...]:
    text = LEGACY_DATA.read_text(encoding="utf-8")
    body = bracketed_body(text, "def z180K30ProjectiveUProfilesV97D6")
    entries = split_top_level_entries(body)
    result: list[tuple[tuple[int, ...], tuple[str, ...]]] = []
    entry_re = re.compile(r"\A\u27e8\s*\[([^]]*)\]\s*,\s*\[([^]]*)\]\s*\u27e9\Z", re.S)
    for number, entry in enumerate(entries):
        match = entry_re.fullmatch(entry.strip())
        if match is None:
            raise RuntimeError(f"malformed DataD6 U class entry {number}")
        profile = parse_ints(match.group(1), f"DataD6 U class {number} profile")
        names = tuple(
            piece.strip() for piece in match.group(2).split(",") if piece.strip()
        )
        result.append((profile, names))
    return tuple(result)


def parse_members() -> tuple[tuple[Member, ...], tuple[Path, ...]]:
    paths = tuple(sorted(FUGLEDE.glob(MEMBER_GLOB), key=lambda path: path.name))
    if len(paths) != EXPECTED_SHARD_COUNT:
        raise RuntimeError(
            f"expected {EXPECTED_SHARD_COUNT} D6 member shards, found {len(paths)}"
        )
    shard_numbers: list[int] = []
    members: dict[str, Member] = {}
    for path in paths:
        module_match = MEMBER_MODULE_RE.fullmatch(path.name)
        if module_match is None:
            raise RuntimeError(f"malformed D6 member shard name {path.name}")
        shard = int(module_match.group(1))
        shard_numbers.append(shard)
        text = path.read_text(encoding="utf-8")
        definitions = {
            match.group(1): parse_ints(match.group(2), f"{path.name} RawSet")
            for match in U_DEF_RE.finditer(text)
        }
        profiles = {
            match.group(1): parse_ints(match.group(2), f"{path.name} profile")
            for match in U_PROFILE_RE.finditer(text)
        }
        if set(definitions) != set(profiles):
            missing_profiles = sorted(set(definitions) - set(profiles))
            missing_definitions = sorted(set(profiles) - set(definitions))
            raise RuntimeError(
                f"member/profile theorem mismatch in {path.name}: "
                f"missing_profiles={missing_profiles}, "
                f"missing_definitions={missing_definitions}"
            )
        for name, raw_value in definitions.items():
            name_match = U_NAME_RE.fullmatch(name)
            if name_match is None:
                raise RuntimeError(f"malformed U member name {name}")
            if name in members:
                raise RuntimeError(f"duplicate U member declaration {name}")
            members[name] = Member(
                name=name,
                u_class=int(name_match.group(1)),
                member_index=int(name_match.group(2)),
                raw_value=raw_value,
                profile=profiles[name],
                shard=shard,
                shard_path=path,
            )
    if shard_numbers != list(range(EXPECTED_SHARD_COUNT)):
        raise RuntimeError("D6 member shard indices are not exactly S000..S115")
    ordered = tuple(
        sorted(members.values(), key=lambda item: (item.u_class, item.member_index))
    )
    if len(ordered) != EXPECTED_MEMBER_COUNT:
        raise RuntimeError(
            f"expected {EXPECTED_MEMBER_COUNT} U members, found {len(ordered)}"
        )
    return ordered, paths


def authenticate_census(
    members: tuple[Member, ...],
    legacy: tuple[tuple[tuple[int, ...], tuple[str, ...]], ...],
) -> tuple[tuple[Member, ...], ...]:
    if len(legacy) != len(EXPECTED_CLASS_COUNTS):
        raise RuntimeError(f"expected ten DataD6 U classes, found {len(legacy)}")
    classes: list[tuple[Member, ...]] = []
    all_names: list[str] = []
    member_by_name = {member.name: member for member in members}
    for u_class, expected_count in enumerate(EXPECTED_CLASS_COUNTS):
        current = tuple(member for member in members if member.u_class == u_class)
        if len(current) != expected_count:
            raise RuntimeError(
                f"U{u_class:02d} count mismatch: {len(current)} != {expected_count}"
            )
        if tuple(member.member_index for member in current) != tuple(range(expected_count)):
            raise RuntimeError(f"U{u_class:02d} member indices are not contiguous")
        profiles = {member.profile for member in current}
        if len(profiles) != 1:
            raise RuntimeError(f"U{u_class:02d} does not have one profile literal")
        profile = current[0].profile
        if len(profile) != 36:
            raise RuntimeError(f"U{u_class:02d} profile length is not 36")
        legacy_profile, legacy_names = legacy[u_class]
        current_names = tuple(member.name for member in current)
        if legacy_profile != profile:
            raise RuntimeError(f"U{u_class:02d} DataD6 profile differs from member theorems")
        if legacy_names != current_names:
            raise RuntimeError(f"U{u_class:02d} DataD6 member order/census differs")
        for name in legacy_names:
            if name not in member_by_name:
                raise RuntimeError(f"DataD6 names missing member {name}")
        classes.append(current)
        all_names.extend(current_names)
    if len(all_names) != len(set(all_names)):
        raise RuntimeError("DataD6 U census contains duplicate member names")
    if set(all_names) != set(member_by_name):
        raise RuntimeError("DataD6 U census is not an exact cover of member shards")
    return tuple(classes)


def make_leaves(classes: tuple[tuple[Member, ...], ...]) -> tuple[Leaf, ...]:
    leaves: list[Leaf] = []
    actual_leaf_counts: list[int] = []
    for u_class, members in enumerate(classes):
        class_leaves: list[Leaf] = []
        for start in range(0, len(members), LEAF_SIZE):
            chunk = len(class_leaves)
            class_leaves.append(
                Leaf(u_class=u_class, chunk=chunk, members=members[start : start + LEAF_SIZE])
            )
        if not class_leaves:
            raise RuntimeError(f"U{u_class:02d} unexpectedly has no validity leaf")
        if tuple(member for leaf in class_leaves for member in leaf.members) != members:
            raise RuntimeError(f"U{u_class:02d} leaf flatten changed membership/order")
        actual_leaf_counts.append(len(class_leaves))
        leaves.extend(class_leaves)
    if tuple(actual_leaf_counts) != EXPECTED_LEAF_COUNTS:
        raise RuntimeError(
            f"validity leaf census mismatch: {tuple(actual_leaf_counts)}"
        )
    if len(leaves) != 119 or max(len(leaf.members) for leaf in leaves) > LEAF_SIZE:
        raise RuntimeError("validity leaves violate the 119/max20 contract")
    return tuple(leaves)


def nested_and(terms: tuple[str, ...]) -> str:
    if not terms:
        raise RuntimeError("cannot build an empty structural conjunction")
    result = terms[-1]
    for term in reversed(terms[:-1]):
        result = f"And.intro {term} ({result})"
    return result


def nested_append(names: tuple[str, ...]) -> str:
    if not names:
        raise RuntimeError("cannot build an empty structural append")
    result = names[-1]
    for name in reversed(names[:-1]):
        result = f"{name} ++ ({result})"
    return result


def nested_forall_append(theorems: tuple[str, ...]) -> str:
    if not theorems:
        raise RuntimeError("cannot build an empty Forall append proof")
    result = theorems[-1]
    for theorem in reversed(theorems[:-1]):
        result = (
            "(List.forall_append).2 "
            f"(And.intro {theorem} ({result}))"
        )
    return result


def core_content(classes: tuple[tuple[Member, ...], ...]) -> str:
    definitions = "\n\n".join(
        f"def {profile_def(u_class)} : List Int :=\n"
        f"  {lean_list(members[0].profile)}"
        for u_class, members in enumerate(classes)
    )
    return f"""import Fuglede.Z180K30ExceptionalProjectiveProfileCoreV97

/-! Profile constants for the isolated, bounded D6 U-validity proof DAG. -/

namespace Fuglede.Z180K30ExceptionalRawV2

{definitions}

end Fuglede.Z180K30ExceptionalRawV2
"""


def leaf_content(leaf: Leaf) -> str:
    shard_paths = tuple(
        sorted({member.shard_path for member in leaf.members}, key=lambda path: path.name)
    )
    imports = "\n".join(
        [f"import Fuglede.{CORE.stem}"]
        + [f"import Fuglede.{path.stem}" for path in shard_paths]
    )
    names = tuple(member.name for member in leaf.members)
    profile_theorems = tuple(f"{name}_profile" for name in names)
    proof = nested_and(profile_theorems)
    return f"""{imports}

/-! Bounded D6 U-validity leaf {leaf.tag}: {len(names)} certified members. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def {leaf.members_def} : List RawSet :=
  {lean_name_list(names)}

theorem {leaf.forall_theorem} :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = {profile_def(leaf.u_class)})
      {leaf.members_def} := by
  unfold {leaf.members_def} {profile_def(leaf.u_class)}
  exact {proof}

end Fuglede.Z180K30ExceptionalRawV2
"""


def group_content(u_class: int, leaves: tuple[Leaf, ...]) -> str:
    imports = "\n".join(f"import Fuglede.{leaf.module}" for leaf in leaves)
    chunk_defs = tuple(leaf.members_def for leaf in leaves)
    append_expression = nested_append(chunk_defs)
    forall_proof = nested_forall_append(tuple(leaf.forall_theorem for leaf in leaves))
    return f"""{imports}

/-! Structural aggregate for D6 U-profile class U{u_class:02d}. -/

namespace Fuglede.Z180K30ExceptionalRawV2

def {group_members_def(u_class)} : List RawSet :=
  {append_expression}

def {group_class_def(u_class)} : ProjectiveProfileClassV97 :=
  {{ profile := {profile_def(u_class)}, members := {group_members_def(u_class)} }}

theorem {group_forall_theorem(u_class)} :
    List.Forall
      (fun U => projectiveUProfileV97 6 U = {profile_def(u_class)})
      {group_members_def(u_class)} := by
  unfold {group_members_def(u_class)}
  exact {forall_proof}

theorem {group_valid_theorem(u_class)} :
    {group_class_def(u_class)}.members.all
      (fun U => projectiveUProfileV97 6 U ==
        {group_class_def(u_class)}.profile) = true := by
  change {group_members_def(u_class)}.all
    (fun U => projectiveUProfileV97 6 U == {profile_def(u_class)}) = true
  apply List.all_eq_true.mpr
  intro U hU
  apply beq_iff_eq.mpr
  exact (List.forall_iff_forall_mem.mp {group_forall_theorem(u_class)}) U hU

end Fuglede.Z180K30ExceptionalRawV2
"""


def aggregate_content() -> str:
    valid_theorems = tuple(
        group_valid_theorem(u_class)
        for u_class in range(len(EXPECTED_CLASS_COUNTS))
    )
    houter = nested_and(valid_theorems)
    group_imports = "\n".join(
        f"import Fuglede.{group_module(u_class)}"
        for u_class in range(len(EXPECTED_CLASS_COUNTS))
    )
    return f"""import Fuglede.{LEGACY_DATA.stem}
{group_imports}

/-! Exact bounded D6 U-profile-validity theorem over the canonical DataD6 list.

Integration precondition: DataV97D6 retains the profile-list definition but
delegates this theorem to the present module, so it must not define the same
theorem when this aggregate is compiled.
-/

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
theorem z180_k30_projective_u_profiles_valid_v97_d6 :
    projectiveUProfilesValidB_v97 6 z180K30ProjectiveUProfilesV97D6 = true := by
  have houter :
      List.Forall
        (fun profileClass =>
          profileClass.members.all
            (fun U => projectiveUProfileV97 6 U == profileClass.profile) = true)
        z180K30ProjectiveUProfilesV97D6 := by
    unfold z180K30ProjectiveUProfilesV97D6
    exact {houter}
  unfold projectiveUProfilesValidB_v97
  apply List.all_eq_true.mpr
  intro profileClass hprofileClass
  exact (List.forall_iff_forall_mem.mp houter) profileClass hprofileClass

end Fuglede.Z180K30ExceptionalRawV2
"""


def validate_outputs(
    outputs: dict[Path, str], leaves: tuple[Leaf, ...]
) -> None:
    if len(outputs) != 131:
        raise RuntimeError(f"expected 131 Lean outputs, generated {len(outputs)}")
    if STALE_DATA.exists():
        raise RuntimeError(
            f"stale duplicate Data owner still exists: {rel(STALE_DATA)}"
        )
    protected = {CORE_INPUT.resolve(), LEGACY_DATA.resolve(), DIVISOR.resolve()}
    for path, content in outputs.items():
        if path.resolve() in protected:
            raise RuntimeError(f"generator attempted to own protected file {rel(path)}")
        forbidden = FORBIDDEN_LEAN.search(content)
        if forbidden:
            raise RuntimeError(
                f"forbidden Lean token {forbidden.group(0)!r} in {rel(path)}"
            )
        mojibake = MOJIBAKE.search(content)
        if mojibake:
            raise RuntimeError(f"mojibake marker in {rel(path)}")
        imports_data = (
            "import Fuglede.Z180K30ExceptionalProjectiveProfileDataV97D6"
            in content
        )
        if imports_data != (path == AGGREGATE):
            raise RuntimeError(
                f"canonical DataD6 import ownership mismatch in {rel(path)}"
            )
        if f"import Fuglede.{STALE_DATA.stem}" in content:
            raise RuntimeError(f"stale duplicate Data import in {rel(path)}")
    for leaf in leaves:
        content = outputs[leaf.path]
        if not 1 <= len(leaf.members) <= LEAF_SIZE:
            raise RuntimeError(f"leaf {leaf.tag} violates max20")
        if content.count("_profile") != len(leaf.members):
            raise RuntimeError(f"leaf {leaf.tag} does not cite each profile theorem exactly once")
    aggregate = outputs[AGGREGATE]
    if aggregate.count(f"import Fuglede.{LEGACY_DATA.stem}") != 1:
        raise RuntimeError("aggregate must import canonical DataD6 exactly once")
    for u_class in range(len(EXPECTED_CLASS_COUNTS)):
        if aggregate.count(f"import Fuglede.{group_module(u_class)}") != 1:
            raise RuntimeError(
                f"aggregate must import validity group U{u_class:02d} exactly once"
            )
    if aggregate.count("List.all_eq_true.mpr") != 1:
        raise RuntimeError("aggregate must have one structural outer List.all bridge")
    if aggregate.count("_valid_pilot_v97") != 10:
        raise RuntimeError("aggregate must cite exactly ten class-valid theorems")
    if "List.all_cons" in aggregate or "rw [" in aggregate:
        raise RuntimeError("aggregate contains a recursive Boolean-expansion tactic")


def build() -> tuple[dict[Path, str], dict[str, object]]:
    members, member_paths = parse_members()
    legacy = parse_legacy_census()
    classes = authenticate_census(members, legacy)
    leaves = make_leaves(classes)
    leaves_by_class = tuple(
        tuple(leaf for leaf in leaves if leaf.u_class == u_class)
        for u_class in range(len(EXPECTED_CLASS_COUNTS))
    )

    outputs: dict[Path, str] = {CORE: core_content(classes)}
    for leaf in leaves:
        outputs[leaf.path] = leaf_content(leaf)
    for u_class, class_leaves in enumerate(leaves_by_class):
        outputs[group_path(u_class)] = group_content(u_class, class_leaves)
    outputs[AGGREGATE] = aggregate_content()
    validate_outputs(outputs, leaves)

    census_payload = [
        {
            "profile": list(legacy[u_class][0]),
            "members": list(legacy[u_class][1]),
        }
        for u_class in range(len(legacy))
    ]
    inputs = (CORE_INPUT, LEGACY_DATA, DIVISOR, *member_paths)
    manifest: dict[str, object] = {
        "schema": "z180-k30-d6-u-validity-v97/1",
        "generator": rel(Path(__file__).resolve()),
        "generator_sha256": sha256_file(Path(__file__).resolve()),
        "inputs": {rel(path): sha256_file(path) for path in inputs},
        "invariants": {
            "member_shard_count": len(member_paths),
            "u_member_count": len(members),
            "u_member_distinct_count": len({member.name for member in members}),
            "u_class_count": len(classes),
            "u_class_member_counts": list(map(len, classes)),
            "u_leaf_count": len(leaves),
            "u_leaf_counts_by_class": list(map(len, leaves_by_class)),
            "u_maximum_members_per_leaf": max(len(leaf.members) for leaf in leaves),
            "u_minimum_members_per_leaf": min(len(leaf.members) for leaf in leaves),
            "u_profile_length": 36,
            "legacy_data_exact_census_authenticated": True,
            "canonical_census_sha256": sha256_text(
                json.dumps(census_payload, separators=(",", ":"), sort_keys=True)
            ),
            "member_order_preserved_by_leaf_flatten": True,
            "generated_import_graph_acyclic": True,
            "generated_output_count": len(outputs),
            "generated_lean_decide_count": 0,
            "generated_lean_simp_count": 0,
            "forbidden_lean_tokens_absent": True,
            "mojibake_absent": True,
            "active_sources_mutated": False,
            "lean_was_run": False,
            "canonical_data_profile_list_reused": True,
            "duplicate_data_owner_absent": True,
            "legacy_monolithic_validity_theorem_must_be_removed_before_compile": True,
        },
        "classes": [
            {
                "u_class": u_class,
                "member_count": len(class_members),
                "profile": list(class_members[0].profile),
                "profile_sha256": sha256_text(json.dumps(class_members[0].profile)),
                "member_names_sha256": sha256_text(
                    json.dumps([member.name for member in class_members])
                ),
                "leaf_count": len(leaves_by_class[u_class]),
                "group_file": rel(group_path(u_class)),
                "group_file_sha256": sha256_text(outputs[group_path(u_class)]),
            }
            for u_class, class_members in enumerate(classes)
        ],
        "leaves": [
            {
                "tag": leaf.tag,
                "u_class": leaf.u_class,
                "chunk": leaf.chunk,
                "size": len(leaf.members),
                "first_member": leaf.members[0].name,
                "last_member": leaf.members[-1].name,
                "members": [member.name for member in leaf.members],
                "member_names_sha256": sha256_text(
                    json.dumps([member.name for member in leaf.members])
                ),
                "source_shards": sorted({member.shard for member in leaf.members}),
                "file": rel(leaf.path),
                "file_sha256": sha256_text(outputs[leaf.path]),
            }
            for leaf in leaves
        ],
        "compile_stages": [
            {"stage": 1, "kind": "core", "files": [rel(CORE)]},
            {
                "stage": 2,
                "kind": "profile_aligned_max20_leaves",
                "files": [rel(leaf.path) for leaf in leaves],
            },
            {
                "stage": 3,
                "kind": "ten_class_structural_aggregates",
                "files": [rel(group_path(u_class)) for u_class in range(10)],
            },
            {
                "stage": 4,
                "kind": "exact_outer_validity_aggregate",
                "files": [rel(AGGREGATE)],
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
        path.write_text(content, encoding="utf-8", newline="\n")
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(manifest_text(manifest), encoding="utf-8", newline="\n")


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
        raise RuntimeError(
            "generated D6 U-validity check failed:\n  " + "\n  ".join(failures)
        )


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
        f"members={invariants['u_member_count']}; "
        f"leaves={invariants['u_leaf_count']}; "
        f"max_leaf={invariants['u_maximum_members_per_leaf']}; "
        f"classes={invariants['u_class_count']}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError) as error:
        print(error, file=sys.stderr)
        raise SystemExit(1)
