#!/usr/bin/env python3
"""Audit the exact Lean source release for Fuglede on Z/180Z.

The script reconstructs the local import closure from
Fuglede.Z180FugledeTheorem, verifies that no extra Lean module is shipped,
scans executable source (comments and strings removed) for proof escape
hatches, and authenticates every proof input with SHA-256.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import re
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
LEAN_PROJECT = REPO_ROOT / "fuglede_lean"
MODULE_ROOT = LEAN_PROJECT / "Fuglede"
ENTRY = MODULE_ROOT / "Z180FugledeTheorem.lean"
MANIFEST = REPO_ROOT / "verification" / "Z180_RELEASE_SHA256.txt"

PROJECT_INPUTS = (
    LEAN_PROJECT / "Fuglede.lean",
    LEAN_PROJECT / "lakefile.toml",
    LEAN_PROJECT / "lean-toolchain",
    LEAN_PROJECT / "lake-manifest.json",
)

IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)
ABSOLUTE_USER_PATH_RE = re.compile(r"(?i)[a-z]:[/\\]users[/\\]")
FORBIDDEN = (
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom", re.compile(r"\baxiom\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
)


class AuditFailure(RuntimeError):
    """A deterministic release invariant failed."""


def strip_comments_and_strings(source: str) -> str:
    """Remove nested Lean comments and double-quoted strings.

    Newlines are preserved so diagnostics retain useful line numbers.
    """

    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False

    while i < len(source):
        if block_depth:
            if source.startswith("/-", i):
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif source.startswith("-/", i):
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                char = source[i]
                out.append("\n" if char == "\n" else " ")
                i += 1
            continue

        if in_string:
            char = source[i]
            out.append("\n" if char == "\n" else " ")
            i += 1
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue

        if source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if source.startswith("/-", i):
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue

        if source[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(source[i])
        i += 1

    if block_depth:
        raise AuditFailure("unterminated block comment in Lean source")
    if in_string:
        raise AuditFailure("unterminated string in Lean source")
    return "".join(out)


def module_path(module: str) -> Path:
    if not module.startswith("Fuglede."):
        raise ValueError(f"not a local module: {module}")
    relative = module.removeprefix("Fuglede.").replace(".", "/") + ".lean"
    return MODULE_ROOT / relative


def local_imports(path: Path) -> list[Path]:
    source = path.read_text(encoding="utf-8-sig")
    executable = strip_comments_and_strings(source)
    imports: list[Path] = []
    for match in IMPORT_RE.finditer(executable):
        for module in match.group(1).split():
            if module.startswith("Fuglede."):
                imports.append(module_path(module))
    return imports


def import_closure(entry: Path) -> set[Path]:
    pending = [entry]
    visited: set[Path] = set()
    missing: set[Path] = set()

    while pending:
        path = pending.pop()
        if path in visited:
            continue
        if not path.is_file():
            missing.add(path)
            continue
        visited.add(path)
        pending.extend(local_imports(path))

    if missing:
        listed = "\n".join(
            f"  - {path.relative_to(REPO_ROOT).as_posix()}"
            for path in sorted(missing)
        )
        raise AuditFailure(f"missing local imports:\n{listed}")
    return visited


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def release_inputs(closure: set[Path]) -> list[Path]:
    inputs = [*PROJECT_INPUTS, *closure]
    missing = [path for path in inputs if not path.is_file()]
    if missing:
        raise AuditFailure(
            "missing project inputs: "
            + ", ".join(path.relative_to(REPO_ROOT).as_posix() for path in missing)
        )
    return sorted(inputs, key=lambda path: path.relative_to(REPO_ROOT).as_posix())


def manifest_text(paths: list[Path]) -> str:
    lines = [
        f"{sha256(path)}  {path.relative_to(REPO_ROOT).as_posix()}"
        for path in paths
    ]
    return "\n".join(lines) + "\n"


def verify_manifest(expected: str) -> None:
    if not MANIFEST.is_file():
        raise AuditFailure(
            f"missing manifest {MANIFEST.relative_to(REPO_ROOT).as_posix()}"
        )
    actual = MANIFEST.read_text(encoding="utf-8")
    if actual != expected:
        difference = "".join(
            difflib.unified_diff(
                actual.splitlines(keepends=True),
                expected.splitlines(keepends=True),
                fromfile="committed manifest",
                tofile="recomputed manifest",
                n=2,
            )
        )
        raise AuditFailure("SHA-256 manifest drift:\n" + difference[:8000])


def scan_sources(paths: set[Path]) -> None:
    failures: list[str] = []
    for path in sorted(paths):
        source = path.read_text(encoding="utf-8-sig")
        executable = strip_comments_and_strings(source)
        for label, pattern in FORBIDDEN:
            match = pattern.search(executable)
            if match:
                line = executable.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{path.relative_to(REPO_ROOT).as_posix()}:{line}: {label}"
                )
        if ABSOLUTE_USER_PATH_RE.search(source):
            failures.append(
                f"{path.relative_to(REPO_ROOT).as_posix()}: absolute user path"
            )
    if failures:
        raise AuditFailure("forbidden source content:\n  - " + "\n  - ".join(failures))


def source_statistics(closure: set[Path]) -> tuple[int, int]:
    byte_count = sum(path.stat().st_size for path in closure)
    line_count = 0
    for path in closure:
        line_count += len(path.read_text(encoding="utf-8-sig").splitlines())
    return byte_count, line_count


def run(write_manifest: bool) -> None:
    closure = import_closure(ENTRY)
    disk_modules = set(MODULE_ROOT.rglob("*.lean"))
    missing_from_disk = closure - disk_modules
    extras = disk_modules - closure
    if missing_from_disk or extras:
        details: list[str] = []
        if missing_from_disk:
            details.append(f"{len(missing_from_disk)} closure files missing")
        if extras:
            sample = ", ".join(
                path.relative_to(REPO_ROOT).as_posix()
                for path in sorted(extras)[:10]
            )
            details.append(f"{len(extras)} extra modules ({sample})")
        raise AuditFailure("; ".join(details))

    scan_sources(closure | {LEAN_PROJECT / "Fuglede.lean"})
    inputs = release_inputs(closure)
    expected_manifest = manifest_text(inputs)

    if write_manifest:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(expected_manifest, encoding="utf-8", newline="\n")
    else:
        verify_manifest(expected_manifest)

    byte_count, line_count = source_statistics(closure)
    print("PASS: exact Z/180Z release closure authenticated")
    print(f"Lean modules: {len(closure):,}")
    print(f"Lean source bytes: {byte_count:,}")
    print(f"Lean source lines: {line_count:,}")
    print(f"Authenticated release inputs: {len(inputs):,}")
    print(f"Manifest: {MANIFEST.relative_to(REPO_ROOT).as_posix()}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-manifest",
        action="store_true",
        help="rewrite the deterministic SHA-256 manifest instead of checking it",
    )
    args = parser.parse_args()
    try:
        run(args.write_manifest)
    except (AuditFailure, OSError, UnicodeError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
