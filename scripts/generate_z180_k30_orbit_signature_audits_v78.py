#!/usr/bin/env python3
"""Generate and verify the 56 coupled K30 orbit-signature audit leaves.

The generated Lean modules are intentionally tiny: every leaf imports the
shared V78 core and certifies one `(column orbit, row orbit)` Boolean audit.
Generation is deterministic (UTF-8, LF endings, sorted JSON keys).
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "fuglede_lean" / "Fuglede"
CORE = LEAN_DIR / "Z180K30ExceptionalOrbitSignatureAuditV78.lean"
MANIFEST = ROOT / "certificates" / "z180_k30_orbit_signature_audits_v78.json"

ACCEPTED_432 = {
    (0, 7),
    (1, 7),
    (2, 4),
    (3, 7),
    (4, 2),
    (5, 7),
    (6, 7),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def leaf_name(o: int, r: int) -> str:
    return f"Z180K30ExceptionalOrbitSignatureAuditV78O{o}R{r}.lean"


def theorem_name(o: int, r: int) -> str:
    return f"z180_k30_exceptional_orbit_signature_audit_v78_o{o}_r{r}"


def leaf_source(o: int, r: int) -> str:
    accepted = 432 if (o, r) in ACCEPTED_432 else 0
    return f"""import Fuglede.Z180K30ExceptionalOrbitSignatureAuditV78

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem {theorem_name(o, r)} :
    z180K30OrbitSignatureAuditV78 ({o} : Fin 8) ({r} : Fin 8) =
      {{ enumerated := 432, accepted := {accepted}, uncovered := 0 }} := by
  decide

#print axioms {theorem_name(o, r)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def expected_files() -> dict[Path, bytes]:
    return {
        LEAN_DIR / leaf_name(o, r): leaf_source(o, r).encode("utf-8")
        for o in range(7)
        for r in range(8)
    }


def manifest_payload(files: dict[Path, bytes]) -> bytes:
    leaves = []
    for o in range(7):
        for r in range(8):
            path = LEAN_DIR / leaf_name(o, r)
            data = files[path]
            leaves.append(
                {
                    "accepted": 432 if (o, r) in ACCEPTED_432 else 0,
                    "column_orbit": o,
                    "enumerated": 432,
                    "file": path.relative_to(ROOT).as_posix(),
                    "row_orbit": r,
                    "sha256": sha256(data),
                    "theorem": theorem_name(o, r),
                    "uncovered": 0,
                }
            )
    payload = {
        "core": {
            "file": CORE.relative_to(ROOT).as_posix(),
            "sha256": sha256(CORE.read_bytes()),
        },
        "generator": {
            "file": Path(__file__).resolve().relative_to(ROOT).as_posix(),
            "sha256": sha256(Path(__file__).read_bytes()),
        },
        "leaf_count": 56,
        "leaves": leaves,
        "schema": "z180-k30-orbit-signature-audit-v78-1",
        "totals": {
            "accepted": 3024,
            "enumerated": 24192,
            "uncovered": 0,
        },
    }
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


def write_all() -> None:
    if not CORE.is_file():
        raise SystemExit(f"missing core module: {CORE}")
    files = expected_files()
    for path, data in files.items():
        path.write_bytes(data)
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_bytes(manifest_payload(files))


def check_all() -> None:
    files = expected_files()
    failures: list[str] = []
    for path, expected in files.items():
        if not path.is_file():
            failures.append(f"missing: {path.relative_to(ROOT)}")
        elif path.read_bytes() != expected:
            failures.append(f"content mismatch: {path.relative_to(ROOT)}")
    expected_manifest = manifest_payload(files)
    if not MANIFEST.is_file():
        failures.append(f"missing: {MANIFEST.relative_to(ROOT)}")
    elif MANIFEST.read_bytes() != expected_manifest:
        failures.append(f"content mismatch: {MANIFEST.relative_to(ROOT)}")
    if failures:
        raise SystemExit("\n".join(failures))
    print("V78 source scan PASS: 56 leaves, 24192 enumerated, 3024 accepted, 0 uncovered")


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.write:
        write_all()
    else:
        check_all()


if __name__ == "__main__":
    main()
