#!/usr/bin/env python3
"""Generate and verify the 49 unit-only K30 trace rejection leaves (V91)."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "fuglede_lean" / "Fuglede"
CORE = LEAN_DIR / "Z180K30ExceptionalUnitTraceClassifierCoreV91.lean"
AGGREGATE = LEAN_DIR / "Z180K30ExceptionalUnitTraceClassifierV91.lean"
MANIFEST = ROOT / "certificates" / "z180_k30_unit_trace_classifier_v91.json"

COMPATIBLE_ROW = {0: 7, 1: 7, 2: 4, 3: 7, 4: 2, 5: 7, 6: 7}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def leaf_name(o: int, r: int) -> str:
    return f"Z180K30ExceptionalUnitTraceRejectV91O{o}R{r}.lean"


def theorem_name(o: int, r: int) -> str:
    return f"z180_k30_unit_trace_reject_v91_o{o}_r{r}"


def row_name(o: int) -> str:
    return f"Z180K30ExceptionalUnitTraceRowClassifierV91O{o}.lean"


def row_theorem_name(o: int) -> str:
    return f"z180_k30_unit_trace_row_classifier_v91_o{o}"


def leaf_source(o: int, r: int) -> str:
    return f"""import Fuglede.Z180K30ExceptionalUnitTraceClassifierCoreV91

namespace Fuglede.Z180K30ExceptionalRawV2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem {theorem_name(o, r)} :
    z180K30UnitTraceRejectAuditV91 ({o} : Fin 7) ({r} : Fin 8) = true := by
  decide

#print axioms {theorem_name(o, r)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def row_source(o: int) -> str:
    compatible = COMPATIBLE_ROW[o]
    imports = "\n".join(
        f"import Fuglede.Z180K30ExceptionalUnitTraceRejectV91O{o}R{r}"
        for r in range(8)
        if r != compatible
    )
    branches = []
    for r in range(8):
        if r == compatible:
            branches.append("  · rfl")
        else:
            branches.append(
                "  · exact\n"
                "      (z180K30UnitTraceRejectAudit_semanticsV91\n"
                f"        ({o} : Fin 7) ({r} : Fin 8)\n"
                f"        {theorem_name(o, r)}\n"
                "        unit hunit htrace).elim"
            )
    return f"""{imports}

namespace Fuglede.Z180K30ExceptionalRawV2

theorem {row_theorem_name(o)}
    (r : Fin 8) (unit : RawPoint) (hunit : unit ∈ units36)
    (htrace :
      gramTraceSquare
          (affineSet unit 0 (z180K30ExceptionalOrbitColumnV4 r))
          (z180K30ExceptionalOrbitColumnV4
            (z180K30NonHOrbitV78Fix2 ({o} : Fin 7))) =
        scalarCoeff 936) :
    r = z180K30CompatibleRowOrbitV78Fix2 ({o} : Fin 7) := by
  fin_cases r
{chr(10).join(branches)}

#print axioms {row_theorem_name(o)}

end Fuglede.Z180K30ExceptionalRawV2
"""


def expected_files() -> dict[Path, bytes]:
    files: dict[Path, bytes] = {}
    for o in range(7):
        for r in range(8):
            if r != COMPATIBLE_ROW[o]:
                files[LEAN_DIR / leaf_name(o, r)] = leaf_source(o, r).encode()
        files[LEAN_DIR / row_name(o)] = row_source(o).encode()
    return files


def manifest_payload(files: dict[Path, bytes]) -> bytes:
    leaves = []
    for o in range(7):
        for r in range(8):
            if r == COMPATIBLE_ROW[o]:
                continue
            path = LEAN_DIR / leaf_name(o, r)
            leaves.append(
                {
                    "column_orbit": o,
                    "row_orbit": r,
                    "unit_cases": 12,
                    "file": path.relative_to(ROOT).as_posix(),
                    "sha256": sha256(files[path]),
                    "theorem": theorem_name(o, r),
                }
            )
    rows = []
    for o in range(7):
        path = LEAN_DIR / row_name(o)
        rows.append(
            {
                "column_orbit": o,
                "compatible_row_orbit": COMPATIBLE_ROW[o],
                "file": path.relative_to(ROOT).as_posix(),
                "sha256": sha256(files[path]),
                "theorem": row_theorem_name(o),
            }
        )
    payload = {
        "schema": "z180-k30-unit-trace-classifier-v91-1",
        "core": {
            "file": CORE.relative_to(ROOT).as_posix(),
            "sha256": sha256(CORE.read_bytes()),
        },
        "aggregate": {
            "file": AGGREGATE.relative_to(ROOT).as_posix(),
            "sha256": sha256(AGGREGATE.read_bytes()),
        },
        "leaf_count": len(leaves),
        "unit_cases_per_leaf": 12,
        "total_unit_cases": 12 * len(leaves),
        "compatible_rows": [COMPATIBLE_ROW[o] for o in range(7)],
        "leaves": leaves,
        "row_aggregates": rows,
    }
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode()


def write_all() -> None:
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
    print("V91 source scan PASS: 49 leaves, 588 unit cases, 7 row aggregates")


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
