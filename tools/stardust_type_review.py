"""Build selected Foundation modules and print explicit declaration types for review.

PRELIMINARY ONLY: never substitutes for the full root build, complete transitive
axiom audit, final public-type/proof review, source-integrity checks or sync receipt.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def snapshot() -> dict[str, str]:
    paths = list((ROOT / "Foundation").rglob("*.lean"))
    paths += list((ROOT / "OperatorDerivativeRewrite").rglob("*.lean"))
    paths += [ROOT / p for p in ["OperatorDerivativeRewrite.lean", "lakefile.toml",
              "lake-manifest.json", "lean-toolchain", "tools/stardust_type_review.py"]]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest().upper()
            for p in sorted(set(paths))}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", required=True, help="Fresh output directory inside .lake")
    parser.add_argument("--module", required=True, action="append")
    parser.add_argument("--declaration", required=True, action="append")
    args = parser.parse_args()
    for values, prefix in [(args.module, "Foundation."),
                           (args.declaration, "OperatorDerivativeRewrite.Foundation.")]:
        for name in values:
            if not name.startswith(prefix) or not re.fullmatch(r"[\w'.]+", name):
                parser.error("Supply fully qualified Foundation module/declaration names")
    for module in args.module:
        path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if not path.is_file():
            parser.error(f"Module source missing: {module}")
    out = (ROOT / args.run_dir).resolve()
    if not out.is_relative_to(ROOT / ".lake"):
        parser.error("Output must stay inside workspace .lake")
    out.mkdir(parents=True, exist_ok=False)
    before = snapshot()
    pinned = (ROOT / "lean-toolchain").read_text().strip()
    lake = Path.home() / ".elan" / "toolchains" / pinned.replace("/", "--").replace(":", "---") / "bin/lake.exe"
    source = out / "types.lean"
    source.write_text("\n".join("import " + m for m in dict.fromkeys(args.module)) + "\n" +
                      "\n".join("#check @" + n for n in args.declaration) + "\n", encoding="utf-8")
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    rows = []
    start = time.perf_counter()
    result = dict(kind="PRELIMINARY_TYPE_REVIEW_ONLY", checkpoint_eligible=False,
                  started_utc=datetime.now(timezone.utc).isoformat(), status="RUNNING",
                  modules=args.module, declarations=args.declaration, stages=rows)
    lock = ROOT / ".lake" / "stardust-verification.lock"
    fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    os.write(fd, f"pid={os.getpid()}\n".encode())
    os.close(fd)
    try:
        for label, cmd in [("target-build", [str(lake), "build", *dict.fromkeys(args.module)]),
                           ("types", [str(lake), "env", "lean", str(source)])]:
            tick = time.perf_counter()
            with (out / (label + ".log")).open("wb") as log:
                process = subprocess.run(cmd, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            rows.append(dict(stage=label, wall_seconds=round(time.perf_counter()-tick, 3),
                             exit_code=process.returncode, command=cmd))
            if process.returncode:
                raise RuntimeError(f"{label} failed; inspect {out / (label+'.log')}")
        if before != snapshot() or hashlib.sha256(source.read_bytes()).hexdigest() != source_hash:
            raise RuntimeError("Inputs changed during review; discard this result")
        result.update(status="PRELIMINARY_PASSED", inputs_sha256=before, generated_types_sha256=source_hash)
        print(f"Preliminary types ready: {out / 'types.log'}")
        print("Full root build, axiom audit and final human review remain required.")
    except Exception as ex:
        result.update(status="FAILED", error=f"{type(ex).__name__}: {ex}")
        raise
    finally:
        lock.unlink()
        result["wall_seconds"] = round(time.perf_counter()-start, 3)
        (out / "review.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
