"""Compile a private local draft twice, retain diagnostics, and verify PDF freshness."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--compiler", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    directory = args.directory.resolve()
    if not directory.is_relative_to(root / "manuscripts"):
        parser.error("Draft directory must be inside this repository's manuscripts directory")
    source = directory / "main.tex"
    if not source.is_file():
        parser.error("Draft main.tex is missing")
    compiler = args.compiler or shutil.which("pdflatex")
    if not compiler:
        candidate = Path(os.environ.get("LOCALAPPDATA", "")) / "Programs/MiKTeX/miktex/bin/x64/pdflatex.exe"
        compiler = candidate if candidate.is_file() else None
    if not compiler:
        parser.error("Local pdflatex not found; pass --compiler; no package installation attempted")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    build = directory / "build"
    logs = directory / "logs"
    build.mkdir(exist_ok=True)
    logs.mkdir(exist_ok=True)
    sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest().upper()
    started = time.perf_counter()
    source_hash = sha(source)
    commands = []
    result = {"started_utc": stamp, "source_sha256": source_hash,
              "compiler": str(compiler), "private_local_build": True,
              "package_installer_disabled": True, "shell_escape_disabled": True,
              "publication_or_upload": False, "status": "FAILED"}
    try:
        for number in (1, 2):
            command = [str(compiler), "-disable-installer", "-no-shell-escape",
                       "-interaction=nonstopmode", "-halt-on-error", "-file-line-error",
                       "-recorder", "-output-directory=build", "main.tex"]
            output = logs / f"{stamp}-pass{number}.stdout.log"
            with output.open("wb") as stream:
                run = subprocess.run(command, cwd=directory, stdout=stream, stderr=subprocess.STDOUT)
            commands.append({"command": command, "exit_code": run.returncode,
                             "log": str(output.relative_to(directory))})
            if (build / "main.log").is_file():
                shutil.copyfile(build / "main.log", logs / f"{stamp}-pass{number}.tex.log")
            if run.returncode:
                raise RuntimeError(f"Local LaTeX pass {number} failed; retained {output}")
        final_log = (build / "main.log").read_text(errors="replace")
        failures = re.findall(r"(?im)^.*(?:undefined references|undefined citations|(?:Reference|Citation).*undefined|multiply defined|Rerun to get cross-references right|Label\(s\) may have changed|Overfull \\[hv]box).*$", final_log)
        if failures:
            result["unresolved_diagnostics"] = failures
            raise RuntimeError("Final LaTeX log contains unresolved references or overfull boxes")
        if sha(source) != source_hash:
            raise RuntimeError("Source changed during compilation")
        output = build / "main.pdf"
        if not output.is_file() or output.stat().st_size == 0:
            raise RuntimeError("Compiler did not create a nonempty PDF")
        shutil.copyfile(output, directory / "main.pdf")
        result.update(status="COMPILED_PENDING_VISUAL_REVIEW", pdf_sha256=sha(directory / "main.pdf"),
                      references_resolved=True, overfull_boxes=False)
    except Exception as error:
        result["error"] = str(error)
        print(str(error), file=sys.stderr)
    finally:
        result.update(commands=commands, wall_seconds=time.perf_counter()-started,
                      completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        (directory / "build-status.json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
        (logs / f"{stamp}-build-status.json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "wall_seconds": result["wall_seconds"],
                      "metadata": str(directory / "build-status.json")}))
    return 0 if result["status"] == "COMPILED_PENDING_VISUAL_REVIEW" else 1


if __name__ == "__main__":
    sys.exit(main())
