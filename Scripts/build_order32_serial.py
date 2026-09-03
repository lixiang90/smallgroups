#!/usr/bin/env python3
"""Build Order32 certificate modules in dependency order, one Lake process at a time.

Lake 5 schedules independent module jobs concurrently and does not expose a job-count
flag.  The generated Order32 certificates contain several kernel-intensive finite checks;
letting all independent checks start together can exceed a GitHub runner's memory.  This
script keeps that resource policy outside the mathematical import graph.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path


IMPORT_RE = re.compile(r"^import\s+([^\s]+)", re.MULTILINE)
PREFIX = "Smallgroups.UsefulTheorems.Order32Certificate."


def module_name(root: Path, source: Path) -> str:
    return ".".join(source.relative_to(root).with_suffix("").parts)


def ordered_modules(root: Path) -> list[str]:
    cert_dir = root / "Smallgroups" / "UsefulTheorems" / "Order32Certificate"
    sources = sorted(cert_dir.glob("*.lean"))
    modules = {module_name(root, source): source for source in sources}
    dependencies: dict[str, set[str]] = {}
    for name, source in modules.items():
        imports = set(IMPORT_RE.findall(source.read_text(encoding="utf-8")))
        dependencies[name] = {dep for dep in imports if dep in modules}

    result: list[str] = []
    temporary: set[str] = set()
    permanent: set[str] = set()

    def visit(name: str) -> None:
        if name in permanent:
            return
        if name in temporary:
            raise RuntimeError(f"cycle in Order32 certificate imports at {name}")
        temporary.add(name)
        for dependency in sorted(dependencies[name]):
            visit(dependency)
        temporary.remove(name)
        permanent.add(name)
        result.append(name)

    for name in sorted(modules):
        visit(name)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    parser.add_argument(
        "--dry-run", action="store_true", help="print the topological order without building"
    )
    parser.add_argument(
        "--from-module",
        help="skip modules before this exact module name (useful when resuming a local run)",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    modules = ordered_modules(root)
    if args.from_module:
        try:
            modules = modules[modules.index(args.from_module) :]
        except ValueError:
            parser.error(f"unknown --from-module value: {args.from_module}")

    for index, name in enumerate(modules, 1):
        print(f"[{index}/{len(modules)}] {name}", flush=True)
        if not args.dry_run:
            subprocess.run([args.lake, "build", name], cwd=root, check=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
