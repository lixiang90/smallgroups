#!/usr/bin/env python3
"""Build Order32 certificates with memory-aware topological batching.

The measured high-memory orbit-forest and PC-alignment checks remain isolated in one
Lake process each. All other modules are submitted in small, bounded topological batches
to avoid paying for hundreds of Lake startups while retaining the low-memory policy.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path


IMPORT_RE = re.compile(r"^import\s+([^\s]+)", re.MULTILINE)
ISOLATED_MODULE_RE = re.compile(r"\.CoverageOrbitParent\d+ForestPart\d+$")


@dataclass(frozen=True)
class BuildBatch:
    kind: str
    modules: tuple[str, ...]


def module_name(root: Path, source: Path) -> str:
    return ".".join(source.relative_to(root).with_suffix("").parts)


def certificate_sources(root: Path) -> dict[str, Path]:
    cert_dir = root / "Smallgroups" / "UsefulTheorems" / "Order32Certificate"
    return {
        module_name(root, source): source
        for source in sorted(cert_dir.glob("*.lean"))
    }


def ordered_modules(sources: dict[str, Path]) -> list[str]:
    dependencies: dict[str, set[str]] = {}
    for name, source in sources.items():
        imports = set(IMPORT_RE.findall(source.read_text(encoding="utf-8")))
        dependencies[name] = {dependency for dependency in imports if dependency in sources}

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

    for name in sorted(sources):
        visit(name)
    return result


def build_batches(
    sources: dict[str, Path], modules: list[str], batch_size: int
) -> list[BuildBatch]:
    batches: list[BuildBatch] = []
    bounded: list[str] = []

    def flush_bounded() -> None:
        if bounded:
            batches.append(BuildBatch("bounded", tuple(bounded)))
            bounded.clear()

    for name in modules:
        source = sources[name].read_text(encoding="utf-8")
        if ISOLATED_MODULE_RE.search(name) or "mulEquivOfDecide" in source:
            flush_bounded()
            batches.append(BuildBatch("isolated", (name,)))
        else:
            bounded.append(name)
            if len(bounded) == batch_size:
                flush_bounded()
    flush_bounded()
    return batches


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    parser.add_argument(
        "--dry-run", action="store_true", help="print the build batches without building"
    )
    parser.add_argument(
        "--from-module",
        help="skip modules before this exact module name (useful when resuming a local run)",
    )
    parser.add_argument(
        "--batch-size",
        "--light-batch-size",
        dest="batch_size",
        type=int,
        default=4,
        help="maximum non-isolated modules per Lake invocation (default: 4)",
    )
    parser.add_argument(
        "--timings-json",
        type=Path,
        help="write per-batch wall-clock timings and the scheduler inventory as JSON",
    )
    args = parser.parse_args()
    if args.batch_size < 1:
        parser.error("--batch-size must be positive")

    root = Path(__file__).resolve().parents[1]
    sources = certificate_sources(root)
    modules = ordered_modules(sources)
    if args.from_module:
        try:
            modules = modules[modules.index(args.from_module) :]
        except ValueError:
            parser.error(f"unknown --from-module value: {args.from_module}")
    batches = build_batches(sources, modules, args.batch_size)

    results: list[dict[str, object]] = []
    isolated_count = sum(batch.kind == "isolated" for batch in batches)
    timing_path = args.timings_json
    if timing_path and not timing_path.is_absolute():
        timing_path = root / timing_path

    def write_report(status: str, elapsed: float) -> None:
        if not timing_path:
            return
        timing_path.parent.mkdir(parents=True, exist_ok=True)
        timing_path.write_text(
            json.dumps(
                {
                    "status": status,
                    "dry_run": args.dry_run,
                    "batch_size": args.batch_size,
                    "module_count": len(modules),
                    "lake_invocation_count": len(batches),
                    "isolated_invocation_count": isolated_count,
                    "bounded_invocation_count": len(batches) - isolated_count,
                    "total_elapsed_seconds": round(elapsed, 3),
                    "batches": results,
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )

    total_start = time.perf_counter()
    write_report("running", 0.0)
    for index, batch in enumerate(batches, 1):
        label = batch.modules[0] if len(batch.modules) == 1 else f"{len(batch.modules)} modules"
        print(f"[{index}/{len(batches)}] {batch.kind}: {label}", flush=True)
        batch_start = time.perf_counter()
        failure = None
        if not args.dry_run:
            try:
                subprocess.run([args.lake, "build", *batch.modules], cwd=root, check=True)
            except subprocess.CalledProcessError as error:
                failure = error
        elapsed = time.perf_counter() - batch_start
        results.append(
            {
                "index": index,
                "kind": batch.kind,
                "modules": list(batch.modules),
                "status": "failed" if failure else "success",
                "elapsed_seconds": round(elapsed, 3),
            }
        )
        write_report(
            "failed" if failure else "running", time.perf_counter() - total_start
        )
        print(f"  completed in {elapsed:.3f}s", flush=True)
        if failure:
            raise failure

    total_elapsed = time.perf_counter() - total_start
    print(
        f"Built {len(modules)} modules in {len(batches)} Lake invocations "
        f"({isolated_count} isolated, {len(batches) - isolated_count} bounded batches) "
        f"in {total_elapsed:.3f}s.",
        flush=True,
    )
    write_report("success", total_elapsed)
    if timing_path:
        print(f"Wrote timings to {timing_path}", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as error:
        sys.exit(error.returncode)
