#!/usr/bin/env python3
"""Maintain the reduced doc-gen4 root set without Order32 certificate internals."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


IMPORT_RE = re.compile(r"^import\s+([^\s]+)", re.MULTILINE)
CERTIFICATE_PREFIX = "Smallgroups.UsefulTheorems.Order32Certificate"
NORMAL_TARGET = 'defaultTargets = ["Smallgroups"]'
DOC_TARGET = 'defaultTargets = ["SmallgroupsDocs"]'
ROOTS_BEGIN = "# BEGIN GENERATED DOC ROOTS"
ROOTS_END = "# END GENERATED DOC ROOTS"


def module_name(root: Path, source: Path) -> str:
    return ".".join(source.relative_to(root).with_suffix("").parts)


def documentation_roots(root: Path) -> tuple[list[str], int, int]:
    sources = [root / "Smallgroups.lean", *sorted((root / "Smallgroups").rglob("*.lean"))]
    modules = {module_name(root, source): source for source in sources}
    dependencies = {
        name: {
            dependency
            for dependency in IMPORT_RE.findall(source.read_text(encoding="utf-8"))
            if dependency in modules
        }
        for name, source in modules.items()
    }
    reachable: set[str] = set()
    pending = ["Smallgroups"]
    while pending:
        name = pending.pop()
        if name in reachable:
            continue
        reachable.add(name)
        pending.extend(dependencies[name] - reachable)
    excluded = {name for name in reachable if name.startswith(CERTIFICATE_PREFIX)}
    changed = True
    while changed:
        changed = False
        for name in reachable:
            imports = dependencies[name]
            if name not in excluded and imports & excluded:
                excluded.add(name)
                changed = True
    included = reachable - excluded
    imported = set().union(*(dependencies[name] & included for name in included))
    roots = sorted(included - imported)
    return roots, len(included), len(excluded)


def rendered_roots(roots: list[str]) -> str:
    lines = [ROOTS_BEGIN, "roots = ["]
    lines.extend(f'  "{name}",' for name in roots)
    lines.extend(["]", ROOTS_END])
    return "\n".join(lines)


def configured_roots_block(lakefile_text: str) -> str:
    start = lakefile_text.index(ROOTS_BEGIN)
    end = lakefile_text.index(ROOTS_END, start) + len(ROOTS_END)
    return lakefile_text[start:end]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true", help="update the generated Lake roots")
    action.add_argument("--check", action="store_true", help="check the generated Lake roots")
    action.add_argument(
        "--select-doc-target",
        action="store_true",
        help="switch the CI worktree's default Lake target to SmallgroupsDocs",
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    lakefile = root / "lakefile.toml"
    lakefile_text = lakefile.read_text(encoding="utf-8")

    if args.select_doc_target:
        if DOC_TARGET in lakefile_text:
            return 0
        if NORMAL_TARGET not in lakefile_text:
            parser.error(f"could not find {NORMAL_TARGET!r} in {lakefile}")
        lakefile.write_text(
            lakefile_text.replace(NORMAL_TARGET, DOC_TARGET, 1), encoding="utf-8"
        )
        print("selected SmallgroupsDocs as the CI documentation target")
        return 0

    roots, included, excluded = documentation_roots(root)
    expected = rendered_roots(roots)
    try:
        actual = configured_roots_block(lakefile_text)
    except ValueError:
        print("generated documentation roots markers are missing", file=sys.stderr)
        return 1
    if args.write:
        lakefile.write_text(lakefile_text.replace(actual, expected, 1), encoding="utf-8")
        print(
            f"wrote {len(roots)} documentation roots "
            f"({included} included, {excluded} excluded modules)"
        )
        return 0
    if actual != expected:
        print(
            "documentation roots are stale; run "
            "python Scripts/generate_doc_entrypoint.py --write",
            file=sys.stderr,
        )
        return 1
    print(
        f"checked {len(roots)} documentation roots "
        f"({included} included, {excluded} excluded modules)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
