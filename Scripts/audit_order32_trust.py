#!/usr/bin/env python3
"""Audit Order32 certificates and their local mathematical infrastructure.

This lexical check supplements compilation; it does not replace Lean's kernel.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


FORBIDDEN = re.compile(r"\b(bv_decide|native_decide|sorry|admit|axiom|unsafe)\b")


def lean_code(source: str) -> str:
    """Blank comments and ordinary strings, retaining offsets and line numbers.

    Lean block comments nest. Sources containing raw or interpolated strings, or
    a double-quote character literal, are checked verbatim. The latter must not
    be mistaken for the start of an ordinary string. Other character literals
    and identifier apostrophes need no special handling because they contain no
    string delimiter. This conservative fallback cannot conceal a token.
    """
    if re.search(r'!"|\br#*"', source) or any(
        literal in source for literal in ("'\"'", "'\\\"'")
    ):
        return source
    code = list(source)
    index = 0
    while index < len(source):
        start = index
        if source.startswith("--", index):
            newline = source.find("\n", index)
            index = len(source) if newline == -1 else newline
        elif source.startswith("/-", index):
            depth = 1
            index += 2
            while index < len(source) and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
        elif source[index] == '"':
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
        else:
            index += 1
            continue
        for position in range(start, min(index, len(source))):
            if source[position] != "\n":
                code[position] = " "
    return "".join(code)


def violations(source: str) -> list[tuple[int, str]]:
    code = lean_code(source)
    return [
        (code.count("\n", 0, match.start()) + 1, match.group())
        for match in FORBIDDEN.finditer(code)
    ]


def self_test() -> None:
    """Check the actual scanner before allowing it to report a clean audit."""
    for token in ("bv_decide", "native_decide", "sorry", "admit", "axiom", "unsafe"):
        if violations(f"example := by {token}\n") != [(1, token)]:
            raise RuntimeError(f"trust audit self-test failed to detect {token}")
    examples = [
        ("private axiom bad : False\npublic axiom worse : False", [(1, "axiom"), (2, "axiom")]),
        ('/- axiom /- sorry -/ unsafe -/\n-- admit\ndef s := "native_decide"', []),
        ('def s := "escaped \\" sorry"\nexample := by admit', [(2, "admit")]),
        ("/- nested\n/- sorry -/\n-/\nexample := by native_decide", [(4, "native_decide")]),
        ('def s := s!"{unsafe}"\nexample := by sorry', [(1, "unsafe"), (2, "sorry")]),
        ('def s := r#"a "quote""#\nexample := by sorry', [(2, "sorry")]),
        ('''def c : Char := '"'\nexample := by sorry''', [(2, "sorry")]),
        (r'''def c : Char := '\"' ''' + "\nexample := by admit", [(2, "admit")]),
        (r'''def c : Char := '\'' ''' + "\nexample := by sorry", [(2, "sorry")]),
        (r'''def c : Char := '\\' ''' + "\nexample := by unsafe", [(2, "unsafe")]),
        ("def x' := 0\nexample := by native_decide", [(2, "native_decide")]),
        ('''def x' := '"'\nexample := by axiom''', [(2, "axiom")]),
        ("def native_decide_extra := 0", []),
    ]
    for source, expected in examples:
        actual = violations(source)
        if actual != expected:
            raise RuntimeError(f"trust audit self-test failed: {actual!r} != {expected!r}")


def main() -> int:
    self_test()
    root = Path(__file__).resolve().parents[1]
    certificate_dir = root / "Smallgroups" / "UsefulTheorems" / "Order32Certificate"
    framework_dir = root / "Smallgroups" / "GAP" / "Polycyclic"
    generation_dir = root / "Smallgroups" / "UsefulTheorems" / "PGroupGeneration"
    certificates = sorted(certificate_dir.rglob("*.lean"))
    framework = sorted(framework_dir.rglob("*.lean"))
    generation = sorted(generation_dir.rglob("*.lean"))
    if not certificates or not generation or not (framework_dir / "PresentationHom.lean").is_file():
        print(
            "Order32 certificates, PGroupGeneration sources, or PresentationHom.lean are missing",
            file=sys.stderr,
        )
        return 1
    failures: list[str] = []
    sources = certificates + framework + generation
    for source in sources:
        for line, name in violations(source.read_text(encoding="utf-8")):
            failures.append(f"{source.relative_to(root)}:{line}: forbidden {name}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(
        f"audited {len(certificates)} Order32 certificate modules, "
        f"{len(framework)} polycyclic infrastructure modules, and "
        f"{len(generation)} PGroupGeneration modules (scanner self-test passed)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
