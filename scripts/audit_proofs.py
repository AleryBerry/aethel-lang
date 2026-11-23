#!/usr/bin/env python3
"""Reject proof holes/declarations and audit Lean's reported dependencies.

This is an additional guard, not a replacement for kernel checking. Strip Lean
comments/strings before checking source declarations so prose does not fail it.
"""
from pathlib import Path
import re
import sys


def lean_code(source: str) -> str:
    output = []
    i, depth = 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
            output.append("\n")
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            output.append(" ")
        else:
            output.append(source[i])
            i += 1
    if depth:
        raise ValueError("unclosed Lean comment")
    return "".join(output)


def audit_source() -> None:
    root = Path(__file__).resolve().parents[1] / "aethel-lean"
    paths = [p for p in root.rglob("*.lean") if ".lake" not in p.parts]
    banned = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe)\b")
    for path in paths:
        match = banned.search(lean_code(path.read_text()))
        if match:
            raise ValueError(f"{path}: forbidden proof/trust token {match[0]}")
    print(f"Source audit passed: {len(paths)} Lean files, no proof holes or project axioms")


def audit_axioms() -> None:
    report = sys.stdin.read()
    if not report.strip():
        raise ValueError("Lean produced no axiom audit output")
    if "sorryAx" in report or re.search(r"\b(error|warning):", report):
        raise ValueError(report)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    declarations = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", report)
    for declaration in declarations:
        names = {name.strip() for name in declaration.split(",") if name.strip()}
        if names - allowed:
            raise ValueError(f"Unexpected axioms: {sorted(names - allowed)}")
    count = len(declarations) + report.count("does not depend on any axioms")
    expected = (Path(__file__).resolve().parents[1] / "aethel-lean" / "Audit.lean").read_text().count("#print axioms ")
    if count != expected:
        raise ValueError(f"Incomplete axiom audit: {count} reports for {expected} declarations\n{report}")
    print(f"Dependency audit passed: {count} declarations; only standard Lean axioms permitted")


if __name__ == "__main__":
    try:
        if sys.argv[1:] == ["--axioms"]:
            audit_axioms()
        elif not sys.argv[1:]:
            audit_source()
        else:
            raise ValueError("usage: audit_proofs.py [--axioms]")
    except ValueError as error:
        sys.exit(str(error))
