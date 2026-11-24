#!/usr/bin/env python3
"""Exercise the reference source checker with complete Aethel files."""

import json
from pathlib import Path
import re
import subprocess
import sys


def main(checker: Path) -> None:
    root = Path(__file__).resolve().parents[1] / "tests" / "source-verification"
    expected = json.loads((root / "expected.json").read_text())
    actual_files = {path.name for path in root.glob("*.aethel")}
    if actual_files != set(expected):
        raise SystemExit(f"Source fixtures and expectations differ: {actual_files ^ set(expected)}")

    accepted = 0
    for name, verdict in sorted(expected.items()):
        result = subprocess.run(
            [str(checker.resolve()), "--source", str(root / name)],
            capture_output=True,
            text=True,
            timeout=10,
        )
        if isinstance(verdict, int):
            success = result.returncode == 0 and not result.stderr and (
                result.stdout == f"Source verified (u8 result: {verdict})\n"
            )
            accepted += 1
        else:
            success = result.returncode == 1 and not result.stdout and re.match(
                rf"Source verification failed: Aethel\.SourceVerification\.Error\.{verdict}\b",
                result.stderr,
            )
        if not success:
            raise SystemExit(
                f"{name}: expected {verdict!r}, got exit {result.returncode}\n"
                f"{result.stdout}{result.stderr}"
            )
    print(f"Source verification fixtures passed ({accepted} accepted, {len(expected) - accepted} rejected)")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
