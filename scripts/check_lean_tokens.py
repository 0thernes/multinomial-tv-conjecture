#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Comment- and string-aware Lean 4 forbidden-token & Palomar module-header scanner.

Single source of truth used by .github/workflows/lean-verify.yml, scripts/dev.sh,
scripts/build_site.py, scripts/generate_social_preview.py, and tests/test_repo_integrity.py.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

FORBIDDEN_RE = re.compile(
    r"\b(sorry|admit|native_decide|unsafe)\b"
    r"|decide\s*\+native"
    r"|^\s*(?:@\[[^\]]+\]\s+|public\s+|private\s+|protected\s+|noncomputable\s+)*axiom\b"
    r"|^\s*(?:public\s+|private\s+|protected\s+)*partial\s+(?:def|theorem)\b"
    r"|implemented_by|@\[extern|@\[nolint"
)

AUTHOR_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s+|(?:public|private|protected)\s+)*(?:theorem|lemma)\s+\S+",
    re.M,
)


def strip_lean_comments(src: str) -> str:
    """Strip nested Lean block comments (`/- ... -/`), line comments (`--`), and string literals."""
    out: list[str] = []
    i, n, depth, in_str = 0, len(src), 0, False
    while i < n:
        if depth > 0:
            if src[i : i + 2] == "/-":
                depth += 1
                i += 2
            elif src[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
        elif in_str:
            if src[i] == "\\" and i + 1 < n:
                i += 2
            elif src[i] == '"':
                in_str = False
                i += 1
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
        else:
            if src[i : i + 2] == "/-":
                depth = 1
                i += 2
            elif src[i : i + 2] == "--":
                while i < n and src[i] != "\n":
                    i += 1
            elif src[i] == '"':
                in_str = True
                i += 1
            else:
                out.append(src[i])
                i += 1
    return "".join(out)


def proof_module_files(lean_dir: Path | None = None) -> list[Path]:
    base = lean_dir if lean_dir is not None else ROOT / "lean"
    files = sorted((base / "MultinomialTVConjecture").rglob("*.lean"))
    for extra in (base / "MultinomialTVConjecture.lean", base / "Solution.lean"):
        if extra.is_file():
            files.append(extra)
    return files


def count_author_theorems(lean_dir: Path | None = None) -> int:
    """Count author-written `theorem` and `lemma` declarations across proof modules (comment-stripped)."""
    count = 0
    for lf in proof_module_files(lean_dir):
        cleaned = strip_lean_comments(lf.read_text(encoding="utf-8", errors="ignore"))
        count += len(AUTHOR_DECL_RE.findall(cleaned))
    return count


def scan_proof_modules(lean_dir: Path | None = None) -> list[str]:
    hits: list[str] = []
    files = proof_module_files(lean_dir)
    if len(files) < 8:
        hits.append(f"Expected >= 8 Lean proof modules, found {len(files)}")
        return hits
    for f in files:
        cleaned = strip_lean_comments(f.read_text(encoding="utf-8"))
        if not re.search(r"^\s*module\s*$", cleaned, re.M):
            hits.append(f"{f}:1: missing required Lean 4.35 module header")
        for lineno, line in enumerate(cleaned.splitlines(), 1):
            if FORBIDDEN_RE.search(line):
                hits.append(f"{f}:{lineno}: {line.strip()}")
    return hits


def main() -> int:
    hits = scan_proof_modules()
    if hits:
        print("Forbidden Lean token or missing module header detected:", file=sys.stderr)
        for h in hits:
            print(" ", h, file=sys.stderr)
        return 1
    print(
        f"PASS: 0 forbidden Lean tokens and 0 @[nolint] suppressions across "
        f"{len(proof_module_files())} proof modules ({count_author_theorems()} author theorems/lemmas)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
