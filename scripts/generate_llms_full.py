#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Deterministically regenerate llms-full.txt from canonical repository documentation."""
from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

SECTIONS = [
    "README.md",
    "AGENTS.md",
    "CLAIMS.md",
    "LIMITATIONS.md",
    "REPLICATION.md",
    "ERRATA.md",
    "docs/statement-fidelity.md",
    "docs/architecture.md",
    "docs/verification.md",
    "docs/literature-search.md",
    "docs/configuration.md",
    "docs/threat-model.md",
    "docs/operations.md",
    "docs/faq.md",
    "docs/glossary.md",
]


def main() -> int:
    parts: list[str] = []
    for rel in SECTIONS:
        p = ROOT / rel
        if p.is_file():
            parts.append(f"=== {rel} ===\n\n" + p.read_text(encoding="utf-8").strip())
    out = ROOT / "llms-full.txt"
    out.write_text("\n\n---\n\n".join(parts) + "\n", encoding="utf-8", newline="\n")
    print(f"Wrote {out} ({out.stat().st_size} bytes, {len(parts)} sections)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
