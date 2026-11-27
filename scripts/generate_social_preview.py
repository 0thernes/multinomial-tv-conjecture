#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Deterministically generate docs/media/social-preview.svg from live repository metadata.

Satisfies Build Standard v1.2.0 item A05 (Demo media produced by a documented command from current
code) and A26 (Social preview image), ensuring version, audited theorem count, comparator target
count, and NonVacuity witness count can never drift out of sync.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT_SVG = ROOT / "docs" / "media" / "social-preview.svg"


def read_live_metrics() -> tuple[str, int, int, int, int]:
    version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    log_path = ROOT / "results" / "lean-axioms-all.log"
    m = re.search(r"checked\s+(\d+)\s+theorems", log_path.read_text(encoding="utf-8")) if log_path.is_file() else None
    constants = int(m.group(1)) if m else 0
    decl_re = re.compile(r"^\s*(?:(?:public|private|protected)\s+)*(?:theorem|lemma)\s+\S+", re.M)
    author_decls = 0
    for lf in sorted((ROOT / "lean").rglob("*.lean")):
        if ".lake" in lf.parts or lf.name in {"Challenge.lean", "VerifyAxioms.lean"}:
            continue
        author_decls += len(decl_re.findall(lf.read_text(encoding="utf-8")))
    nv_path = ROOT / "lean" / "MultinomialTVConjecture" / "NonVacuity.lean"
    nonvac = len(re.findall(r"^\s*theorem\s+", nv_path.read_text(encoding="utf-8"), re.M)) if nv_path.is_file() else 0
    comp = json.loads((ROOT / "lean" / "comparator.json").read_text(encoding="utf-8"))
    targets = len(comp["theorem_names"])
    return version, author_decls, constants, nonvac, targets


def render_svg() -> str:
    version, author_decls, constants, nonvac, targets = read_live_metrics()
    return f"""<svg xmlns="http://www.w3.org/2000/svg" width="1280" height="640" viewBox="0 0 1280 640" role="img" aria-label="Multinomial TV Conjecture — Lean 4.35.0 Proof of Conjecture 7.7 and Quantitative Lemma 7.3">
  <defs>
    <linearGradient id="bg" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#0b1020"/>
      <stop offset="55%" stop-color="#0f1d3a"/>
      <stop offset="100%" stop-color="#172554"/>
    </linearGradient>
    <linearGradient id="accent" x1="0" y1="0" x2="1" y2="0">
      <stop offset="0%" stop-color="#38bdf8"/>
      <stop offset="100%" stop-color="#4ade80"/>
    </linearGradient>
  </defs>
  <rect width="1280" height="640" fill="url(#bg)"/>
  <rect x="64" y="56" width="1152" height="528" rx="24" fill="#0f172a" fill-opacity="0.72" stroke="#1e3a8a" stroke-width="2"/>
  <rect x="108" y="102" width="620" height="36" rx="18" fill="#0c4a6e" stroke="#38bdf8" stroke-width="1.5"/>
  <text x="418" y="126" fill="#e0f2fe" font-family="Segoe UI, system-ui, sans-serif" font-size="16" font-weight="700" text-anchor="middle" letter-spacing="1.2">LEAN 4.35.0 (MODULE SPEC) · COMPARATOR REPLAY · V{version}</text>
  <text x="108" y="212" fill="#f8fafc" font-family="Segoe UI, system-ui, sans-serif" font-size="52" font-weight="800">Conjecture 7.7 &amp; Lemma 7.3 Proved</text>
  <text x="108" y="264" fill="#cbd5e1" font-family="Segoe UI, system-ui, sans-serif" font-size="25" font-weight="500">Second-Order Variance Constant of Multinomial Discrete Total Variation</text>
  <rect x="108" y="302" width="1064" height="106" rx="14" fill="#0b1224" stroke="#334155" stroke-width="1.5"/>
  <text x="640" y="352" fill="#38bdf8" font-family="Consolas, Menlo, monospace" font-size="30" font-weight="700" text-anchor="middle">a_△ = 1/32 − 4√3/243     ·     γ₂ = −1/(32π) − 8√3/(243π)</text>
  <text x="640" y="388" fill="#94a3b8" font-family="Consolas, Menlo, monospace" font-size="20" text-anchor="middle">b₀ = 32√3/(81π)   ·   b₁ = b₂ = −22√3/(81π)   ·   d₀ = −4√3/(81π)   ·   O(ℓ⁻²) proved</text>
  <rect x="108" y="438" width="336" height="68" rx="12" fill="#064e3b" fill-opacity="0.55" stroke="#4ade80" stroke-width="1.5"/>
  <text x="276" y="468" fill="#6ee7b7" font-family="Segoe UI, system-ui, sans-serif" font-size="18" font-weight="700" text-anchor="middle">6 Checker Runs · {targets} Targets</text>
  <text x="276" y="492" fill="#d1fae5" font-family="Segoe UI, system-ui, sans-serif" font-size="14" text-anchor="middle">Lean (paranoid/default) · lean4lean · nanoda · con-leche · con-ron</text>
  <rect x="472" y="438" width="336" height="68" rx="12" fill="#1e1b4b" fill-opacity="0.7" stroke="#818cf8" stroke-width="1.5"/>
  <text x="640" y="468" fill="#c7d2fe" font-family="Segoe UI, system-ui, sans-serif" font-size="18" font-weight="700" text-anchor="middle">{author_decls} Author Theorems ({constants} Constants)</text>
  <text x="640" y="492" fill="#e0e7ff" font-family="Segoe UI, system-ui, sans-serif" font-size="14" text-anchor="middle">Strictly [propext, Classical.choice, Quot.sound]</text>
  <rect x="836" y="438" width="336" height="68" rx="12" fill="#172554" fill-opacity="0.8" stroke="#38bdf8" stroke-width="1.5"/>
  <text x="1004" y="468" fill="#bae6fd" font-family="Segoe UI, system-ui, sans-serif" font-size="18" font-weight="700" text-anchor="middle">Exact + 80-Digit Verified</text>
  <text x="1004" y="492" fill="#e0f2fe" font-family="Segoe UI, system-ui, sans-serif" font-size="14" text-anchor="middle">{nonvac} NonVacuity theorems · Banić &amp; Elezović (2026)</text>
  <line x1="108" y1="532" x2="1172" y2="532" stroke="url(#accent)" stroke-width="2" stroke-opacity="0.5"/>
  <text x="108" y="562" fill="#94a3b8" font-family="Segoe UI, system-ui, sans-serif" font-size="17">Alexander S. Donahue · Independent Researcher · ORCID 0009-0006-8168-9648</text>
  <text x="1172" y="562" fill="#38bdf8" font-family="Consolas, monospace" font-size="17" text-anchor="end">github.com/0thernes/multinomial-tv-conjecture</text>
</svg>
"""


def main() -> int:
    OUT_SVG.parent.mkdir(parents=True, exist_ok=True)
    OUT_SVG.write_text(render_svg(), encoding="utf-8", newline="\n")
    print(f"Wrote {OUT_SVG} ({OUT_SVG.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
