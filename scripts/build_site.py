#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Assemble and link-check the static GitHub Pages portal at build/site/."""
from __future__ import annotations

import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "build" / "site"


def parse_audited_theorem_count() -> int:
    log_path = ROOT / "results" / "lean-axioms-all.log"
    if log_path.is_file():
        m = re.search(r"checked\s+(\d+)\s+theorems", log_path.read_text(encoding="utf-8", errors="ignore"))
        if m:
            return int(m.group(1))
    return 0


def parse_nonvacuity_count() -> int:
    nv_path = ROOT / "lean" / "MultinomialTVConjecture" / "NonVacuity.lean"
    if nv_path.is_file():
        return len(re.findall(r"^\s*theorem\s+", nv_path.read_text(encoding="utf-8", errors="ignore"), re.M))
    return 0


def parse_author_theorem_count() -> int:
    decl_re = re.compile(r"^\s*(?:(?:public|private|protected)\s+)*(?:theorem|lemma)\s+\S+", re.M)
    count = 0
    for lf in sorted((ROOT / "lean").rglob("*.lean")):
        if ".lake" in lf.parts or lf.name in {"Challenge.lean", "VerifyAxioms.lean"}:
            continue
        count += len(decl_re.findall(lf.read_text(encoding="utf-8", errors="ignore")))
    return count


def render_portal() -> str:
    version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    theorem_count = parse_audited_theorem_count()
    author_count = parse_author_theorem_count()
    nonvac_count = parse_nonvacuity_count()
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width,initial-scale=1"/>
  <meta http-equiv="Content-Security-Policy" content="default-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; object-src 'none'; base-uri 'self'; form-action 'none';"/>
  <title>Multinomial TV Conjecture · v{version}</title>
  <meta name="description" content="Lean 4.35.0 proof of Conjecture 7.7 and quantitative O(L^-2) Lemma 7.3 of Banić &amp; Elezović (arXiv:2610.17046v1) replayed via lake comparator --paranoid."/>
  <meta property="og:title" content="Multinomial TV Conjecture · v{version}"/>
  <meta property="og:description" content="Lean 4.35.0 (module-header Palomar spec) proof of Conjecture 7.7 and quantitative Lemma 7.3 of Banić &amp; Elezović (arXiv:2610.17046v1)."/>
  <meta property="og:image" content="media/social-preview.svg"/>
  <style>
    :root {{ color-scheme: dark; }}
    body {{ font-family: system-ui, -apple-system, Segoe UI, Roboto, sans-serif; background: #0b1020; color: #e2e8f0; margin: 0; line-height: 1.55; }}
    .skip-link {{ position: absolute; left: -9999px; top: auto; width: 1px; height: 1px; overflow: hidden; }}
    .skip-link:focus {{ position: static; width: auto; height: auto; display: inline-block; margin: .75rem 1.5rem; padding: .4rem .8rem; background: #0284c7; color: #fff; border-radius: 6px; text-decoration: none; }}
    a:focus-visible {{ outline: 2px solid #38bdf8; outline-offset: 2px; }}
    header {{ background: linear-gradient(135deg, #0f172a, #172554); border-bottom: 1px solid #1e3a8a; padding: 3rem 1.5rem 2.5rem; }}
    .wrap {{ max-width: 1020px; margin: 0 auto; }}
    .eyebrow {{ color: #38bdf8; font-size: .82rem; font-weight: 700; letter-spacing: .12em; text-transform: uppercase; }}
    h1 {{ margin: .35rem 0 .6rem; font-size: 2.2rem; color: #f8fafc; }}
    .lead {{ font-size: 1.05rem; color: #cbd5e1; max-width: 800px; }}
    .formula {{ margin: 1.2rem 0; padding: .9rem 1.1rem; border-radius: 10px; background: #0b1224; border: 1px solid #334155; font-family: ui-monospace, Consolas, monospace; color: #7dd3fc; overflow-x: auto; }}
    .pills {{ display: flex; flex-wrap: wrap; gap: .6rem; margin-top: 1.25rem; }}
    .pill {{ display: inline-block; padding: .45rem .9rem; border-radius: 999px; background: #1e293b; border: 1px solid #334155; color: #f8fafc; text-decoration: none; font-size: .88rem; font-weight: 600; }}
    .pill.primary {{ background: #0284c7; border-color: #38bdf8; }}
    main {{ padding: 2rem 1.5rem 4rem; }}
    .grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(290px, 1fr)); gap: 1.2rem; }}
    .card {{ background: #111827; border: 1px solid #1f2937; border-radius: 14px; padding: 1.3rem; }}
    .card h2 {{ margin: 0 0 .5rem; font-size: 1.15rem; color: #f8fafc; }}
    .card p {{ color: #cbd5e1; font-size: .92rem; margin: 0; }}
    .note {{ margin-top: 2rem; padding: 1rem 1.25rem; border-left: 3px solid #f59e0b; background: #172033; border-radius: 0 10px 10px 0; font-size: .9rem; color: #cbd5e1; }}
    footer {{ border-top: 1px solid #1e293b; padding: 1.5rem; text-align: center; color: #94a3b8; font-size: .85rem; }}
    footer a {{ color: #7dd3fc; text-decoration: none; }}
    @media (prefers-reduced-motion: reduce) {{ * {{ scroll-behavior: auto !important; transition: none !important; }} }}
  </style>
</head>
<body>
  <a class="skip-link" href="#main-content">Skip to main content</a>
  <header>
    <div class="wrap">
      <div class="eyebrow">Lean 4.35.0 (Palomar module spec) · Mathlib v4.35.0 · Comparator Replay · v{version}</div>
      <h1>Proof of Conjecture 7.7 &amp; Lemma 7.3 on Multinomial Discrete Total Variation</h1>
      <p class="lead">Machine-checked Lean 4.35.0 proof of Conjecture 7.7 (<code>conj:atriangle</code>) and the quantitative <em>O</em>(&ell;<sup>&minus;2</sup>) remainder of Lemma 7.3 of Banić &amp; Elezović (unrefereed arXiv v1 preprint <code>arXiv:2610.17046v1</code>; Part 5 <code>arXiv:2611.14735v1</code>, Theorem 3.10), replayed in six comparator checker runs and cross-checked in 80-digit arithmetic.</p>
      <div class="formula" role="region" aria-label="Main proved constants">a_△ = 1/32 &minus; 4&radic;3/243 &nbsp;&middot;&nbsp; &gamma;<sub>2</sub> = &minus;1/(32&pi;) &minus; 8&radic;3/(243&pi;) &nbsp;&middot;&nbsp; d<sub>0</sub> = &minus;4&radic;3/(81&pi;)</div>
      <nav class="pills" aria-label="Primary verification artifacts">
        <a class="pill primary" href="blueprint/">Interactive Lean 4 Blueprint</a>
        <a class="pill" href="paper/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf">Preprint PDF</a>
        <a class="pill" href="results/lean-axioms-all.log">Verbatim Axiom Log</a>
        <a class="pill" href="results/comparator-paranoid.log">Comparator Log (6 Runs)</a>
        <a class="pill" href="data/MANIFEST.sha256">SHA-256 Manifest</a>
        <a class="pill" href="data/MANIFEST.sha256.tsr">RFC 3161 TSA (.tsr)</a>
        <a class="pill" href="data/MANIFEST.sha256.ots">OpenTimestamps (.ots)</a>
        <a class="pill" href="https://github.com/0thernes/multinomial-tv-conjecture/blob/main/docs/statement-fidelity.md">Statement-Fidelity Audit</a>
        <a class="pill" href="https://github.com/0thernes/multinomial-tv-conjecture/blob/main/CLAIMS.md">Claims Ledger</a>
        <a class="pill" href="https://github.com/0thernes/multinomial-tv-conjecture">GitHub Repository</a>
      </nav>
    </div>
  </header>
  <main id="main-content" class="wrap">
    <div class="grid">
      <article class="card">
        <h2>Palomar Isolation &amp; 6 Comparator Runs</h2>
        <p>Every Lean file carries a Lean 4.35.0 <code>module</code> header. Isolated Mathlib-only <code>Challenge.lean</code> (10 targets) is matched against sorry-free <code>Solution.lean</code> via sandboxed <code>lake comparator --paranoid</code> (six checker runs: Lean paranoid/default, <code>lean4lean</code>, <code>nanoda</code>, <code>con-leche</code>, <code>con-ron</code>), plus standalone <code>leanchecker</code> replay of <code>NonVacuity.lean</code>.</p>
      </article>
      <article class="card">
        <h2>{theorem_count} Exhaustively Audited Constants</h2>
        <p>{author_count} author-written theorems and lemmas ({theorem_count} compiler-emitted theorem constants audited by <code>Lean.collectAxioms</code>). Zero <code>sorry</code>, <code>admit</code>, custom axioms, or <code>native_decide</code> in proof modules; strictly within <code>[propext, Classical.choice, Quot.sound]</code>.</p>
      </article>
      <article class="card">
        <h2>Non-Vacuity, Oracles &amp; Provenance</h2>
        <p>{nonvac_count} theorems in <code>NonVacuity.lean</code> (6 direct <code>hAdj 0..5</code> definition checks + 14 closed-form corollaries and proved refutations such as <code>adversarial_aTriangle_ne_one_div_32</code>), exact rational (L=3..45) &amp; 80-digit checks (&lt;3e-55), 22/22 code mutation kills, Sigstore SLSA, RFC 3161 TSA, and Bitcoin OpenTimestamps.</p>
      </article>
    </div>
    <div class="note">
      <strong>Verification &amp; Epistemic Disclosure:</strong> Unreviewed research preprint by Alexander S. Donahue (Independent Researcher, Spokane, WA, USA; ORCID <a href="https://orcid.org/0009-0006-8168-9648" style="color:#fcd34d">0009-0006-8168-9648</a>), produced with AI assistance under human direction. Source conjecture is from unrefereed arXiv v1 preprint <code>arXiv:2610.17046v1</code>. Independent human line-by-line statement-fidelity review and outside operator replication remain open; see <code>docs/statement-fidelity.md</code>, <code>REPLICATION.md</code>, and <code>LIMITATIONS.md</code>.
    </div>
  </main>
  <footer>
    Apache-2.0 (code &amp; Lean) &middot; CC-BY-4.0 (paper &amp; docs) &middot;
    <a href="https://github.com/0thernes/multinomial-tv-conjecture">Source on GitHub</a> &middot;
    <a href="blueprint/">Lean Blueprint</a>
  </footer>
</body>
</html>
"""


def verify_internal_links(site_root: Path) -> list[tuple[str, str, str]]:
    broken: list[tuple[str, str, str]] = []
    for html_file in sorted(site_root.rglob("*.html")):
        txt = html_file.read_text(encoding="utf-8", errors="ignore")
        for attr, href in re.findall(r'(href|src)="([^"]+)"', txt):
            if href.startswith(("http://", "https://", "mailto:", "#", "data:", "javascript:")):
                continue
            clean = href.split("#", 1)[0].split("?", 1)[0]
            if not clean:
                continue
            target = (site_root / clean.lstrip("/")) if clean.startswith("/") else (html_file.parent / clean).resolve()
            if not target.exists():
                broken.append((html_file.relative_to(site_root).as_posix(), attr, href))
    return broken


def main() -> int:
    SITE.mkdir(parents=True, exist_ok=True)
    (SITE / ".nojekyll").write_text("", encoding="utf-8")
    (SITE / "index.html").write_text(render_portal(), encoding="utf-8", newline="\n")

    pdf_src = ROOT / "dist" / "Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf"
    if pdf_src.is_file():
        (SITE / "paper").mkdir(parents=True, exist_ok=True)
        shutil.copy2(pdf_src, SITE / "paper" / pdf_src.name)

    for rel_src, dst_dir in (
        (ROOT / "results" / "lean-axioms-all.log", SITE / "results"),
        (ROOT / "results" / "comparator-paranoid.log", SITE / "results"),
        (ROOT / "data" / "MANIFEST.sha256", SITE / "data"),
        (ROOT / "data" / "MANIFEST.sha256.tsr", SITE / "data"),
        (ROOT / "data" / "MANIFEST.sha256.ots", SITE / "data"),
        (ROOT / "docs" / "media" / "social-preview.svg", SITE / "media"),
    ):
        if rel_src.is_file():
            dst_dir.mkdir(parents=True, exist_ok=True)
            shutil.copy2(rel_src, dst_dir / rel_src.name)

    broken = verify_internal_links(SITE)
    if broken:
        print(f"ERROR: {len(broken)} broken local link(s) in {SITE}:", file=sys.stderr)
        for page, attr, href in broken:
            print(f"  {page}: {attr}={href!r}", file=sys.stderr)
        return 1

    print(f"PASS: Static Pages site assembled & link-checked (0 broken links) at {SITE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
