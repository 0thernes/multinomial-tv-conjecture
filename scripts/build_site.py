#!/usr/bin/env python3
"""Assemble and link-check the static GitHub Pages portal at build/site/."""
from __future__ import annotations

import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / "build" / "site"


def render_portal() -> str:
    version = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width,initial-scale=1"/>
  <title>Multinomial TV Conjecture · v{version}</title>
  <meta name="description" content="Complete Lean 4.35.0 6-kernel verified proof of Conjecture 7.7 of Banić &amp; Elezović (arXiv:2610.17046v1) on the second-order variance constant of multinomial discrete total variation."/>
  <style>
    :root {{ color-scheme: dark; }}
    body {{ font-family: system-ui, -apple-system, Segoe UI, Roboto, sans-serif; background: #0b1020; color: #e2e8f0; margin: 0; line-height: 1.55; }}
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
  </style>
</head>
<body>
  <header>
    <div class="wrap">
      <div class="eyebrow">Lean 4.35.0 · Mathlib v4.35.0 · 6-Kernel Verified · v{version}</div>
      <h1>Proof of Conjecture 7.7 on Multinomial Discrete Total Variation</h1>
      <p class="lead">Machine-checked Lean 4.35.0 resolution of Conjecture 7.7 (<code>conj:atriangle</code>) of Banić &amp; Elezović (arXiv:2610.17046v1, 2026) and its cyclic corollary (arXiv:2611.14735v1), independently checked across 6 proof kernels and 80-digit arithmetic.</p>
      <div class="formula">a_△ = 1/32 &minus; 4&radic;3/243 &nbsp;&middot;&nbsp; &gamma;<sub>2</sub> = &minus;1/(32&pi;) &minus; 8&radic;3/(243&pi;) &nbsp;&middot;&nbsp; d<sub>0</sub> = &minus;4&radic;3/(81&pi;)</div>
      <div class="pills">
        <a class="pill primary" href="blueprint/">Interactive Lean 4 Blueprint</a>
        <a class="pill" href="paper/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf">Preprint PDF</a>
        <a class="pill" href="results/lean-axioms-all.log">Verbatim Axiom Log</a>
        <a class="pill" href="results/comparator-paranoid.log">6-Kernel Comparator Log</a>
        <a class="pill" href="data/MANIFEST.sha256">SHA-256 Manifest</a>
        <a class="pill" href="https://github.com/0thernes/multinomial-tv-conjecture/blob/main/docs/statement-fidelity.md">Statement-Fidelity Audit</a>
        <a class="pill" href="https://github.com/0thernes/multinomial-tv-conjecture/blob/main/CLAIMS.md">Claims Ledger</a>
        <a class="pill" href="https://github.com/0thernes/multinomial-tv-conjecture">GitHub Repository</a>
      </div>
    </div>
  </header>
  <main class="wrap">
    <div class="grid">
      <article class="card">
        <h2>6-Kernel Isolation</h2>
        <p>Isolated Mathlib-only <code>Challenge.lean</code> (108 lines) matched against sorry-free <code>Solution.lean</code> via sandboxed <code>lake comparator --paranoid</code> (Lean 4.35.0, leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron) plus live negative kernel rejection in CI.</p>
      </article>
      <article class="card">
        <h2>576 Exhaustively Audited Theorems</h2>
        <p>Zero <code>sorry</code>, zero <code>admit</code>, zero custom axioms, zero <code>native_decide</code>, zero Batteries linter warnings. All 576 theorems under <code>MultinomialTV</code> depend strictly on <code>[propext, Classical.choice, Quot.sound]</code>.</p>
      </article>
      <article class="card">
        <h2>Non-Vacuity, Oracles &amp; Provenance</h2>
        <p>18 concrete small-L, sign, and adversarial false-constant refutation witnesses in <code>NonVacuity.lean</code>, independent exact rational (L=3..45) &amp; 80-digit <code>mpmath</code> checks (&lt;3e-55), Sigstore SLSA Rekor attestations, and DigiCert RFC 3161 timestamping.</p>
      </article>
    </div>
    <div class="note">
      <strong>Verification &amp; Epistemic Disclosure:</strong> Unreviewed research preprint by Alexander S. Donahue (Independent Researcher, Spokane, WA, USA; ORCID <a href="https://orcid.org/0009-0006-8168-9648" style="color:#fcd34d">0009-0006-8168-9648</a>), produced with AI assistance under human direction. Independent human line-by-line statement-fidelity review remains open; see <code>docs/statement-fidelity.md</code> and <code>LIMITATIONS.md</code>.
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
