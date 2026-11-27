#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Validate every \\lean{...} declaration in blueprint/src/content.tex against lean/
and build an interactive SVG DAG + searchable HTML/JSON Lean 4 Blueprint with direct
GitHub line links at build/site/blueprint/.
"""
from __future__ import annotations

import html
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
TEX_PATH = ROOT / "blueprint" / "src" / "content.tex"
LEAN_DIR = ROOT / "lean"
OUT_DIR = ROOT / "build" / "site" / "blueprint"
REPO_BLOB_BASE = "https://github.com/0thernes/multinomial-tv-conjecture/blob/main/lean"

SEC_OR_ENV_RE = re.compile(
    r"\\section\{([^}]+)\}|\\begin\{(theorem|lemma|proposition|corollary|definition)\}(?:\[([^\]]*)\])?(.*?)\\end\{\2\}",
    re.S,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
LEAN_RE = re.compile(r"\\lean\{([^}]+)\}")
USES_RE = re.compile(r"\\uses\{([^}]+)\}")
DECL_LINE_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s+|public\s+|private\s+|noncomputable\s+|protected\s+)*(?:theorem|lemma|def|structure|abbrev|inductive|instance)\s+([A-Za-z0-9_.']+)"
)
NS_LINE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.]+)\s*$")
END_LINE_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.]+))?\s*$")


def index_lean_declarations() -> tuple[dict[str, tuple[str, int]], dict[str, tuple[str, int]]]:
    """Index all Lean declarations under lean/ (preferring proof modules over Challenge stubs)."""
    exact: dict[str, tuple[str, int]] = {}
    short_map: dict[str, tuple[str, int]] = {}
    lean_files = sorted(
        f for f in LEAN_DIR.rglob("*.lean") if ".lake" not in f.parts and f.name != "Challenge.lean"
    )
    for lean_file in lean_files:
        rel = lean_file.relative_to(LEAN_DIR).as_posix()
        text = lean_file.read_text(encoding="utf-8", errors="replace")
        ns_stack: list[list[str]] = []
        for lineno, line in enumerate(text.splitlines(), 1):
            nm = NS_LINE_RE.match(line)
            if nm:
                ns_stack.append(nm.group(1).split("."))
                continue
            em = END_LINE_RE.match(line)
            if em and ns_stack:
                target = em.group(1)
                if target is None:
                    ns_stack.pop()
                else:
                    parts = target.split(".")
                    if ns_stack[-1] == parts:
                        ns_stack.pop()
                    else:
                        flat = [p for frame in ns_stack for p in frame]
                        if len(flat) >= len(parts) and flat[-len(parts) :] == parts:
                            remaining = len(parts)
                            while remaining > 0 and ns_stack:
                                top = ns_stack.pop()
                                remaining -= len(top)
                continue
            dm = DECL_LINE_RE.match(line)
            if dm:
                short = dm.group(1)
                loc = (rel, lineno)
                flat_ns = [p for frame in ns_stack for p in frame]
                full = ".".join([*flat_ns, short]) if flat_ns else short
                exact.setdefault(full, loc)
                for i in range(1, len(flat_ns)):
                    exact.setdefault(".".join([*flat_ns[i:], short]), loc)
                short_map.setdefault(short, loc)
    return exact, short_map


def resolve_decl_location(
    decl: str,
    exact: dict[str, tuple[str, int]],
    short_map: dict[str, tuple[str, int]],
) -> tuple[str, int] | None:
    if decl in exact:
        return exact[decl]
    suffix = "." + decl
    for key, loc in exact.items():
        if key.endswith(suffix):
            return loc
    short = decl.split(".")[-1]
    if short in short_map:
        return short_map[short]
    return None


def classify_stage(section: str) -> str:
    low = section.lower()
    if "stage 1" in low:
        return "stage1"
    if "stage 2" in low:
        return "stage2"
    if "stage 3" in low:
        return "stage3"
    if "stage 4" in low:
        return "stage4"
    return "stage5"


def parse_blueprint(tex: str) -> list[dict[str, Any]]:
    nodes: list[dict[str, Any]] = []
    current_section = "Stage 1"
    for m in SEC_OR_ENV_RE.finditer(tex):
        if m.group(1) is not None:
            current_section = m.group(1).strip()
            continue
        kind, title, body = m.group(2), (m.group(3) or "").strip(), m.group(4)
        label_m = LABEL_RE.search(body)
        label = label_m.group(1).strip() if label_m else f"node-{len(nodes)}"
        lean_decls: list[str] = []
        for lm in LEAN_RE.finditer(body):
            lean_decls.extend(x.strip() for x in lm.group(1).split(",") if x.strip())
        uses: list[str] = []
        for um in USES_RE.finditer(body):
            uses.extend(x.strip() for x in um.group(1).split(",") if x.strip())
        leanok = "\\leanok" in body
        prose = re.sub(r"\\(label|lean|uses)\{[^}]*\}", "", body)
        prose = prose.replace("\\leanok", "").replace("\\mathlibok", "").strip()
        prose = re.sub(r"\s+", " ", prose)
        nodes.append(
            {
                "id": label,
                "kind": kind,
                "stage": classify_stage(current_section),
                "section": current_section,
                "title": title or label,
                "lean": lean_decls,
                "uses": uses,
                "leanok": leanok,
                "summary": prose,
            }
        )
    return nodes


def plain_svg_text(text: str) -> str:
    s = text.replace(r"\&", "&").replace(r"\_", "_").replace("--", "–")
    for old, new in (
        (r"\mathrm{adj}", "adj"),
        (r"\mathrm{sumA}", "sumA"),
        (r"\mathrm{sumB}", "sumB"),
        (r"\mathrm{sumC}", "sumC"),
        (r"\pmod{3}", "(mod 3)"),
        (r"\equiv", "≡"),
        (r"\gamma_c", "γ_c"),
        (r"\gamma", "γ"),
        (r"\triangle", "△"),
    ):
        s = s.replace(old, new)
    s = s.replace("$", "").replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", s).strip()


def clean_html_math(text: str) -> str:
    parts = text.split("$")
    out: list[str] = []
    for idx, part in enumerate(parts):
        if idx % 2 == 0:
            cleaned = part.replace(r"\&", "&").replace(r"\_", "_").replace("--", "–")
            escaped = html.escape(cleaned)
            escaped = re.sub(r"\\texttt\{([^}]+)\}", r"<code>\1</code>", escaped)
            escaped = re.sub(r"`([^`]+)`", r"<code>\1</code>", escaped)
            out.append(escaped)
        else:
            out.append("$" + html.escape(part) + "$")
    return "".join(out)


def render_svg_dag(nodes: list[dict[str, Any]]) -> str:
    by_id: dict[str, dict[str, Any]] = {n["id"]: n for n in nodes}
    depth_cache: dict[str, int] = {}

    def depth(nid: str, seen: set[str]) -> int:
        if nid in depth_cache:
            return depth_cache[nid]
        if nid in seen or nid not in by_id:
            return 0
        seen2 = seen | {nid}
        deps = [u for u in by_id[nid]["uses"] if u in by_id]
        d = 0 if not deps else 1 + max(depth(u, seen2) for u in deps)
        depth_cache[nid] = d
        return d

    layers: dict[int, list[dict[str, Any]]] = {}
    for n in nodes:
        layers.setdefault(depth(n["id"], set()), []).append(n)

    max_cols = max((len(v) for v in layers.values()), default=1)
    node_w, node_h = 200, 48
    gap_x, gap_y = 22, 46
    pad_x, pad_y = 24, 24
    width = max(920, pad_x * 2 + max_cols * node_w + max(0, max_cols - 1) * gap_x)
    height = pad_y * 2 + len(layers) * node_h + max(0, len(layers) - 1) * gap_y

    coords: dict[str, tuple[float, float]] = {}
    for lvl in sorted(layers):
        row = layers[lvl]
        row_w = len(row) * node_w + max(0, len(row) - 1) * gap_x
        start_x = (width - row_w) / 2.0
        y = float(pad_y + lvl * (node_h + gap_y))
        for idx, n in enumerate(row):
            coords[n["id"]] = (float(start_x + idx * (node_w + gap_x)), y)

    stage_colors = {
        "stage1": ("#0c4a6e", "#38bdf8"),
        "stage2": ("#1e1b4b", "#818cf8"),
        "stage3": ("#4c1d95", "#c084fc"),
        "stage4": ("#14532d", "#4ade80"),
        "stage5": ("#78350f", "#fbbf24"),
    }

    edges_svg: list[str] = []
    for n in nodes:
        x2, y2 = coords[n["id"]]
        cx2, cy2 = x2 + node_w / 2.0, y2
        for u in n["uses"]:
            if u not in coords:
                continue
            x1, y1 = coords[u]
            cx1, cy1 = x1 + node_w / 2.0, y1 + node_h
            mid_y = (cy1 + cy2) / 2.0
            edges_svg.append(
                f'<path class="dag-edge" data-from="{html.escape(u)}" data-to="{html.escape(n["id"])}" '
                f'd="M {cx1:.1f} {cy1:.1f} C {cx1:.1f} {mid_y:.1f}, {cx2:.1f} {mid_y:.1f}, {cx2:.1f} {cy2:.1f}" '
                f'fill="none" stroke="#475569" stroke-width="1.5" marker-end="url(#arrow)"/>'
            )

    nodes_svg: list[str] = []
    for n in nodes:
        x, y = coords[n["id"]]
        fill, stroke = stage_colors.get(n["stage"], ("#1e293b", "#94a3b8"))
        short_title = plain_svg_text(n["title"])
        if len(short_title) > 29:
            short_title = short_title[:27].rstrip() + "…"
        sub = f'{n["kind"]} · {len(n["lean"])} Lean decls'
        nodes_svg.append(
            f'<a href="#{html.escape(n["id"])}" class="dag-node" data-id="{html.escape(n["id"])}" '
            f'data-stage="{html.escape(n["stage"])}" data-title="{html.escape(plain_svg_text(n["title"]))}">'
            f'<rect x="{x:.1f}" y="{y:.1f}" width="{node_w}" height="{node_h}" rx="9" '
            f'fill="{fill}" stroke="{stroke}" stroke-width="1.5"/>'
            f'<text x="{x + 10:.1f}" y="{y + 20:.1f}" fill="#f8fafc" font-size="11.5" font-weight="600">'
            f"{html.escape(short_title)}</text>"
            f'<text x="{x + 10:.1f}" y="{y + 36:.1f}" fill="#cbd5e1" font-size="10">'
            f"{html.escape(sub)}</text></a>"
        )

    return (
        f'<svg id="dag" viewBox="0 0 {width} {height}" width="100%" role="img" '
        f'aria-label="Interactive Lean 4 theorem dependency graph for Conjecture 7.7">'
        f'<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" '
        f'orient="auto-start-reverse"><path d="M 0 1 L 10 5 L 0 9 z" fill="#64748b"/></marker></defs>'
        f'{"".join(edges_svg)}{"".join(nodes_svg)}</svg>'
    )


def render_html(nodes: list[dict[str, Any]]) -> str:
    total_decls = sum(len(n["lean"]) for n in nodes)
    svg = render_svg_dag(nodes)
    rows: list[str] = []
    for n in nodes:
        badge = '<span class="ok">Lean 4 verified</span>' if n["leanok"] else '<span class="wip">Open</span>'
        decl_chips = [
            f'<a class="decl-link" href="{html.escape(link["url"])}" target="_blank" rel="noopener" '
            f'title="{html.escape(link["file"] + ":L" + str(link["line"]))}"><code>{html.escape(link["name"])}</code></a>'
            for link in n["lean_links"]
        ]
        decls = " ".join(decl_chips) or "<em>—</em>"
        deps = ", ".join(f'<a href="#{html.escape(u)}">{html.escape(u)}</a>' for u in n["uses"]) or "<em>root</em>"
        rows.append(
            f'<article class="card" id="{html.escape(n["id"])}" data-stage="{html.escape(n["stage"])}">'
            f'<div class="hdr"><span class="kind">{html.escape(n["kind"].upper())}</span>'
            f'<h3>{clean_html_math(n["title"])}</h3>{badge}</div>'
            f'<p class="sum">{clean_html_math(n["summary"])}</p>'
            f'<div class="meta"><b>Lean ({len(n["lean"])}):</b> <span class="decl-list">{decls}</span><br/>'
            f'<b>Uses:</b> {deps}</div></article>'
        )
    nonvac_node = next((n for n in nodes if n["id"] == "prop:nonvac"), None)
    nonvac_count = len(nonvac_node["lean"]) if nonvac_node is not None else 0
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"/><meta name="viewport" content="width=device-width,initial-scale=1"/>
<meta http-equiv="Content-Security-Policy" content="default-src 'self'; script-src 'self' 'unsafe-inline' https://cdnjs.cloudflare.com; style-src 'self' 'unsafe-inline'; font-src 'self' https://cdnjs.cloudflare.com data:; img-src 'self' data:; object-src 'none'; base-uri 'self'; form-action 'none';"/>
<title>Multinomial TV Conjecture · Lean 4 Dependency Blueprint</title>
<script>window.MathJax={{tex:{{inlineMath:[["$","$"]]}}}};</script>
<script defer src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-chtml-full.min.js" integrity="sha384-dCtf/9Xgzj8edI30iIEsxNfjUQ0zj2AXa3eUdgjsx8odUmpURZx5Z7aDZmV781et" crossorigin="anonymous"></script>
<style>
body{{font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif;background:#0b1020;color:#e2e8f0;margin:0;padding:1.75rem;line-height:1.5}}
main{{max-width:1240px;margin:0 auto}}
h1{{margin:0 0 .35rem;font-size:2rem;color:#f8fafc}}
.sub{{color:#94a3b8;margin-bottom:1rem}}
.toolbar{{display:flex;flex-wrap:wrap;gap:.55rem;align-items:center;margin-bottom:1rem}}
.search{{flex:1;min-width:220px;padding:.48rem .8rem;border-radius:8px;border:1px solid #334155;background:#0f172a;color:#f8fafc;font-size:.9rem}}
.btn{{padding:.4rem .75rem;border-radius:999px;border:1px solid #334155;background:#1e293b;color:#e2e8f0;font-size:.8rem;font-weight:600;cursor:pointer}}
.btn.active{{background:#0284c7;border-color:#38bdf8;color:#fff}}
.legend{{display:flex;flex-wrap:wrap;gap:.9rem;font-size:.78rem;color:#94a3b8;margin-bottom:.75rem}}
.swatch{{display:inline-block;width:10px;height:10px;border-radius:3px;margin-right:.3rem;vertical-align:middle}}
.dag-wrap{{background:#0f172a;border:1px solid #1e293b;border-radius:14px;padding:.75rem;overflow-x:auto;margin-bottom:1.5rem}}
.dag-node{{cursor:pointer;transition:opacity .15s}}
.dag-edge{{transition:opacity .15s,stroke .15s,stroke-width .15s}}
.dim{{opacity:.16}}
.dag-edge.hi{{stroke:#38bdf8;stroke-width:2.5;opacity:1}}
.grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(350px,1fr));gap:1rem}}
.card{{background:#131c33;border:1px solid #23304f;border-radius:12px;padding:1rem;transition:border-color .15s,opacity .15s}}
.card.selected,.card:target{{border-color:#38bdf8;box-shadow:0 0 0 2px rgba(56,189,248,.35)}}
.card.hidden{{display:none}}
.hdr{{display:flex;flex-wrap:wrap;align-items:center;gap:.5rem;margin-bottom:.45rem}}
.hdr h3{{margin:0;font-size:1.02rem;flex:1;color:#f8fafc}}
.kind{{font-size:.68rem;font-weight:700;padding:.15rem .45rem;border-radius:6px;background:#1e293b;color:#38bdf8}}
.ok{{font-size:.7rem;font-weight:700;padding:.15rem .5rem;border-radius:999px;background:#064e3b;color:#6ee7b7}}
.wip{{font-size:.7rem;font-weight:700;padding:.15rem .5rem;border-radius:999px;background:#451a03;color:#fcd34d}}
.sum{{font-size:.87rem;color:#cbd5e1;margin:.35rem 0 .65rem}}
.sum code{{background:#0f172a;border:1px solid #1e293b;padding:.06rem .28rem;border-radius:4px;color:#7dd3fc}}
.meta{{font-size:.78rem;color:#94a3b8;overflow-wrap:anywhere}}
.decl-list{{display:inline-flex;flex-wrap:wrap;gap:.25rem;vertical-align:middle}}
.decl-link code{{background:#0f172a;border:1px solid #1e293b;padding:.08rem .32rem;border-radius:4px;color:#7dd3fc}}
a{{color:#38bdf8;text-decoration:none}}
a:focus-visible,.btn:focus-visible,.search:focus-visible{{outline:2px solid #38bdf8;outline-offset:2px}}
.skip-link{{position:absolute;left:-9999px;top:auto;width:1px;height:1px;overflow:hidden}}
.skip-link:focus{{position:static;width:auto;height:auto;display:inline-block;padding:.35rem .7rem;margin-bottom:.75rem;background:#0284c7;color:#fff;border-radius:6px}}
.status{{font-size:.82rem;color:#94a3b8;margin-bottom:.65rem}}
@media (prefers-reduced-motion: reduce){{.dag-node,.dag-edge,.card{{transition:none}}}}
</style></head><body>
<a class="skip-link" href="#cards">Skip to theorem cards</a>
<main id="main">
<p><a href="../">&larr; Back to Multinomial TV Conjecture Portal</a></p>
<h1>Lean 4.35.0 Dependency Blueprint (Conjecture 7.7)</h1>
<p class="sub">{len(nodes)} formal nodes &middot; {total_decls} statically validated Lean 4 declarations linked to exact GitHub source lines across <code>MultinomialTVConjecture</code>, <code>NonVacuity</code> ({nonvac_count}/{nonvac_count}), and the Comparator Bridge (six checker runs). Click any DAG node to highlight its transitive dependency cone.</p>
<div class="toolbar" role="region" aria-label="Blueprint filters">
  <input id="q" class="search" type="search" placeholder="Filter nodes or Lean declarations (e.g., hAdj_mod0, NonVacuity, conjecture_7_7)..." aria-label="Filter blueprint nodes"/>
  <button class="btn active" data-stage="all" aria-pressed="true">All ({len(nodes)})</button>
  <button class="btn" data-stage="stage1" aria-pressed="false">Stage 1</button>
  <button class="btn" data-stage="stage2" aria-pressed="false">Stage 2</button>
  <button class="btn" data-stage="stage3" aria-pressed="false">Stage 3</button>
  <button class="btn" data-stage="stage4" aria-pressed="false">Stage 4</button>
  <button class="btn" data-stage="stage5" aria-pressed="false">Stage 5</button>
  <button class="btn" id="reset">Reset Cone</button>
</div>
<div id="status" class="status" role="status" aria-live="polite">Showing {len(nodes)} of {len(nodes)} formal nodes.</div>
<div class="legend">
  <span><i class="swatch" style="background:#38bdf8"></i>Stage 1: 2D&rarr;1D Combinatorial</span>
  <span><i class="swatch" style="background:#818cf8"></i>Stage 2: Stirling &amp; Euler&ndash;Maclaurin</span>
  <span><i class="swatch" style="background:#c084fc"></i>Stage 3: Local Asymptotics</span>
  <span><i class="swatch" style="background:#4ade80"></i>Stage 4: Conjecture 7.7 &amp; &gamma;(n)</span>
  <span><i class="swatch" style="background:#fbbf24"></i>Stage 5: Non-Vacuity &amp; Comparator Bridge</span>
</div>
<section class="dag-wrap">{svg}</section>
<section class="grid" id="cards">{"".join(rows)}</section>
</main>
<script>
(() => {{
  const dagNodes = [...document.querySelectorAll('.dag-node')];
  const dagEdges = [...document.querySelectorAll('.dag-edge')];
  const cards = [...document.querySelectorAll('.card')];
  const parents = {{}}, children = {{}};
  dagEdges.forEach(e => {{
    const u = e.dataset.from, v = e.dataset.to;
    (parents[v] ||= []).push(u);
    (children[u] ||= []).push(v);
  }});
  function cone(start) {{
    const keep = new Set([start]);
    const walk = (adj) => {{
      const stack = [start];
      while (stack.length) {{
        const cur = stack.pop();
        for (const nxt of (adj[cur] || [])) {{
          if (!keep.has(nxt)) {{ keep.add(nxt); stack.push(nxt); }}
        }}
      }}
    }};
    walk(parents); walk(children);
    return keep;
  }}
  let activeId = null, activeStage = 'all';
  function apply() {{
    const term = document.getElementById('q').value.trim().toLowerCase();
    const keep = activeId ? cone(activeId) : null;
    dagNodes.forEach(n => {{
      const id = n.dataset.id;
      const stageOk = activeStage === 'all' || n.dataset.stage === activeStage;
      const inCone = !keep || keep.has(id);
      n.classList.toggle('dim', !(stageOk && inCone));
    }});
    dagEdges.forEach(e => {{
      const u = e.dataset.from, v = e.dataset.to;
      const on = keep ? (keep.has(u) && keep.has(v)) : false;
      e.classList.toggle('hi', on);
      e.classList.toggle('dim', keep ? !on : false);
    }});
    let visible = 0;
    cards.forEach(c => {{
      const stageOk = activeStage === 'all' || c.dataset.stage === activeStage;
      const textOk = !term || c.textContent.toLowerCase().includes(term);
      const coneOk = !keep || keep.has(c.id);
      const show = stageOk && textOk && coneOk;
      c.classList.toggle('hidden', !show);
      c.classList.toggle('selected', c.id === activeId);
      if (show) visible += 1;
    }});
    const st = document.getElementById('status');
    if (st) st.textContent = `Showing ${{visible}} of ${{cards.length}} formal nodes${{activeId ? ' (dependency cone: ' + activeId + ')' : ''}}.`;
  }}
  const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  dagNodes.forEach(n => n.addEventListener('click', (ev) => {{
    const id = n.dataset.id;
    activeId = (activeId === id) ? null : id;
    apply();
    if (activeId) {{
      ev.preventDefault();
      document.getElementById(activeId)?.scrollIntoView({{behavior: reducedMotion ? 'auto' : 'smooth', block:'nearest'}});
    }}
  }}));
  document.querySelectorAll('.btn[data-stage]').forEach(b => b.addEventListener('click', () => {{
    activeStage = b.dataset.stage;
    document.querySelectorAll('.btn[data-stage]').forEach(x => {{
      const on = x === b;
      x.classList.toggle('active', on);
      x.setAttribute('aria-pressed', String(on));
    }});
    apply();
  }}));
  document.getElementById('q').addEventListener('input', apply);
  document.getElementById('reset').addEventListener('click', () => {{
    activeId = null; activeStage = 'all'; document.getElementById('q').value = '';
    document.querySelectorAll('.btn[data-stage]').forEach(x => {{
      const on = x.dataset.stage === 'all';
      x.classList.toggle('active', on);
      x.setAttribute('aria-pressed', String(on));
    }});
    apply();
  }});
}})();
</script>
</body></html>
"""


def main() -> int:
    if not TEX_PATH.is_file():
        print(f"ERROR: missing {TEX_PATH}", file=sys.stderr)
        return 1
    nodes = parse_blueprint(TEX_PATH.read_text(encoding="utf-8"))
    exact, short_map = index_lean_declarations()

    missing: list[tuple[str, str]] = []
    for n in nodes:
        lean_links: list[dict[str, Any]] = []
        for d in n["lean"]:
            loc = resolve_decl_location(d, exact, short_map)
            if loc is None:
                missing.append((n["id"], d))
            else:
                rel, lineno = loc
                lean_links.append(
                    {
                        "name": d,
                        "file": f"lean/{rel}",
                        "line": lineno,
                        "url": f"{REPO_BLOB_BASE}/{rel}#L{lineno}",
                    }
                )
        n["lean_links"] = lean_links

    node_ids = {n["id"] for n in nodes}
    bad_uses = [(n["id"], u) for n in nodes for u in n["uses"] if u not in node_ids]

    if missing:
        print("Blueprint validation FAILED — missing Lean declarations:", file=sys.stderr)
        for nid, d in missing:
            print(f"  [{nid}] {d}", file=sys.stderr)
        return 1
    if bad_uses:
        print("Blueprint validation FAILED — broken \\uses references:", file=sys.stderr)
        for nid, u in bad_uses:
            print(f"  [{nid}] uses unknown label {u}", file=sys.stderr)
        return 1

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUT_DIR / "index.html").write_text(render_html(nodes), encoding="utf-8", newline="\n")
    (OUT_DIR / "blueprint.json").write_text(json.dumps(nodes, indent=2) + "\n", encoding="utf-8", newline="\n")
    total_decls = sum(len(n["lean"]) for n in nodes)
    print(f"PASS: Blueprint validated {len(nodes)} nodes ({total_decls} Lean decls with exact GitHub #L links) -> {OUT_DIR}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
