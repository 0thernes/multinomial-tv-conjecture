#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Validate DOI, arXiv, BibTeX cite-key parity, and retraction metadata across paper/ and CITATION.cff.

Static structural and regression checks run offline in CI without mutating tracked files.
Pass --online to perform live HTTPS checks against arXiv and Crossref (including
retraction/withdrawal metadata checks), and --write to refresh results/citation-audit.json.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PAPER_DIR = ROOT / "paper"
VERSION = (ROOT / "VERSION").read_text(encoding="utf-8").strip() if (ROOT / "VERSION").is_file() else "0.0.0"

ARXIV_RE = re.compile(r"arXiv:([0-9]{4}\.[0-9]{4,5}(?:v[0-9]+)?|[a-z-]+/[0-9]{7})", re.I)
EPRINT_RE = re.compile(r"eprint\s*=\s*\{([^}]+)\}", re.I)
DOI_RE = re.compile(r"\b(10\.[0-9]{4,9}/[-._;()/:A-Za-z0-9]+)")
PLACEHOLDER_RE = re.compile(r"(TODO\(cite\)|FIXME_DOI|10\.0000/|arXiv:0000\.00000)", re.I)
CITE_RE = re.compile(r"\\cite[a-zA-Z*]*(?:\[[^\]]*\])*\{([^}]+)\}")
BIB_KEY_RE = re.compile(r"@\w+\s*\{\s*([^,\s]+)\s*,")
KNOWN_BAD_ARXIV = {"2610.1336", "2610.01336"}  # E-2026-001 truncated ID guard
USER_AGENT = f"multinomial-tv-conjecture-audit/{VERSION} (mailto:0_0@0thernes.art)"


def check_bib_cite_parity() -> tuple[list[str], list[str], int]:
    """Return (missing_keys_in_bib, uncited_keys_in_bib, bib_entry_count)."""
    main_tex = PAPER_DIR / "main.tex"
    refs_bib = PAPER_DIR / "refs.bib"
    if not (main_tex.is_file() and refs_bib.is_file()):
        return [], [], 0
    tex_txt = main_tex.read_text(encoding="utf-8", errors="replace")
    bib_txt = refs_bib.read_text(encoding="utf-8", errors="replace")
    cited: set[str] = set()
    for m in CITE_RE.finditer(tex_txt):
        for key in m.group(1).split(","):
            k = key.strip()
            if k:
                cited.add(k)
    bib_keys = set(BIB_KEY_RE.findall(bib_txt))
    return sorted(cited - bib_keys), sorted(bib_keys - cited), len(bib_keys)


def scan_citations() -> dict[str, Any]:
    arxiv_ids: set[str] = set()
    dois: set[str] = set()
    placeholders: list[dict[str, str]] = []
    malformed: list[dict[str, str]] = []
    files_scanned = 0

    targets = [
        p
        for p in sorted(PAPER_DIR.rglob("*"))
        if p.is_file() and p.suffix.lower() in {".tex", ".bib", ".md"} and "build" not in p.parts
    ]
    cff = ROOT / "CITATION.cff"
    if cff.is_file():
        targets.append(cff)

    for path in targets:
        files_scanned += 1
        text = path.read_text(encoding="utf-8", errors="replace")
        rel = path.relative_to(ROOT).as_posix()
        for m in ARXIV_RE.finditer(text):
            aid = m.group(1)
            arxiv_ids.add(aid)
            if aid in KNOWN_BAD_ARXIV:
                malformed.append({"file": rel, "id": aid, "reason": "known truncated arXiv ID (E-2026-001)"})
        for m in EPRINT_RE.finditer(text):
            aid = m.group(1).strip()
            arxiv_ids.add(aid)
            if aid in KNOWN_BAD_ARXIV or not re.fullmatch(r"[0-9]{4}\.[0-9]{5}(?:v[0-9]+)?", aid):
                malformed.append({"file": rel, "id": aid, "reason": "post-2015 arXiv eprint must have 5-digit suffix"})
        for m in DOI_RE.finditer(text):
            cleaned = m.group(1).rstrip(".,;)]}")
            dois.add(cleaned)
        for m in PLACEHOLDER_RE.finditer(text):
            placeholders.append({"file": rel, "match": m.group(0)})

    missing_bib, uncited_bib, bib_count = check_bib_cite_parity()
    return {
        "files_scanned": files_scanned,
        "bib_entry_count": bib_count,
        "missing_bib_keys": missing_bib,
        "uncited_bib_keys": uncited_bib,
        "arxiv_ids": sorted(arxiv_ids),
        "dois": sorted(dois),
        "placeholders": placeholders,
        "malformed": malformed,
    }


def _check_arxiv(aid: str) -> dict[str, Any]:
    url = f"https://arxiv.org/abs/{aid}"
    req = urllib.request.Request(url, method="HEAD", headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:  # noqa: S310
            return {"kind": "arxiv", "id": aid, "url": url, "status": resp.status, "ok": 200 <= resp.status < 400}
    except Exception as exc:
        return {"kind": "arxiv", "id": aid, "url": url, "status": None, "ok": False, "error": str(exc)}


def _check_crossref_doi(doi: str) -> dict[str, Any]:
    url = f"https://api.crossref.org/works/{doi}"
    req = urllib.request.Request(url, method="GET", headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:  # noqa: S310
            payload = json.loads(resp.read().decode("utf-8", errors="replace"))
            msg = payload.get("message", {})
            titles = msg.get("title") or []
            title = titles[0] if titles else ""
            retracted = False
            for upd in msg.get("update-to", []) or []:
                utype = str(upd.get("type", "")).lower()
                if "retract" in utype or "withdraw" in utype:
                    retracted = True
            rel = msg.get("relation") or {}
            if any("retract" in str(k).lower() for k in rel):
                retracted = True
            return {
                "kind": "doi",
                "id": doi,
                "url": url,
                "status": resp.status,
                "title": title,
                "retracted": retracted,
                "ok": (200 <= resp.status < 400) and (not retracted),
            }
    except Exception as exc:
        return {"kind": "doi", "id": doi, "url": url, "status": None, "retracted": None, "ok": False, "error": str(exc)}


def check_online(arxiv_ids: list[str], dois: list[str]) -> list[dict[str, Any]]:
    return [_check_arxiv(aid) for aid in arxiv_ids] + [_check_crossref_doi(doi) for doi in dois]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--online", action="store_true", help="Verify DOI/arXiv URLs & Crossref retraction status over HTTPS")
    parser.add_argument("--write", action="store_true", help="Write audit JSON to results/citation-audit.json")
    args = parser.parse_args()

    scan = scan_citations()
    online_checks: list[dict[str, Any]] = []
    if args.online:
        online_checks = check_online(scan["arxiv_ids"], scan["dois"])

    online_ok = all(item["ok"] for item in online_checks)
    retracted_count = sum(1 for item in online_checks if item.get("retracted") is True)
    ok = (
        len(scan["placeholders"]) == 0
        and len(scan["malformed"]) == 0
        and len(scan["missing_bib_keys"]) == 0
        and len(scan["uncited_bib_keys"]) == 0
        and scan["files_scanned"] > 0
        and online_ok
        and retracted_count == 0
    )
    report = {
        "status": "pass" if ok else "fail",
        "checked_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "files_scanned": scan["files_scanned"],
        "bib_entry_count": scan["bib_entry_count"],
        "missing_bib_keys": scan["missing_bib_keys"],
        "uncited_bib_keys": scan["uncited_bib_keys"],
        "arxiv_count": len(scan["arxiv_ids"]),
        "doi_count": len(scan["dois"]),
        "retracted_count": retracted_count,
        "placeholder_hits": scan["placeholders"],
        "malformed_hits": scan["malformed"],
        "arxiv_ids": scan["arxiv_ids"],
        "dois": scan["dois"],
        "online_checks": online_checks,
    }
    if args.write:
        out = ROOT / "results" / "citation-audit.json"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(
        f"Citation audit ({report['status']}): {scan['files_scanned']} files, "
        f"{scan['bib_entry_count']} BibTeX entries (missing={len(scan['missing_bib_keys'])}, "
        f"uncited={len(scan['uncited_bib_keys'])}), "
        f"{len(scan['arxiv_ids'])} arXiv IDs, {len(scan['dois'])} DOIs, "
        f"{len(online_checks)} online checks, {retracted_count} retractions, "
        f"{len(scan['placeholders'])} placeholders, {len(scan['malformed'])} malformed."
    )
    if not ok:
        print(json.dumps(report, indent=2), file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
