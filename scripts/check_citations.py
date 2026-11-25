#!/usr/bin/env python3
"""Validate DOI, arXiv, and BibTeX citation identifiers across paper/ and CITATION.cff.

Static structural and regression checks run offline in CI; pass --online to perform
live HTTPS checks against arXiv and Crossref/DOI endpoints.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PAPER_DIR = ROOT / "paper"

ARXIV_RE = re.compile(r"arXiv:([0-9]{4}\.[0-9]{4,5}(?:v[0-9]+)?|[a-z-]+/[0-9]{7})", re.I)
EPRINT_RE = re.compile(r"eprint\s*=\s*\{([^}]+)\}", re.I)
DOI_RE = re.compile(r"\b(10\.[0-9]{4,9}/[-._;()/:A-Za-z0-9]+)")
PLACEHOLDER_RE = re.compile(r"(TODO\(cite\)|FIXME_DOI|10\.0000/|arXiv:0000\.00000)", re.I)
KNOWN_BAD_ARXIV = {"2610.1336", "2610.01336"}  # E-2026-001 truncated ID guard


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

    return {
        "files_scanned": files_scanned,
        "arxiv_ids": sorted(arxiv_ids),
        "dois": sorted(dois),
        "placeholders": placeholders,
        "malformed": malformed,
    }


def check_online(urls: list[str]) -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    for url in urls:
        if not url.startswith(("https://", "http://")):
            raise ValueError(f"Unsupported URL scheme: {url!r}")
        req = urllib.request.Request(
            url,
            method="HEAD",
            headers={"User-Agent": "multinomial-tv-conjecture-audit/2.0"},
        )
        try:
            with urllib.request.urlopen(req, timeout=12) as resp:  # noqa: S310
                results.append({"url": url, "status": resp.status, "ok": 200 <= resp.status < 400})
        except Exception as exc:
            results.append({"url": url, "status": None, "ok": False, "error": str(exc)})
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--online", action="store_true", help="Verify DOI/arXiv URLs live over HTTPS")
    args = parser.parse_args()

    scan = scan_citations()
    online_checks: list[dict[str, Any]] = []
    if args.online:
        urls = [f"https://arxiv.org/abs/{aid}" for aid in scan["arxiv_ids"]] + [
            f"https://api.crossref.org/works/{doi}" for doi in scan["dois"]
        ]
        online_checks = check_online(urls)

    online_ok = all(item["ok"] for item in online_checks)
    ok = (
        len(scan["placeholders"]) == 0
        and len(scan["malformed"]) == 0
        and scan["files_scanned"] > 0
        and online_ok
    )
    report = {
        "status": "pass" if ok else "fail",
        "files_scanned": scan["files_scanned"],
        "arxiv_count": len(scan["arxiv_ids"]),
        "doi_count": len(scan["dois"]),
        "placeholder_hits": scan["placeholders"],
        "malformed_hits": scan["malformed"],
        "arxiv_ids": scan["arxiv_ids"],
        "dois": scan["dois"],
        "online_checks": online_checks,
    }
    out = ROOT / "results" / "citation-audit.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(
        f"Citation audit ({report['status']}): {scan['files_scanned']} files, "
        f"{len(scan['arxiv_ids'])} arXiv IDs, {len(scan['dois'])} DOIs, "
        f"{len(scan['placeholders'])} placeholders, {len(scan['malformed'])} malformed."
    )
    if not ok:
        print(json.dumps(report, indent=2), file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
