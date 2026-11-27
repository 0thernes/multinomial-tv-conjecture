#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Validate DOI, arXiv, BibTeX cite-key parity, title/author match, and retraction metadata.

Static structural and regression checks run offline in CI without mutating tracked files.
Pass --online to perform live HTTPS checks against arXiv Atom API and Crossref JSON API
(verifying HTTP 200, title/author/primaryClass match against paper/refs.bib, and Crossref
updated-by / update-to / relation retraction metadata), and --write to refresh
results/citation-audit.json.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
import urllib.request
import xml.etree.ElementTree as ET
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

# Composite journal column headers in Crossref where multiple short notes share one DOI
# (e.g., Robbins 1955 "A Remark on Stirling's Formula" is indexed under "Mathematical Notes", pp. 26-33).
COMPOSITE_COLUMN_TITLES = {"mathematical notes"}

STOPWORDS = {"a", "an", "and", "for", "in", "of", "on", "the", "to", "under", "with", "its"}


def _strip_tex_accents(text: str) -> str:
    s = re.sub(r"\\['\"`^~=.uvHc]\{?([A-Za-z])\}?", r"\1", text)
    s = s.replace("{", "").replace("}", "").replace("\\&", " and ")
    s = unicodedata.normalize("NFKD", s)
    return "".join(ch for ch in s if not unicodedata.combining(ch))


def _title_tokens(text: str) -> set[str]:
    clean = _strip_tex_accents(text).lower()
    words = re.findall(r"[a-z0-9]+", clean)
    return {w for w in words if len(w) > 1 and w not in STOPWORDS}


def _author_surnames(author_str: str) -> set[str]:
    clean = _strip_tex_accents(author_str)
    surnames: set[str] = set()
    for part in re.split(r"\s+and\s+", clean):
        p = part.strip()
        if not p:
            continue
        if "," in p:
            last = p.split(",", 1)[0].strip()
        else:
            tokens = p.split()
            last = tokens[-1] if tokens else ""
        norm = re.sub(r"[^a-z]", "", last.lower())
        if norm:
            surnames.add(norm)
    return surnames


def parse_bib_entries(bib_path: Path | None = None) -> list[dict[str, str]]:
    """Parse BibTeX entries from paper/refs.bib with brace-balanced field extraction."""
    path = bib_path if bib_path is not None else PAPER_DIR / "refs.bib"
    if not path.is_file():
        return []
    text = path.read_text(encoding="utf-8", errors="replace")
    entries: list[dict[str, str]] = []
    i, n = 0, len(text)
    while i < n:
        m = re.search(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", text[i:])
        if not m:
            break
        key = m.group(2).strip()
        pos = i + m.end()
        depth = 1
        start = pos
        while pos < n and depth > 0:
            if text[pos] == "{":
                depth += 1
            elif text[pos] == "}":
                depth -= 1
            pos += 1
        body = text[start : pos - 1]
        fields: dict[str, str] = {"key": key}
        j, bn = 0, len(body)
        while j < bn:
            fm = re.search(r"([A-Za-z][A-Za-z0-9_-]*)\s*=\s*", body[j:])
            if not fm:
                break
            fname = fm.group(1).lower()
            vpos = j + fm.end()
            if vpos >= bn:
                break
            if body[vpos] == "{":
                vdepth = 1
                vpos += 1
                vstart = vpos
                while vpos < bn and vdepth > 0:
                    if body[vpos] == "{":
                        vdepth += 1
                    elif body[vpos] == "}":
                        vdepth -= 1
                    vpos += 1
                val = body[vstart : vpos - 1]
            elif body[vpos] == '"':
                vpos += 1
                vstart = vpos
                while vpos < bn and body[vpos] != '"':
                    vpos += 1
                val = body[vstart:vpos]
                vpos += 1
            else:
                vstart = vpos
                while vpos < bn and body[vpos] not in ",\n\r":
                    vpos += 1
                val = body[vstart:vpos]
            fields[fname] = re.sub(r"\s+", " ", val).strip()
            j = vpos
        entries.append(fields)
        i = pos
    return entries


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


def verify_crossref_payload(
    doi: str,
    payload: dict[str, Any],
    expected: dict[str, str] | None = None,
    *,
    http_status: int = 200,
) -> dict[str, Any]:
    """Validate Crossref JSON payload for retractions (updated-by/update-to/relation) and title/author match."""
    msg = payload.get("message", {})
    titles = msg.get("title") or []
    title = re.sub(r"\s+", " ", str(titles[0])).strip() if titles else ""
    cr_authors: list[str] = []
    cr_surnames: set[str] = set()
    for a in msg.get("author") or []:
        fam = str(a.get("family") or a.get("name") or "").strip()
        if fam:
            cr_authors.append(fam)
            norm = re.sub(r"[^a-z]", "", _strip_tex_accents(fam).lower())
            if norm:
                cr_surnames.add(norm)

    retracted = False
    for field_name in ("update-to", "updated-by"):
        for upd in msg.get(field_name) or []:
            utype = str(upd.get("type", "")).lower()
            label = str(upd.get("label", "")).lower()
            if "retract" in utype or "withdraw" in utype or "retract" in label or "withdraw" in label:
                retracted = True
    rel = msg.get("relation") or {}
    if any("retract" in str(k).lower() or "withdraw" in str(k).lower() for k in rel):
        retracted = True

    metadata_match = True
    match_note = "no_bib_entry"
    if expected is not None:
        exp_title_toks = _title_tokens(expected.get("title", ""))
        got_title_toks = _title_tokens(title)
        exp_surnames = _author_surnames(expected.get("author", ""))
        overlap = len(exp_title_toks & got_title_toks) / max(1, len(exp_title_toks))
        author_ok = (not exp_surnames) or bool(exp_surnames & cr_surnames) or any(
            s in " ".join(cr_surnames) for s in exp_surnames
        )
        if overlap >= 0.6 and author_ok:
            metadata_match = True
            match_note = "title_and_author_match"
        elif title.lower() in COMPOSITE_COLUMN_TITLES and author_ok:
            cr_vol = str(msg.get("volume", "")).strip()
            exp_vol = expected.get("volume", "").strip()
            cr_years = {
                str(parts[0][0])
                for key in ("published-print", "published-online", "issued", "created")
                for parts in [(msg.get(key) or {}).get("date-parts") or []]
                if parts and parts[0]
            }
            exp_year = expected.get("year", "").strip()
            vol_ok = (not exp_vol) or (cr_vol == exp_vol)
            year_ok = (not exp_year) or (exp_year in cr_years)
            metadata_match = vol_ok and year_ok
            match_note = "composite_column_author_year_vol_match" if metadata_match else "composite_column_mismatch"
        else:
            metadata_match = False
            match_note = f"metadata_mismatch(title_overlap={overlap:.2f}, author_ok={author_ok})"

    return {
        "kind": "doi",
        "id": doi,
        "url": f"https://api.crossref.org/works/{doi}",
        "status": http_status,
        "title": title,
        "authors": cr_authors,
        "retracted": retracted,
        "metadata_match": metadata_match,
        "match_note": match_note,
        "ok": (200 <= http_status < 400) and (not retracted) and metadata_match,
    }


def verify_arxiv_xml(
    aid: str,
    xml_text: str,
    expected: dict[str, str] | None = None,
    *,
    http_status: int = 200,
) -> dict[str, Any]:
    """Validate arXiv Atom XML for live existence, title/author match, and primaryClass match."""
    ns = {
        "atom": "http://www.w3.org/2005/Atom",
        "arxiv": "http://arxiv.org/schemas/atom",
    }
    root = ET.fromstring(xml_text)
    entry = root.find("atom:entry", ns)
    if entry is None:
        return {
            "kind": "arxiv",
            "id": aid,
            "url": f"https://arxiv.org/abs/{aid}",
            "status": http_status,
            "ok": False,
            "metadata_match": False,
            "error": "No Atom <entry> returned by arXiv API",
        }

    title = re.sub(r"\s+", " ", (entry.findtext("atom:title", default="", namespaces=ns) or "")).strip()
    if not title or title.lower() == "error":
        return {
            "kind": "arxiv",
            "id": aid,
            "url": f"https://arxiv.org/abs/{aid}",
            "status": http_status,
            "title": title,
            "ok": False,
            "metadata_match": False,
            "error": f"Invalid arXiv entry title: {title!r}",
        }

    authors = [
        re.sub(r"\s+", " ", (a.findtext("atom:name", default="", namespaces=ns) or "")).strip()
        for a in entry.findall("atom:author", ns)
    ]
    got_surnames = _author_surnames(" and ".join(authors))
    prim_el = entry.find("arxiv:primary_category", ns)
    primary_category = prim_el.attrib.get("term", "").strip() if prim_el is not None else ""

    metadata_match = True
    match_note = "no_bib_entry"
    if expected is not None:
        exp_title_toks = _title_tokens(expected.get("title", ""))
        got_title_toks = _title_tokens(title)
        exp_surnames = _author_surnames(expected.get("author", ""))
        overlap = len(exp_title_toks & got_title_toks) / max(1, len(exp_title_toks))
        author_ok = (not exp_surnames) or bool(exp_surnames & got_surnames)
        exp_cls = expected.get("primaryclass", "").strip()
        cls_ok = (not exp_cls) or (primary_category == exp_cls)
        metadata_match = (overlap >= 0.6) and author_ok and cls_ok
        match_note = (
            "title_author_class_match"
            if metadata_match
            else f"metadata_mismatch(title_overlap={overlap:.2f}, author_ok={author_ok}, class_ok={cls_ok})"
        )

    return {
        "kind": "arxiv",
        "id": aid,
        "url": f"https://arxiv.org/abs/{aid}",
        "status": http_status,
        "title": title,
        "authors": authors,
        "primary_category": primary_category,
        "metadata_match": metadata_match,
        "match_note": match_note,
        "ok": (200 <= http_status < 400) and metadata_match,
    }


def _check_arxiv(aid: str, expected: dict[str, str] | None = None) -> dict[str, Any]:
    api_url = f"https://export.arxiv.org/api/query?id_list={aid}"
    req = urllib.request.Request(api_url, method="GET", headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:  # noqa: S310
            xml_text = resp.read().decode("utf-8", errors="replace")
            return verify_arxiv_xml(aid, xml_text, expected=expected, http_status=resp.status)
    except Exception as exc:
        return {
            "kind": "arxiv",
            "id": aid,
            "url": f"https://arxiv.org/abs/{aid}",
            "status": None,
            "metadata_match": False,
            "ok": False,
            "error": str(exc),
        }


def _check_crossref_doi(doi: str, expected: dict[str, str] | None = None) -> dict[str, Any]:
    url = f"https://api.crossref.org/works/{doi}"
    req = urllib.request.Request(url, method="GET", headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:  # noqa: S310
            payload = json.loads(resp.read().decode("utf-8", errors="replace"))
            return verify_crossref_payload(doi, payload, expected=expected, http_status=resp.status)
    except Exception as exc:
        return {
            "kind": "doi",
            "id": doi,
            "url": url,
            "status": None,
            "retracted": None,
            "metadata_match": False,
            "ok": False,
            "error": str(exc),
        }


def check_online(arxiv_ids: list[str], dois: list[str]) -> list[dict[str, Any]]:
    bib_entries = parse_bib_entries()
    by_arxiv = {e["eprint"].strip(): e for e in bib_entries if e.get("eprint")}
    by_doi = {e["doi"].strip().lower(): e for e in bib_entries if e.get("doi")}
    return [_check_arxiv(aid, expected=by_arxiv.get(aid)) for aid in arxiv_ids] + [
        _check_crossref_doi(doi, expected=by_doi.get(doi.lower())) for doi in dois
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--online",
        action="store_true",
        help="Verify DOI/arXiv URLs, title/author/primaryClass match, and Crossref retraction status over HTTPS",
    )
    parser.add_argument("--write", action="store_true", help="Write audit JSON to results/citation-audit.json")
    args = parser.parse_args()

    scan = scan_citations()
    online_checks: list[dict[str, Any]] = []
    if args.online:
        online_checks = check_online(scan["arxiv_ids"], scan["dois"])

    online_ok = all(item["ok"] for item in online_checks)
    retracted_count = sum(1 for item in online_checks if item.get("retracted") is True)
    metadata_mismatch_count = sum(1 for item in online_checks if item.get("metadata_match") is False)
    ok = (
        len(scan["placeholders"]) == 0
        and len(scan["malformed"]) == 0
        and len(scan["missing_bib_keys"]) == 0
        and len(scan["uncited_bib_keys"]) == 0
        and scan["files_scanned"] > 0
        and online_ok
        and retracted_count == 0
        and metadata_mismatch_count == 0
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
        "metadata_mismatch_count": metadata_mismatch_count,
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
        f"{metadata_mismatch_count} metadata mismatches, "
        f"{len(scan['placeholders'])} placeholders, {len(scan['malformed'])} malformed."
    )
    if not ok:
        print(json.dumps(report, indent=2), file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
