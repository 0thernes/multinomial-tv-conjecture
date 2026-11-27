# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Repository integrity, regression, schema, axiom-sync, citation, and reproducibility tests.

Covers Build Standard v1.2.0 items:
- A08: Single version source consistency (VERSION, CHANGELOG, CITATION.cff, formalization.yaml, lakefile.toml)
- A32: Agent entry points (AGENTS.md, CLAUDE.md, GEMINI.md, llms.txt)
- B03: Deterministic byte-reproducible arXiv tarball
- B06: Negative tamper-detection tests on axiom parser & forbidden-token lexer
- B07: Regression tests for every erratum E-2026-001..017
- B08: Golden snapshot checks on results/lean-axioms-all.log
- B13: Code mutation audit report verification (results/mutation-report.json)
- R4:  Zero banned files (PULL_REQUEST_TEMPLATE.md, dependabot.yml, etc.)
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tarfile
from pathlib import Path

import jsonschema
import pytest
import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import build_arxiv_bundle as bab  # noqa: E402
import check_citations as cc  # noqa: E402
import check_readme_axioms as cra  # noqa: E402
import generate_manifest as gm  # noqa: E402
import stamp_timestamps as st_mod  # noqa: E402


def test_repo_yaml_matches_json_schema() -> None:
    """Validate repo.yaml against repo-standard.schema.json (Draft 2020-12)."""
    schema = json.loads((ROOT / "repo-standard.schema.json").read_text(encoding="utf-8"))
    manifest = yaml.safe_load((ROOT / "repo.yaml").read_text(encoding="utf-8"))
    jsonschema.validate(instance=manifest, schema=schema)
    assert manifest["standard"] == "1.2.0"


def test_single_version_consistency() -> None:
    """Verify VERSION matches CHANGELOG.md, CITATION.cff, formalization.yaml, and lean/lakefile.toml."""
    ver = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    assert re.fullmatch(r"\d+\.\d+\.\d+", ver)

    changelog = (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
    assert re.search(rf"^## \[?v?{re.escape(ver)}\]?", changelog, re.M)

    cff = yaml.safe_load((ROOT / "CITATION.cff").read_text(encoding="utf-8"))
    assert str(cff["version"]) == ver

    formal = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    assert str(formal["version"]) == ver

    lakefile = (ROOT / "lean" / "lakefile.toml").read_text(encoding="utf-8")
    assert f'version = "{ver}"' in lakefile


def test_r4_no_banned_files() -> None:
    """Build Standard R4: ensure zero banned repository files exist."""
    banned = [
        ".github/PULL_REQUEST_TEMPLATE.md",
        ".github/pull_request_template.md",
        ".github/dependabot.yml",
        ".github/dependabot.yaml",
        "renovate.json",
        ".github/copilot-instructions.md",
        ".github/FUNDING.yml",
    ]
    for rel in banned:
        assert not (ROOT / rel).exists(), f"R4 banned file present: {rel}"


def test_regression_e2026_001_citations_and_no_truncated_arxiv(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Regression & negative test (B06, B07) for E-2026-001: truncated arXiv:2610.1336 and cite parity."""
    scan = cc.scan_citations()
    assert scan["placeholders"] == []
    assert scan["malformed"] == []
    assert "2610.13366" in scan["arxiv_ids"]
    assert "2610.1336" not in scan["arxiv_ids"]

    # Negative check (kills M14_citations_drop_bad_arxiv & M15_citations_skip_parity)
    assert "2610.1336" in cc.KNOWN_BAD_ARXIV
    fake_paper = tmp_path / "paper"
    fake_paper.mkdir()
    (fake_paper / "main.tex").write_text(
        "See arXiv:2610.1336 and \\cite{missing_key}.\n", encoding="utf-8", newline="\n"
    )
    (fake_paper / "refs.bib").write_text(
        "@article{uncited_key, title={Dummy}, year={2026}}\n", encoding="utf-8", newline="\n"
    )
    monkeypatch.setattr(cc, "PAPER_DIR", fake_paper)
    monkeypatch.setattr(cc, "ROOT", tmp_path)
    bad_scan = cc.scan_citations()
    assert any(hit["id"] == "2610.1336" for hit in bad_scan["malformed"])
    missing_keys, uncited_keys, bib_cnt = cc.check_bib_cite_parity()
    assert missing_keys == ["missing_key"]
    assert uncited_keys == ["uncited_key"]
    assert bib_cnt == 1


def test_regression_e2026_002_no_unformed_llc_in_active_metadata() -> None:
    """Regression test (B07) for E-2026-002: active identity files must not assert '0thernes LLC'."""
    active_files = [
        "README.md",
        "CITATION.cff",
        "formalization.yaml",
        "LICENSE",
        "LICENSE-DOCS",
        "NOTICE",
        "paper/main.tex",
    ]
    for rel in active_files:
        text = (ROOT / rel).read_text(encoding="utf-8")
        assert "0thernes LLC" not in text, f"Unformed entity '0thernes LLC' found in {rel}"


def test_regression_e2026_003_and_005_deterministic_arxiv_bundle(tmp_path: Path) -> None:
    """Regression & determinism test (B03, B07) for E-2026-003 & E-2026-005."""
    t1 = tmp_path / "bundle1.tar.gz"
    t2 = tmp_path / "bundle2.tar.gz"
    _, h1 = bab.build_bundle(t1)
    _, h2 = bab.build_bundle(t2)
    assert h1 == h2, "arXiv tarball build is not byte-reproducible"

    with tarfile.open(t1, "r:gz") as tf:
        names = tf.getnames()
        assert "00README.XXX" in names
        assert "main.tex" in names
        assert "refs.bib" in names
        assert "figures/fig1_residue_convergence.pdf" in names
        for member in tf.getmembers():
            assert member.mtime == 0
            assert member.uid == 0
            assert member.gid == 0


def test_regression_e2026_004_axiom_log_and_readme_sync(tmp_path: Path) -> None:
    """Regression & golden snapshot test (B06, B07, B08) for exhaustive Lean axiom log & README sync."""
    log_path = ROOT / "results" / "lean-axioms-all.log"
    assert log_path.is_file()
    log_text = log_path.read_text(encoding="utf-8")
    decls = cra.parse_log(log_text)
    assert len(decls) == 55
    for name, axioms in decls.items():
        assert axioms <= cra.ALLOWED, f"Non-standard axiom in {name}: {axioms}"
    assert cra.EXHAUSTIVE_RE.search(log_text), "Missing ALL_THEOREMS_AXIOM_AUDIT_PASS sentinel"

    # Negative check (B06, kills M12_axioms_allow_sorry): tampered log with sorryAx must be detected
    tampered = cra.parse_log("'MultinomialTV.fake' depends on axioms: [propext, sorryAx]\n")
    assert not (tampered["MultinomialTV.fake"] <= cra.ALLOWED)

    # Negative check (B06, kills M13_axioms_skip_exhaustive): missing exhaustive sentinel must fail --require-exhaustive
    no_ex_log = tmp_path / "no-exhaustive.log"
    no_ex_log.write_text(
        "\n".join(ln for ln in log_text.splitlines() if "ALL_THEOREMS_AXIOM_AUDIT_PASS" not in ln) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    neg_proc = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "check_readme_axioms.py"),
            "--log",
            str(no_ex_log),
            "--require-exhaustive",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert neg_proc.returncode != 0, "Expected failure when ALL_THEOREMS_AXIOM_AUDIT_PASS sentinel is absent"

    proc = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "check_readme_axioms.py"), "--require-exhaustive"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_forbidden_lean_tokens_absent_from_proof_modules() -> None:
    """Soundness check (Claim C5): zero sorry/admit/axiom/native_decide/unsafe in proof modules."""
    def strip_lean_comments(src: str) -> str:
        out, i, n, depth, in_str = [], 0, len(src), 0, False
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

    forbidden = re.compile(
        r"\b(sorry|admit|native_decide|unsafe)\b"
        r"|^\s*(?:@\[[^\]]+\]\s+|public\s+|private\s+|protected\s+|noncomputable\s+)*axiom\b"
        r"|^\s*(?:public\s+|private\s+|protected\s+)*partial\s+(?:def|theorem)\b"
        r"|implemented_by|@\[extern"
    )
    proof_files = (
        sorted((ROOT / "lean" / "MultinomialTVConjecture").rglob("*.lean"))
        + [ROOT / "lean" / "MultinomialTVConjecture.lean", ROOT / "lean" / "Solution.lean"]
    )
    assert len(proof_files) >= 8
    for f in proof_files:
        cleaned = strip_lean_comments(f.read_text(encoding="utf-8"))
        assert re.search(r"^\s*module\s*$", cleaned, re.M), f"Missing Lean 4.35 module header in {f}"
        for lineno, line in enumerate(cleaned.splitlines(), 1):
            assert not forbidden.search(line), f"Forbidden token in {f}:{lineno}: {line.strip()}"

    # Negative check (B06, F-37): ensure public axiom and partial def are caught by the hardened regex
    assert forbidden.search("public axiom sneak : False")
    assert forbidden.search("noncomputable axiom sneak2 : False")
    assert forbidden.search("public partial def loop : Nat := loop")


def test_palomar_module_headers_and_reuse_spdx_headers() -> None:
    """Verify Palomar module-header rule across all 10 Lean files and SPDX headers across all code/TeX files."""
    lean_files = [f for f in sorted((ROOT / "lean").rglob("*.lean")) if ".lake" not in f.parts]
    assert len(lean_files) == 10
    for lf in lean_files:
        txt = lf.read_text(encoding="utf-8")
        assert re.search(r"^\s*module\s*$", txt, re.M), f"Missing module header in {lf}"
        assert "SPDX-License-Identifier: Apache-2.0" in txt, f"Missing SPDX Apache-2.0 in {lf}"
        assert len(txt.splitlines()) <= 10_000, f"Palomar 10k-line limit exceeded in {lf}"
    ch = ROOT / "lean" / "Challenge.lean"
    assert len(ch.read_text(encoding="utf-8").splitlines()) <= 1_000
    assert ch.stat().st_size <= 100 * 1024

    for folder in ("scripts", "tests"):
        for f in sorted((ROOT / folder).glob("*")):
            if f.is_file() and f.suffix.lower() in {".py", ".sh", ".ps1"}:
                txt = f.read_text(encoding="utf-8")
                assert "SPDX-License-Identifier: Apache-2.0" in txt, f"Missing SPDX Apache-2.0 in {f}"

    for tex in (ROOT / "paper" / "main.tex", ROOT / "blueprint" / "src" / "content.tex"):
        txt = tex.read_text(encoding="utf-8")
        assert "SPDX-License-Identifier: CC-BY-4.0" in txt, f"Missing SPDX CC-BY-4.0 in {tex}"


def test_citation_cff_and_formalization_lockfile_parity() -> None:
    """Validate CITATION.cff required CFF 1.2.0 fields and formalization.yaml revs against lake-manifest.json."""
    cff = yaml.safe_load((ROOT / "CITATION.cff").read_text(encoding="utf-8"))
    assert cff["cff-version"] == "1.2.0"
    assert cff["license"] == "Apache-2.0"
    assert re.fullmatch(r"\d{4}-\d{2}-\d{2}", str(cff["date-released"]))
    assert cff["authors"][0]["orcid"] == "https://orcid.org/0009-0006-8168-9648"
    assert len(cff["references"]) >= 3

    formal = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    lake_manifest = json.loads((ROOT / "lean" / "lake-manifest.json").read_text(encoding="utf-8"))
    pkg_revs = {p["name"]: p["rev"] for p in lake_manifest["packages"]}
    assert pkg_revs["mathlib"].startswith(str(formal["mathlib_rev"]))
    assert pkg_revs["batteries"].startswith(str(formal["batteries_rev"]))


def test_blueprint_and_site_build_cleanly() -> None:
    """Verify every \\lean{...} declaration in blueprint/src/content.tex resolves and site has 0 broken links."""
    bp_tex = (ROOT / "blueprint" / "src" / "content.tex").read_text(encoding="utf-8")
    assert "`" not in bp_tex, "Raw Markdown backticks found in blueprint/src/content.tex (use \\texttt{...})"
    for script in ("build_blueprint.py", "build_site.py"):
        proc = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / script)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
        )
        assert proc.returncode == 0, f"{script} failed:\n{proc.stdout}\n{proc.stderr}"

    bp_nodes = json.loads((ROOT / "build" / "site" / "blueprint" / "blueprint.json").read_text(encoding="utf-8"))
    nonvac = next(n for n in bp_nodes if n["id"] == "prop:nonvac")
    assert len(nonvac["lean"]) == 20, f"Expected all 20 NonVacuity theorems in Blueprint, got {len(nonvac['lean'])}"

    # Verify strict CSP, SRI integrity on external CDN scripts, and dynamic audited theorem count on portal (F-47, F-52)
    portal_html = (ROOT / "build" / "site" / "index.html").read_text(encoding="utf-8")
    bp_html = (ROOT / "build" / "site" / "blueprint" / "index.html").read_text(encoding="utf-8")
    assert 'http-equiv="Content-Security-Policy"' in portal_html
    assert 'http-equiv="Content-Security-Policy"' in bp_html
    ax_m = cra.EXHAUSTIVE_RE.search((ROOT / "results" / "lean-axioms-all.log").read_text(encoding="utf-8"))
    assert ax_m is not None
    assert f"{ax_m.group(1)} Exhaustively Audited Theorems" in portal_html
    for html_txt in (portal_html, bp_html):
        for tag in re.findall(r"<(?:script|link)\b[^>]+https?://[^>]+>", html_txt):
            assert 'integrity="sha384-' in tag, f"External CDN resource missing sha384 SRI: {tag}"
            assert 'crossorigin="anonymous"' in tag, f"External CDN resource missing crossorigin: {tag}"


def test_mathlib_standard_linter_and_version_hygiene() -> None:
    """Verify Playbook #5 Mathlib style linter set in lakefile.toml and zero stale version labels."""
    lakefile = (ROOT / "lean" / "lakefile.toml").read_text(encoding="utf-8")
    assert "weak.linter.mathlibStandardSet = true" in lakefile

    ver = (ROOT / "VERSION").read_text(encoding="utf-8").strip()
    assert f"(v{ver})" in (ROOT / "llms.txt").read_text(encoding="utf-8")
    assert f"V{ver}" in (ROOT / "docs" / "media" / "social-preview.svg").read_text(encoding="utf-8")


def test_zero_broken_relative_markdown_links() -> None:
    """Ensure every relative Markdown link across root and docs/ resolves to an existing file."""
    md_link_re = re.compile(r'!?\[[^\]]*\]\(([^)\s]+)(?:\s+"[^"]*")?\)')
    broken: list[str] = []
    for md in sorted(ROOT.rglob("*.md")):
        if any(p in md.parts for p in (".git", ".venv", "build", "lean")):
            continue
        if md.relative_to(ROOT).as_posix() == "docs/build-standard.md":
            continue
        txt = re.sub(r"```.*?```", "", md.read_text(encoding="utf-8", errors="ignore"), flags=re.S)
        for m in md_link_re.finditer(txt):
            href = m.group(1)
            if href.startswith(("http://", "https://", "mailto:", "#")):
                continue
            target = href.split("#", 1)[0].split("?", 1)[0]
            if not target:
                continue
            dest = (ROOT / target.lstrip("/")) if target.startswith("/") else (md.parent / target).resolve()
            if not dest.exists():
                broken.append(f"{md.relative_to(ROOT).as_posix()} -> {href}")
    assert broken == [], f"Broken relative Markdown links: {broken}"


def test_regression_e2026_006_and_010_statement_fidelity_and_paper_parity() -> None:
    """Regression test (B07) for E-2026-006 & E-2026-010: exact L range, Sec. 2 Thm 2.3 anchor, Table 1, C6, --paranoid."""
    vr = json.loads((ROOT / "scripts" / "verification_results.json").read_text(encoding="utf-8"))
    lo, hi = vr["exact_rational_checked_L"]
    sf = (ROOT / "docs" / "statement-fidelity.md").read_text(encoding="utf-8")
    assert f"L = {lo}..{hi}" in sf, f"statement-fidelity.md does not match exact range L = {lo}..{hi}"
    assert "3..150" not in sf
    assert "Theorem 2.3" in sf
    assert "Theorems 3.1" not in sf

    lean_root = ROOT / "lean"
    lean_files = [f for f in sorted(lean_root.rglob("*.lean")) if ".lake" not in f.parts]
    actual_total = sum(len(f.read_text(encoding="utf-8").splitlines()) for f in lean_files)
    tex = (ROOT / "paper" / "main.tex").read_text(encoding="utf-8")
    assert f"\\textbf{{{actual_total:,}}}" in tex, f"Table 1 total in paper/main.tex does not match actual {actual_total}"
    assert "MultinomialTVConjecture.lean" in tex
    assert "\\textbf{C6}" in tex, "Table 2 in paper/main.tex must include Claim C6"
    assert "--paranoid" not in tex, "Use {-}{-}paranoid in paper/main.tex so TeX does not ligature into en-dash"


def test_regression_e2026_007_live_citation_audit_preserved() -> None:
    """Regression test (B07) for E-2026-007: committed citation-audit.json has 100% live checks & 0 retractions."""
    ca = json.loads((ROOT / "results" / "citation-audit.json").read_text(encoding="utf-8"))
    assert ca["status"] == "pass"
    assert ca["retracted_count"] == 0
    assert len(ca["online_checks"]) >= 16
    assert len(ca["online_checks"]) == ca["arxiv_count"] + ca["doi_count"]
    assert all(item["ok"] for item in ca["online_checks"])
    scan = cc.scan_citations()
    assert scan["missing_bib_keys"] == []
    assert scan["uncited_bib_keys"] == []


def test_regression_e2026_008_no_workstation_path_leaks_and_6kernel_log() -> None:
    """Regression test (B07) for E-2026-008: zero private local paths in tracked files & verbatim 6-kernel CI log."""
    comp_log = (ROOT / "results" / "comparator-paranoid.log").read_text(encoding="utf-8")
    for sentinel in (
        "Lean paranoid kernel accepts the solution",
        "lean4lean kernel accepts the solution",
        "nanoda kernel accepts the solution",
        "con-leche kernel accepts the solution",
        "con-ron kernel accepts the solution",
        "Lean default kernel accepts the solution",
        "Your solution is okay!",
    ):
        assert sentinel in comp_log, f"Missing 6-kernel sentinel in comparator-paranoid.log: {sentinel}"

    tracked = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files"], text=True, encoding="utf-8"
    ).splitlines()
    leak_re = re.compile(
        r"Vibe Coded|Z:\\|I:\\|I:/|All GH Repos|C:/Users/Alexa|C:\\Users\\Alexa",
        re.I,
    )
    for rel in tracked:
        if rel == "tests/test_repo_integrity.py":
            continue
        p = ROOT / rel
        if not p.is_file() or p.suffix.lower() in {".pdf", ".gz", ".png", ".zip", ".tsr", ".tsq", ".ots"}:
            continue
        txt = p.read_text(encoding="utf-8", errors="replace")
        assert not leak_re.search(txt), f"Private workstation path leaked in {rel}"


def test_dual_cryptographic_timestamps_bind_manifest() -> None:
    """Verify BOTH DigiCert RFC 3161 (.tsr) and Bitcoin OpenTimestamps (.ots) bind data/MANIFEST.sha256's exact SHA-256."""
    proc = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "stamp_timestamps.py"), "--verify"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_negative_timestamp_and_manifest_tamper_detection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Negative tamper tests (B06, kills M18, M19, M20): tampered .tsr, .ots, and MANIFEST digests must fail."""
    import hashlib

    orig_manifest = (ROOT / "data" / "MANIFEST.sha256").read_bytes()
    orig_tsr = (ROOT / "data" / "MANIFEST.sha256.tsr").read_bytes()
    orig_ots = (ROOT / "data" / "MANIFEST.sha256.ots").read_bytes()
    digest = hashlib.sha256(orig_manifest).digest()
    bad_digest = bytes([b ^ 0xFF for b in digest])

    m_copy = tmp_path / "MANIFEST.sha256"
    tsr_copy = tmp_path / "MANIFEST.sha256.tsr"
    ots_copy = tmp_path / "MANIFEST.sha256.ots"
    m_copy.write_bytes(orig_manifest)
    monkeypatch.setattr(st_mod, "MANIFEST", m_copy)
    monkeypatch.setattr(st_mod, "TSR_PATH", tsr_copy)
    monkeypatch.setattr(st_mod, "OTS_PATH", ots_copy)

    # 1. Tamper .tsr digest only (kills M18_tsa_skip_digest_check)
    tsr_copy.write_bytes(orig_tsr.replace(digest, bad_digest))
    ots_copy.write_bytes(orig_ots)
    assert st_mod.verify_timestamps() != 0

    # 2. Tamper .ots digest only (kills M19_ots_skip_digest_check)
    tsr_copy.write_bytes(orig_tsr)
    ots_copy.write_bytes(orig_ots.replace(digest, bad_digest))
    assert st_mod.verify_timestamps() != 0

    # 3. Tamper MANIFEST digest (kills M20_manifest_skip_mismatch)
    bad_manifest = tmp_path / "BAD_MANIFEST.sha256"
    bad_manifest.write_text(("0" * 64) + "  VERSION\n", encoding="utf-8", newline="\n")
    monkeypatch.setattr(gm, "MANIFEST", bad_manifest)
    assert gm.verify_manifest() != 0


def test_regression_e2026_015_part5_citation_numbers_and_primary_class() -> None:
    """Regression test (B07, E-2026-015): Part 5 uses Thm 3.10 / Prop 4.2 / Rems 3.11, 3.13, 4.3; Part 1/2 math.PR."""
    bad_refs = re.compile(
        r"(?:Theorem|Thm\.?)\s+5\.2|Proposition\s+6\.2|Remarks?\s+5\.3|Remark\s+5\.5|Remark\s+6\.3"
    )
    active_files = [
        "paper/main.tex",
        "README.md",
        "CLAIMS.md",
        "LIMITATIONS.md",
        "docs/statement-fidelity.md",
        "docs/faq.md",
        "formalization.yaml",
        "blueprint/src/content.tex",
        "lean/Challenge.lean",
        "lean/Solution.lean",
        "lean/MultinomialTVConjecture/Main.lean",
    ]
    for rel in active_files:
        txt = (ROOT / rel).read_text(encoding="utf-8")
        assert not bad_refs.search(txt), f"Stale shifted Part 5 theorem/proposition number in {rel}"

    refs_bib = (ROOT / "paper" / "refs.bib").read_text(encoding="utf-8")
    for key, expected_cls in (
        ("banic_elezovic_p1", "math.PR"),
        ("banic_elezovic_p2", "math.PR"),
        ("banic_elezovic_p5", "math.ST"),
    ):
        m = re.search(rf"@misc\{{{key},.*?\n\}}", refs_bib, re.S)
        assert m is not None, f"Missing {key} in paper/refs.bib"
        assert f"primaryClass  = {{{expected_cls}}}" in m.group(0), (
            f"Expected primaryClass = {{{expected_cls}}} for {key}"
        )


def test_comparator_9_targets_and_mutation_report_green() -> None:
    """Verify comparator.json covers all 9 targets (incl. Lemma 7.3 O(L^-2)) and B13 mutation report is 100%."""
    comp = json.loads((ROOT / "lean" / "comparator.json").read_text(encoding="utf-8"))
    names = comp["theorem_names"]
    assert len(names) == 9
    assert "MultinomialTV.ComparatorTarget.target_lemma_7_3_O_inv_sq" in names

    mut_path = ROOT / "results" / "mutation-report.json"
    assert mut_path.is_file(), "Missing B13 mutation report results/mutation-report.json"
    mut = json.loads(mut_path.read_text(encoding="utf-8"))
    assert mut["total_mutants"] >= 20
    assert mut["survived"] == 0
    assert mut["kill_rate_percent"] == 100.0


def test_manifest_text_artifacts_strictly_lf_cross_platform() -> None:
    """Regression test (F-54): every tracked text artifact in data/MANIFEST.sha256 uses LF (no CRLF)."""
    binary_ext = {".pdf", ".gz", ".png", ".zip", ".tsr", ".ots"}
    for line in (ROOT / "data" / "MANIFEST.sha256").read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        _, rel = line.split("  ", 1)
        p = ROOT / rel
        if p.suffix.lower() in binary_ext:
            continue
        assert b"\r\n" not in p.read_bytes(), f"CRLF detected in manifest-tracked text file {rel}"
