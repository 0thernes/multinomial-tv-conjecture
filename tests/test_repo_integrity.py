"""Repository integrity, regression, schema, axiom-sync, citation, and reproducibility tests.

Covers Build Standard v1.2.0 items:
- A08: Single version source consistency (VERSION, CHANGELOG, CITATION.cff, formalization.yaml, lakefile.toml)
- A32: Agent entry points (AGENTS.md, CLAUDE.md, GEMINI.md, llms.txt)
- B03: Deterministic byte-reproducible arXiv tarball
- B06: Negative tamper-detection tests on axiom parser & forbidden-token lexer
- B07: Regression tests for every erratum E-2026-001..005
- B08: Golden snapshot checks on results/lean-axioms-all.log
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
import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import build_arxiv_bundle as bab  # noqa: E402
import check_citations as cc  # noqa: E402
import check_readme_axioms as cra  # noqa: E402


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


def test_regression_e2026_001_citations_and_no_truncated_arxiv() -> None:
    """Regression test (B07) for E-2026-001: truncated arXiv:2610.1336 must never reappear."""
    scan = cc.scan_citations()
    assert scan["placeholders"] == []
    assert scan["malformed"] == []
    assert "2610.13366" in scan["arxiv_ids"]
    assert "2610.1336" not in scan["arxiv_ids"]


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


def test_regression_e2026_004_axiom_log_and_readme_sync() -> None:
    """Regression & golden snapshot test (B07, B08) for exhaustive Lean axiom log & README sync."""
    log_path = ROOT / "results" / "lean-axioms-all.log"
    assert log_path.is_file()
    log_text = log_path.read_text(encoding="utf-8")
    decls = cra.parse_log(log_text)
    assert len(decls) == 43
    for name, axioms in decls.items():
        assert axioms <= cra.ALLOWED, f"Non-standard axiom in {name}: {axioms}"
    assert cra.EXHAUSTIVE_RE.search(log_text), "Missing ALL_THEOREMS_AXIOM_AUDIT_PASS sentinel"

    # Negative check (B06): tampered log with sorryAx must be detected
    tampered = cra.parse_log("'MultinomialTV.fake' depends on axioms: [propext, sorryAx]\n")
    assert not (tampered["MultinomialTV.fake"] <= cra.ALLOWED)

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
        r"\b(sorry|admit|native_decide|unsafe)\b|^\s*(?:private\s+|protected\s+)?axiom\b|implemented_by|@\[extern"
    )
    proof_files = (
        sorted((ROOT / "lean" / "MultinomialTVConjecture").rglob("*.lean"))
        + [ROOT / "lean" / "MultinomialTVConjecture.lean", ROOT / "lean" / "Solution.lean"]
    )
    assert len(proof_files) >= 8
    for f in proof_files:
        cleaned = strip_lean_comments(f.read_text(encoding="utf-8"))
        for lineno, line in enumerate(cleaned.splitlines(), 1):
            assert not forbidden.search(line), f"Forbidden token in {f}:{lineno}: {line.strip()}"


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
    assert len(nonvac["lean"]) == 18, f"Expected all 18 NonVacuity theorems in Blueprint, got {len(nonvac['lean'])}"


def test_regression_e2026_006_statement_fidelity_and_paper_table1_parity() -> None:
    """Regression test (B07) for E-2026-006: exact L range and exact Table 1 Lean line counts."""
    vr = json.loads((ROOT / "scripts" / "verification_results.json").read_text(encoding="utf-8"))
    lo, hi = vr["exact_rational_checked_L"]
    sf = (ROOT / "docs" / "statement-fidelity.md").read_text(encoding="utf-8")
    assert f"L = {lo}..{hi}" in sf, f"statement-fidelity.md does not match exact range L = {lo}..{hi}"
    assert "3..150" not in sf

    lean_root = ROOT / "lean"
    lean_files = [f for f in sorted(lean_root.rglob("*.lean")) if ".lake" not in f.parts]
    actual_total = sum(len(f.read_text(encoding="utf-8").splitlines()) for f in lean_files)
    tex = (ROOT / "paper" / "main.tex").read_text(encoding="utf-8")
    assert f"\\textbf{{{actual_total:,}}}" in tex, f"Table 1 total in paper/main.tex does not match actual {actual_total}"
    assert "MultinomialTVConjecture.lean" in tex


def test_regression_e2026_007_live_citation_audit_preserved() -> None:
    """Regression test (B07) for E-2026-007: committed citation-audit.json has 18/18 online checks & 0 retractions."""
    ca = json.loads((ROOT / "results" / "citation-audit.json").read_text(encoding="utf-8"))
    assert ca["status"] == "pass"
    assert ca["retracted_count"] == 0
    assert len(ca["online_checks"]) == 18
    assert all(item["ok"] for item in ca["online_checks"])


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
    leak_re = re.compile(r"Vibe Coded|Z:\\\\|C:/Users/Alexa|C:\\\\Users\\\\Alexa", re.I)
    for rel in tracked:
        if rel == "tests/test_repo_integrity.py":
            continue
        p = ROOT / rel
        if not p.is_file() or p.suffix.lower() in {".pdf", ".gz", ".png", ".zip", ".tsr", ".tsq"}:
            continue
        txt = p.read_text(encoding="utf-8", errors="replace")
        assert not leak_re.search(txt), f"Private workstation path leaked in {rel}"


def test_rfc3161_timestamp_present_and_nonempty() -> None:
    """Verify DigiCert RFC 3161 TSA response for data/MANIFEST.sha256 is committed and DER-encoded."""
    tsr = ROOT / "data" / "MANIFEST.sha256.tsr"
    assert tsr.is_file(), "Missing RFC 3161 timestamp response data/MANIFEST.sha256.tsr"
    raw = tsr.read_bytes()
    assert len(raw) > 500, "RFC 3161 timestamp response unexpectedly small"
    assert raw[0] == 0x30, "RFC 3161 response must start with ASN.1 SEQUENCE tag 0x30"
