#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Real isolated source-code mutation testing runner for core verification scripts (Build Standard B13).

Copies the lightweight repository tree (excluding lean/.lake and .git) into an isolated temporary
directory, applies AST-verified source mutations one at a time to core verification scripts, executes
the real pytest suite against each mutant, and writes a verbatim report to results/mutation-report.json.
"""
from __future__ import annotations

import argparse
import ast
import json
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class CodeMutant:
    mutant_id: str
    rel_path: str
    description: str
    target: str
    replacement: str
    pytest_target: str


MUTANTS: list[CodeMutant] = [
    # --- scripts/verify_conjecture.py ---
    CodeMutant(
        "M01_direct_abs_drop",
        "scripts/verify_conjecture.py",
        "Drop abs() on (x2 - x1) in h_adj_direct_exact",
        "total += coeff * abs(x2 - x1) * abs(x3 - x2)",
        "total += coeff * (x2 - x1) * abs(x3 - x2)",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M02_direct_denom_off",
        "scripts/verify_conjecture.py",
        "Mutate 3**L denominator to 3**(L + 1) in h_adj_direct_exact",
        "return Fraction(total, 3**L)",
        "return Fraction(total, 3 ** (L + 1))",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M03_p3q_support_bound",
        "scripts/verify_conjecture.py",
        "Weaken out-of-support boundary 2 * x > 3 * q to 2 * x > 3 * q + 2 in p3q_exact",
        "if x < 0 or 2 * x > 3 * q:",
        "if x < 0 or 2 * x > 3 * q + 2:",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M04_mod0_sign_flip",
        "scripts/verify_conjecture.py",
        "Flip -2*B to +2*B in h_adj_1d_exact (mod 0)",
        "return Fraction(3 * q, 9) + 2 * q * p0 * (1 + A - 2 * B) + 4 * (q**2) * p0",
        "return Fraction(3 * q, 9) + 2 * q * p0 * (1 + A + 2 * B) + 4 * (q**2) * p0",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M05_mod1_coeff_shift",
        "scripts/verify_conjecture.py",
        "Perturb 6*q + 1 to 6*q + 2 in h_adj_1d_exact (mod 1)",
        "+ Fraction(2 * (6 * q + 1) * (3 * q + 1), 9) * p0",
        "+ Fraction(2 * (6 * q + 2) * (3 * q + 1), 9) * p0",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M06_mod2_C_sign_flip",
        "scripts/verify_conjecture.py",
        "Flip +4*C to -4*C in h_adj_1d_exact (mod 2)",
        "+ 4 * C",
        "- 4 * C",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M07_domain_guard_L_neg",
        "scripts/verify_conjecture.py",
        "Disable L < 0 guard in h_adj_direct_exact",
        "if L < 0:\n        raise ValueError(f\"L must be non-negative, got {L}\")",
        "if L < -10:\n        raise ValueError(f\"L must be non-negative, got {L}\")",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M08_domain_guard_1d_L3",
        "scripts/verify_conjecture.py",
        "Weaken L < 3 guard to L < 2 in h_adj_1d_exact",
        "if L < 3:\n        raise ValueError(f\"1D reduction requires L >= 3, got {L}\")",
        "if L < 2:\n        raise ValueError(f\"1D reduction requires L >= 3, got {L}\")",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M09_tail_tol_hardcoded_85",
        "scripts/verify_conjecture.py",
        "Reintroduce E-2026-009 hardcoded 1e-85 tail cutoff in sums_abc_mp",
        "tail_tol = mp.power(10, -(mp.mp.dps + 10))",
        "tail_tol = mp.mpf(\"1e-85\")",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M10_mp_mod0_B_sign",
        "scripts/verify_conjecture.py",
        "Flip -2*B to -3*B in h_adj_1d_mp (mod 0)",
        "return (3 * qf) / 9 + 2 * qf * p0 * (1 + A - 2 * B) + 4 * qf * qf * p0",
        "return (3 * qf) / 9 + 2 * qf * p0 * (1 + A - 3 * B) + 4 * qf * qf * p0",
        "tests/test_exact_and_properties.py",
    ),
    CodeMutant(
        "M11_richardson_formula_flip",
        "scripts/verify_conjecture.py",
        "Corrupt Neville-Richardson numerator sign in richardson_extrapolate",
        "table[i] = (hs[i - j] * table[i] - hs[i] * table[i - 1]) / (",
        "table[i] = (hs[i - j] * table[i] + hs[i] * table[i - 1]) / (",
        "tests/test_exact_and_properties.py",
    ),
    # --- scripts/check_readme_axioms.py ---
    CodeMutant(
        "M12_axioms_allow_sorry",
        "scripts/check_readme_axioms.py",
        "Permit sorryAx in ALLOWED axiom set",
        'ALLOWED = {"propext", "Classical.choice", "Quot.sound"}',
        'ALLOWED = {"propext", "Classical.choice", "Quot.sound", "sorryAx"}',
        "tests/test_repo_integrity.py",
    ),
    CodeMutant(
        "M13_axioms_skip_exhaustive",
        "scripts/check_readme_axioms.py",
        "Disable exhaustive sentinel requirement check",
        "if args.require_exhaustive and not ex_match:",
        "if False and args.require_exhaustive and not ex_match:",
        "tests/test_repo_integrity.py",
    ),
    # --- scripts/check_citations.py ---
    CodeMutant(
        "M14_citations_drop_bad_arxiv",
        "scripts/check_citations.py",
        "Clear KNOWN_BAD_ARXIV regression guard (E-2026-001)",
        'KNOWN_BAD_ARXIV = {"2610.1336", "2610.01336"}',
        "KNOWN_BAD_ARXIV: set[str] = set()",
        "tests/test_repo_integrity.py",
    ),
    CodeMutant(
        "M15_citations_skip_parity",
        "scripts/check_citations.py",
        "Return empty parity lists in check_bib_cite_parity",
        "return sorted(cited - bib_keys), sorted(bib_keys - cited), len(bib_keys)",
        "return [], [], len(bib_keys)",
        "tests/test_repo_integrity.py",
    ),
    # --- scripts/build_arxiv_bundle.py ---
    CodeMutant(
        "M16_arxiv_drop_00readme",
        "scripts/build_arxiv_bundle.py",
        "Omit 00README.XXX from arXiv submission bundle (E-2026-003)",
        '("00README.XXX", b"main.tex toplevel\\n"),',
        "",
        "tests/test_repo_integrity.py",
    ),
    CodeMutant(
        "M17_arxiv_nonzero_mtime",
        "scripts/build_arxiv_bundle.py",
        "Set non-zero tar member mtime breaking determinism (B03)",
        "info.mtime = 0",
        "info.mtime = 123456",
        "tests/test_repo_integrity.py",
    ),
    # --- scripts/stamp_timestamps.py ---
    CodeMutant(
        "M18_tsa_skip_sig_verify",
        "scripts/stamp_timestamps.py",
        "Disable OpenSSL X.509 CMS signature verification gate in verify_rfc3161_openssl",
        'if ver.returncode != 0 or "Verification: OK" not in ver.stdout:',
        'if False and (ver.returncode != 0 or "Verification: OK" not in ver.stdout):',
        "tests/test_repo_integrity.py",
    ),
    CodeMutant(
        "M19_ots_skip_digest_check",
        "scripts/stamp_timestamps.py",
        "Disable 32-byte SHA-256 imprint check on OpenTimestamps .ots proof",
        "elif ots_raw[len(prefix) : len(prefix) + 32] != digest:",
        "elif False and ots_raw[len(prefix) : len(prefix) + 32] != digest:",
        "tests/test_repo_integrity.py",
    ),
    # --- scripts/generate_manifest.py ---
    CodeMutant(
        "M20_manifest_skip_mismatch",
        "scripts/generate_manifest.py",
        "Ignore SHA-256 mismatch in verify_manifest",
        "if actual != expected:",
        "if False and actual != expected:",
        "tests/test_repo_integrity.py",
    ),
    # --- scripts/check_citations.py (F-65 retraction & title-match guards) ---
    CodeMutant(
        "M21_citations_drop_updated_by",
        "scripts/check_citations.py",
        "Drop Crossref updated-by retraction check in verify_crossref_payload",
        'for field_name in ("update-to", "updated-by"):',
        'for field_name in ("update-to",):',
        "tests/test_repo_integrity.py",
    ),
    CodeMutant(
        "M22_citations_skip_title_match",
        "scripts/check_citations.py",
        "Weaken DOI title/author metadata mismatch check to always True",
        "metadata_match = False",
        "metadata_match = True",
        "tests/test_repo_integrity.py",
    ),
    # --- scripts/stamp_timestamps.py (F-73 OTS non-empty calendar attestation payload guard) ---
    CodeMutant(
        "M23_ots_skip_payload_check",
        "scripts/stamp_timestamps.py",
        "Disable non-empty calendar attestation payload length guard on .ots proof",
        "elif len(ots_raw) < len(prefix) + 32 + 16:",
        "elif False and len(ots_raw) < len(prefix) + 32 + 16:",
        "tests/test_repo_integrity.py",
    ),
    # --- scripts/check_lean_tokens.py (F-81 centralized Lean forbidden-token lexer guard) ---
    CodeMutant(
        "M24_lean_tokens_allow_sorry",
        "scripts/check_lean_tokens.py",
        "Drop 'sorry' from FORBIDDEN_RE in check_lean_tokens.py",
        'r"\\b(sorry|admit|native_decide|unsafe)\\b"',
        'r"\\b(admit|native_decide|unsafe)\\b"',
        "tests/test_repo_integrity.py",
    ),
]


def stage_isolated_workspace(dst: Path) -> None:
    """Copy tracked and untracked non-ignored repo files (excluding .git, build/, lean/.lake/) into dst."""
    tracked = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files", "--cached", "--others", "--exclude-standard"],
        text=True,
        encoding="utf-8",
    ).splitlines()
    for rel in tracked:
        src = ROOT / rel
        if not src.is_file():
            continue
        out = dst / rel
        out.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, out)


def run_mutants(*, write_report: bool = False) -> int:
    results: list[dict[str, Any]] = []
    killed = 0
    survived = 0

    with tempfile.TemporaryDirectory(prefix="mtv_mut_") as tmp:
        ws = Path(tmp) / "repo"
        ws.mkdir(parents=True, exist_ok=True)
        stage_isolated_workspace(ws)

        # Initialize minimal git repo on branch `main` with an initial commit so git ls-files & Audit-Repo A23 pass
        subprocess.run(["git", "init", "-q", "-b", "main"], cwd=ws, check=True)
        subprocess.run(["git", "config", "user.email", "0_0@0thernes.art"], cwd=ws, check=True)
        subprocess.run(["git", "config", "user.name", "Alexander S. Donahue"], cwd=ws, check=True)
        subprocess.run(["git", "add", "-A"], cwd=ws, check=True)
        subprocess.run(["git", "commit", "-q", "-m", "chore: mutation audit baseline"], cwd=ws, check=True)

        # MANDATORY ANTI-THEATER GATE: unmutated baseline MUST pass 100% before testing any mutant!
        for target_suite in sorted({m.pytest_target for m in MUTANTS}):
            base_proc = subprocess.run(
                [sys.executable, "-m", "pytest", "-q", "--tb=short", target_suite],
                cwd=ws,
                capture_output=True,
                text=True,
                encoding="utf-8",
                timeout=90,
            )
            if base_proc.returncode != 0:
                raise RuntimeError(
                    f"ABORT: Unmutated baseline failed on {target_suite} (refusing to count false kills):\n"
                    f"{base_proc.stdout}\n{base_proc.stderr}"
                )

        for m in MUTANTS:
            target_file = ws / m.rel_path
            original = target_file.read_text(encoding="utf-8")
            if m.target not in original:
                raise RuntimeError(f"Mutant {m.mutant_id}: target snippet not found in {m.rel_path}")
            mutated = original.replace(m.target, m.replacement, 1)
            # Confirm mutated Python source is syntactically valid AST (real semantic mutant, not syntax error!)
            ast.parse(mutated, filename=m.rel_path)
            target_file.write_text(mutated, encoding="utf-8", newline="\n")
            try:
                proc = subprocess.run(
                    [sys.executable, "-m", "pytest", "-q", "--tb=line", m.pytest_target],
                    cwd=ws,
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    timeout=90,
                )
            finally:
                target_file.write_text(original, encoding="utf-8", newline="\n")

            is_killed = proc.returncode != 0
            if is_killed:
                killed += 1
            else:
                survived += 1
            summary_line = ""
            for ln in (proc.stdout + "\n" + proc.stderr).splitlines():
                if ln.startswith("FAILED ") or "failed" in ln.lower():
                    summary_line = ln.strip()
                    break
            results.append(
                {
                    "id": m.mutant_id,
                    "file": m.rel_path,
                    "description": m.description,
                    "pytest_target": m.pytest_target,
                    "status": "killed" if is_killed else "survived",
                    "evidence": summary_line,
                }
            )
            tag = "KILLED  " if is_killed else "SURVIVED"
            print(f"[{tag}] {m.mutant_id} ({m.rel_path}): {m.description}")

    total = len(MUTANTS)
    score_pct = round(100.0 * killed / total, 1) if total else 0.0
    report = {
        "generated_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "tool": "scripts/run_mutation_audit.py (isolated AST-validated source mutation)",
        "total_mutants": total,
        "killed": killed,
        "survived": survived,
        "kill_rate_percent": score_pct,
        "mutants": results,
    }
    if write_report:
        out_path = ROOT / "results" / "mutation-report.json"
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(f"Wrote {out_path}")

    print(f"\nMutation summary: {killed}/{total} killed ({score_pct}%), {survived} survived.")
    return 0 if survived == 0 else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Write results/mutation-report.json")
    args = parser.parse_args()
    return run_mutants(write_report=args.write)


if __name__ == "__main__":
    raise SystemExit(main())
