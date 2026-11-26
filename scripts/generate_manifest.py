#!/usr/bin/env python3
"""Generate or verify cryptographic SHA-256 manifest data/MANIFEST.sha256."""
from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "data" / "MANIFEST.sha256"

TRACKED_ARTIFACTS = [
    "VERSION",
    "formalization.yaml",
    "CITATION.cff",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/lake-manifest.json",
    "lean/comparator.json",
    "lean/Challenge.lean",
    "lean/Solution.lean",
    "lean/VerifyAxioms.lean",
    "lean/MultinomialTVConjecture.lean",
    "lean/MultinomialTVConjecture/Combinatorial.lean",
    "lean/MultinomialTVConjecture/StirlingRefined.lean",
    "lean/MultinomialTVConjecture/GaussianEulerMaclaurin.lean",
    "lean/MultinomialTVConjecture/LocalAsymptotics.lean",
    "lean/MultinomialTVConjecture/Main.lean",
    "lean/MultinomialTVConjecture/NonVacuity.lean",
    "blueprint/src/content.tex",
    "paper/main.tex",
    "paper/refs.bib",
    "paper/figures/fig1_residue_convergence.pdf",
    "paper/figures/fig2_reduction_gaussian.pdf",
    "dist/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf",
    "dist/arxiv_submission.tar.gz",
    "scripts/verify_conjecture.py",
    "scripts/verification_results.json",
    "results/lean-axioms-all.log",
    "results/comparator-paranoid.log",
    "results/lean-linter.log",
    "results/citation-audit.json",
]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def write_manifest() -> int:
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    lines: list[str] = []
    missing: list[str] = []
    for rel in TRACKED_ARTIFACTS:
        p = ROOT / rel
        if not p.is_file():
            missing.append(rel)
            continue
        lines.append(f"{sha256_file(p)}  {rel}")
    if missing:
        print(f"ERROR: missing artifacts for manifest: {missing}", file=sys.stderr)
        return 1
    MANIFEST.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print(f"Wrote {MANIFEST} ({len(lines)} SHA-256 entries)")
    return 0


def verify_manifest() -> int:
    if not MANIFEST.is_file():
        print(f"ERROR: missing {MANIFEST}", file=sys.stderr)
        return 1
    mismatches: list[str] = []
    count = 0
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        expected, rel = line.split("  ", 1)
        p = ROOT / rel
        if not p.is_file():
            mismatches.append(f"MISSING {rel}")
            continue
        actual = sha256_file(p)
        if actual != expected:
            mismatches.append(f"MISMATCH {rel}: expected {expected}, got {actual}")
        count += 1
    if mismatches:
        for m in mismatches:
            print("ERROR:", m, file=sys.stderr)
        return 1
    print(f"PASS: Verified {count} SHA-256 entries in {MANIFEST.relative_to(ROOT).as_posix()}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true", help="Write data/MANIFEST.sha256")
    group.add_argument("--verify", action="store_true", help="Verify data/MANIFEST.sha256")
    args = parser.parse_args()
    return write_manifest() if args.write else verify_manifest()


if __name__ == "__main__":
    raise SystemExit(main())
