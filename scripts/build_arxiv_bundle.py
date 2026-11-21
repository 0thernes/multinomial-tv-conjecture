#!/usr/bin/env python3
"""
Build the release PDF copy and a self-contained arXiv-compliant LaTeX tarball
(`dist/arxiv_submission.tar.gz`) containing:
  - main.tex
  - main.bbl (pre-generated BibTeX bibliography required by arXiv)
  - figures/fig1_residue_convergence.pdf
  - figures/fig2_reduction_gaussian.pdf
  - 00README.XXX (telling arXiv to compile with pdflatex)

Usage:
    python scripts/build_arxiv_bundle.py
"""

from __future__ import annotations

import shutil
import tarfile
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    paper_dir = root / "paper"
    build_dir = paper_dir / "build"
    dist_dir = root / "dist"
    dist_dir.mkdir(parents=True, exist_ok=True)

    pdf_src = build_dir / "main.pdf"
    bbl_src = build_dir / "main.bbl"
    tex_src = paper_dir / "main.tex"
    fig1 = paper_dir / "figures" / "fig1_residue_convergence.pdf"
    fig2 = paper_dir / "figures" / "fig2_reduction_gaussian.pdf"

    for p in (pdf_src, bbl_src, tex_src, fig1, fig2):
        if not p.exists():
            raise FileNotFoundError(f"Missing required build artifact: {p}")

    pdf_dst = dist_dir / "Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf"
    shutil.copy2(pdf_src, pdf_dst)
    print(f"Copied release PDF: {pdf_dst} ({pdf_dst.stat().st_size:,} bytes)")

    tar_dst = dist_dir / "arxiv_submission.tar.gz"
    with tarfile.open(tar_dst, "w:gz") as tf:
        tf.add(tex_src, arcname="main.tex")
        tf.add(bbl_src, arcname="main.bbl")
        tf.add(fig1, arcname="figures/fig1_residue_convergence.pdf")
        tf.add(fig2, arcname="figures/fig2_reduction_gaussian.pdf")

    print(f"Created arXiv bundle: {tar_dst} ({tar_dst.stat().st_size:,} bytes)")
    with tarfile.open(tar_dst, "r:gz") as tf:
        print("Tarball contents:")
        for member in tf.getmembers():
            print(f"  {member.name} ({member.size:,} bytes)")


if __name__ == "__main__":
    main()
