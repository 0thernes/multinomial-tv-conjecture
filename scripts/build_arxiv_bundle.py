#!/usr/bin/env python3
"""Build a clean, byte-reproducible arXiv LaTeX submission tarball.

Packages `paper/main.tex`, `paper/refs.bib`, `paper/build/main.bbl` (if present),
and a generated `00README.XXX` directive (`main.tex toplevel`) into
`dist/arxiv_submission.tar.gz` with deterministic tar headers (`mtime=0`,
`uid=0`, `gid=0`, sorted members, gzip `mtime=0`).
"""
from __future__ import annotations

import gzip
import hashlib
import io
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPER = ROOT / "paper"
DIST = ROOT / "dist"


def add_bytes_deterministic(tf: tarfile.TarFile, arcname: str, data: bytes) -> None:
    info = tarfile.TarInfo(name=arcname)
    info.size = len(data)
    info.mtime = 0
    info.mode = 0o644
    info.uid = 0
    info.gid = 0
    info.uname = ""
    info.gname = ""
    tf.addfile(info, io.BytesIO(data))


def build_bundle(out_tar: Path | None = None) -> tuple[Path, str]:
    DIST.mkdir(parents=True, exist_ok=True)
    target = out_tar if out_tar is not None else DIST / "arxiv_submission.tar.gz"

    main_tex = PAPER / "main.tex"
    refs_bib = PAPER / "refs.bib"
    bbl = PAPER / "build" / "main.bbl"

    if not main_tex.is_file():
        raise FileNotFoundError(f"Missing {main_tex}")
    if not refs_bib.is_file():
        raise FileNotFoundError(f"Missing {refs_bib}")

    entries: list[tuple[str, bytes]] = [
        ("00README.XXX", b"main.tex toplevel\n"),
        ("main.tex", main_tex.read_bytes().replace(b"\r\n", b"\n")),
        ("refs.bib", refs_bib.read_bytes().replace(b"\r\n", b"\n")),
    ]
    if bbl.is_file():
        entries.append(("main.bbl", bbl.read_bytes().replace(b"\r\n", b"\n")))
    fig_dir = PAPER / "figures"
    if fig_dir.is_dir():
        for fig in sorted(fig_dir.glob("*.pdf")):
            entries.append((f"figures/{fig.name}", fig.read_bytes()))
    entries.sort(key=lambda pair: pair[0])

    raw_tar = io.BytesIO()
    with tarfile.open(fileobj=raw_tar, mode="w", format=tarfile.USTAR_FORMAT) as tf:
        for arcname, data in entries:
            add_bytes_deterministic(tf, arcname, data)

    with target.open("wb") as raw_out:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw_out, mtime=0, compresslevel=9) as gz:
            gz.write(raw_tar.getvalue())

    digest = hashlib.sha256(target.read_bytes()).hexdigest()
    return target, digest


def main() -> int:
    target, digest = build_bundle()
    print(f"Wrote {target} ({target.stat().st_size} bytes)")
    print(f"SHA-256: {digest}")
    with tarfile.open(target, "r:gz") as tf:
        print("Contents:", tf.getnames())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
