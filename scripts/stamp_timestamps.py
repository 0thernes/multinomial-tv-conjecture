#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
"""Stamp and cryptographically verify data/MANIFEST.sha256 with BOTH:
  1. DigiCert RFC 3161 TSA (data/MANIFEST.sha256.tsr) — verified via full OpenSSL
     X.509 certificate-chain & CMS signature verification (`openssl ts -verify`).
  2. Multi-calendar Bitcoin OpenTimestamps proof (data/MANIFEST.sha256.ots) —
     verified structurally (OTS v1 magic, SHA-256 op, exact 32-byte digest, and
     non-empty calendar attestation payload; full Bitcoin Merkle check via `ots verify`).

Satisfies Independent Research Verification Playbook v1.3 Checklist Item #26.
Uses temp-directory staging for OpenSSL so Windows paths with literal brackets
never break subprocess or shell invocation.
"""
from __future__ import annotations

import argparse
import hashlib
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "data" / "MANIFEST.sha256"
TSR_PATH = ROOT / "data" / "MANIFEST.sha256.tsr"
OTS_PATH = ROOT / "data" / "MANIFEST.sha256.ots"

# Official OpenTimestamps binary file format header (v1, SHA-256 = 0x08)
OTS_MAGIC = b"\x00OpenTimestamps\x00\x00Proof\x00\xbf\x89\xe2\xe8\x84\xe8\x92\x94"
OTS_VERSION_1 = b"\x01"
OTS_OP_SHA256 = b"\x08"
OTS_FORK_TAG = b"\xff"

OTS_CALENDARS = [
    "https://a.pool.opentimestamps.org/digest",
    "https://b.pool.opentimestamps.org/digest",
    "https://alice.btc.calendar.opentimestamps.org/digest",
]
DIGICERT_TSA_URL = "http://timestamp.digicert.com"


def find_openssl() -> str:
    found = shutil.which("openssl")
    if found:
        return found
    git_openssl = Path(r"C:\Program Files\Git\usr\bin\openssl.exe")
    if git_openssl.is_file():
        return str(git_openssl)
    raise FileNotFoundError("openssl binary not found on PATH or standard Git install")


def find_ca_bundle() -> Path | None:
    """Locate a PEM root CA bundle containing DigiCert roots across Windows, Linux, and macOS."""
    candidates: list[Path] = []
    try:
        import certifi  # type: ignore[import-untyped]

        candidates.append(Path(certifi.where()))
    except ImportError:
        pass
    candidates.extend(
        [
            Path("/etc/ssl/certs/ca-certificates.crt"),
            Path("/etc/ssl/cert.pem"),
            Path("/etc/pki/tls/certs/ca-bundle.crt"),
            Path(r"C:\Program Files\Git\usr\ssl\certs\ca-bundle.crt"),
            Path(r"C:\Program Files\Git\mingw64\etc\ssl\certs\ca-bundle.crt"),
        ]
    )
    for cand in candidates:
        if cand.is_file():
            return cand
    return None


def parse_tsr_message_digest_hex(reply_text: str) -> str | None:
    """Extract the 64-char SHA-256 Message data hex imprint from `openssl ts -reply -text`."""
    m = re.search(r"Message data:\s*\n((?:\s+[0-9a-fA-F]{4}\s+-\s+.*\n)+)", reply_text)
    if not m:
        return None
    hex_bytes: list[str] = []
    for line in m.group(1).splitlines():
        body = line.split(" - ", 1)[1] if " - " in line else ""
        # Hex columns occupy the first 48 chars (16 bytes * 3 chars) before ASCII preview
        hex_part = body[:48]
        hex_bytes.extend(re.findall(r"\b[0-9a-fA-F]{2}\b", hex_part))
    return "".join(hex_bytes).lower() if hex_bytes else None


def verify_rfc3161_openssl(manifest_path: Path, tsr_path: Path, expected_digest_hex: str) -> list[str]:
    """Verify RFC 3161 DER structure, granted status, message imprint, and X.509 CMS signature."""
    errors: list[str] = []
    openssl = find_openssl()
    ca_bundle = find_ca_bundle()
    if ca_bundle is None:
        return ["No system or certifi PEM CA bundle found for OpenSSL RFC 3161 verification"]

    with tempfile.TemporaryDirectory(prefix="mtv_tsa_ver_") as tmp:
        tmp_dir = Path(tmp)
        m_copy = tmp_dir / "MANIFEST.sha256"
        t_copy = tmp_dir / "MANIFEST.sha256.tsr"
        shutil.copy2(manifest_path, m_copy)
        shutil.copy2(tsr_path, t_copy)

        reply = subprocess.run(
            [openssl, "ts", "-reply", "-in", str(t_copy), "-text"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        if reply.returncode != 0:
            errors.append(f"openssl ts -reply failed: {reply.stderr.strip()}")
            return errors
        if "Status: Granted." not in reply.stdout:
            errors.append("RFC 3161 token Status is not 'Granted.'")
        if "Hash Algorithm: sha256" not in reply.stdout:
            errors.append("RFC 3161 token Hash Algorithm is not sha256")
        parsed_hex = parse_tsr_message_digest_hex(reply.stdout)
        if parsed_hex != expected_digest_hex:
            errors.append(
                f"RFC 3161 parsed Message data ({parsed_hex}) != {manifest_path.name} SHA-256 ({expected_digest_hex})"
            )

        ver = subprocess.run(
            [openssl, "ts", "-verify", "-data", str(m_copy), "-in", str(t_copy), "-CAfile", str(ca_bundle)],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        if ver.returncode != 0 or "Verification: OK" not in ver.stdout:
            errors.append(
                f"RFC 3161 X.509 cryptographic signature verification failed: "
                f"{ver.stdout.strip()} {ver.stderr.strip()}".strip()
            )
    return errors


def stamp_rfc3161() -> Path:
    openssl = find_openssl()
    with tempfile.TemporaryDirectory(prefix="mtv_tsa_") as tmp:
        tmp_dir = Path(tmp)
        manifest_copy = tmp_dir / "MANIFEST.sha256"
        tsq_file = tmp_dir / "MANIFEST.sha256.tsq"
        tsr_file = tmp_dir / "MANIFEST.sha256.tsr"
        shutil.copy2(MANIFEST, manifest_copy)
        subprocess.run(
            [openssl, "ts", "-query", "-data", str(manifest_copy), "-sha256", "-cert", "-out", str(tsq_file)],
            check=True,
        )
        req = urllib.request.Request(
            DIGICERT_TSA_URL,
            data=tsq_file.read_bytes(),
            method="POST",
            headers={"Content-Type": "application/timestamp-query"},
        )
        with urllib.request.urlopen(req, timeout=20) as resp:  # noqa: S310
            tsr_bytes = resp.read()
        tsr_file.write_bytes(tsr_bytes)
        txt = subprocess.check_output(
            [openssl, "ts", "-reply", "-in", str(tsr_file), "-text"], text=True, encoding="utf-8"
        )
        if "Status: Granted." not in txt:
            raise RuntimeError(f"DigiCert TSA did not grant timestamp:\n{txt}")
        TSR_PATH.write_bytes(tsr_bytes)
        print(f"PASS: Stamped RFC 3161 TSA -> {TSR_PATH} ({len(tsr_bytes)} bytes)")
        return TSR_PATH


def stamp_opentimestamps() -> Path:
    digest = hashlib.sha256(MANIFEST.read_bytes()).digest()
    calendar_proofs: list[bytes] = []
    for url in OTS_CALENDARS:
        try:
            req = urllib.request.Request(
                url,
                data=digest,
                method="POST",
                headers={
                    "Accept": "application/vnd.opentimestamps.v1",
                    "User-Agent": "OpenTimestamps-Client/0.7",
                    "Content-Type": "application/x-www-form-urlencoded",
                },
            )
            with urllib.request.urlopen(req, timeout=15) as resp:  # noqa: S310
                body = resp.read()
                if resp.status == 200 and len(body) >= 32:
                    calendar_proofs.append(body)
        except Exception as exc:
            print(f"WARN: OpenTimestamps calendar {url} failed: {exc}", file=sys.stderr)

    if not calendar_proofs:
        raise RuntimeError("No OpenTimestamps calendar responded with HTTP 200")

    # Assemble official OTS v1 proof file (forking when multiple calendar attestations succeed)
    parts = [OTS_MAGIC, OTS_VERSION_1, OTS_OP_SHA256, digest]
    for idx, proof in enumerate(calendar_proofs):
        if idx < len(calendar_proofs) - 1:
            parts.append(OTS_FORK_TAG)
        parts.append(proof)
    ots_bytes = b"".join(parts)
    OTS_PATH.write_bytes(ots_bytes)
    print(
        f"PASS: Stamped OpenTimestamps ({len(calendar_proofs)} calendars) -> "
        f"{OTS_PATH} ({len(ots_bytes)} bytes)"
    )
    return OTS_PATH


def verify_timestamps() -> int:
    if not MANIFEST.is_file():
        print(f"ERROR: missing {MANIFEST}", file=sys.stderr)
        return 1
    digest = hashlib.sha256(MANIFEST.read_bytes()).digest()
    errors: list[str] = []

    if not TSR_PATH.is_file():
        errors.append(f"Missing RFC 3161 token: {TSR_PATH}")
    else:
        tsr_raw = TSR_PATH.read_bytes()
        if len(tsr_raw) < 500 or tsr_raw[0] != 0x30:
            errors.append("RFC 3161 token is not a valid DER ASN.1 SEQUENCE")
        else:
            errors.extend(verify_rfc3161_openssl(MANIFEST, TSR_PATH, digest.hex()))

    if not OTS_PATH.is_file():
        errors.append(f"Missing OpenTimestamps proof: {OTS_PATH}")
    else:
        ots_raw = OTS_PATH.read_bytes()
        prefix = OTS_MAGIC + OTS_VERSION_1 + OTS_OP_SHA256
        if not ots_raw.startswith(prefix):
            errors.append("OpenTimestamps proof missing official OTS v1 SHA-256 magic header")
        elif ots_raw[len(prefix) : len(prefix) + 32] != digest:
            errors.append(
                f"OpenTimestamps proof digest does NOT match current {MANIFEST.name} SHA-256 ({digest.hex()})"
            )
        elif len(ots_raw) < len(prefix) + 32 + 16:
            errors.append("OpenTimestamps proof missing calendar attestation payload after digest")

    if errors:
        for err in errors:
            print("ERROR:", err, file=sys.stderr)
        return 1
    print(
        f"PASS: RFC 3161 ({TSR_PATH.name}) X.509 signature verified (openssl ts -verify OK) and "
        f"OpenTimestamps ({OTS_PATH.name}) structurally binds {MANIFEST.name} SHA-256 {digest.hex()}"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--stamp", action="store_true", help="Stamp data/MANIFEST.sha256 via DigiCert TSA + OpenTimestamps")
    group.add_argument("--verify", action="store_true", help="Cryptographically verify RFC 3161 X.509 signature & structural OTS binding against data/MANIFEST.sha256")
    args = parser.parse_args()
    if args.stamp:
        stamp_rfc3161()
        stamp_opentimestamps()
        return verify_timestamps()
    return verify_timestamps()


if __name__ == "__main__":
    raise SystemExit(main())
