# Operations, Backups & Offsite Mirror (`docs/operations.md`)

Although `multinomial-tv-conjecture` is a static research and formal-proof repository with no live backend, long-term scientific preservation requires verifiable backups, checksums, and offsite mirrors.

## 1. Cryptographic Integrity & Artifact Manifests

Frozen PDFs, arXiv submission tarballs, verification logs, and data artifacts are hashed in `data/MANIFEST.sha256` via:

```bash
python3 scripts/generate_manifest.py --write
python3 scripts/generate_manifest.py --verify
```

Every `v*` Git tag triggers `.github/workflows/release.yml`, publishing:
- Compiled PDF (`Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf`)
- Byte-reproducible arXiv source bundle (`arxiv_submission.tar.gz`)
- Live axiom audit log (`lean-axioms-all.log`)
- Data manifest (`data-MANIFEST.sha256`), X.509-verified DigiCert RFC 3161 timestamp (`data-MANIFEST.sha256.tsr`, verified via `openssl ts -verify`), and Bitcoin OpenTimestamps proof (`data-MANIFEST.sha256.ots`)
- `SHA256SUMS` + Sigstore SLSA build-provenance attestations (`actions/attest-build-provenance@v2`).

## 2. Creating an Offline Git Bundle Backup

Create a self-contained single-file archival backup of all branches and tags:

```bash
git bundle create multinomial-tv-conjecture-$(cat VERSION).bundle --all
git bundle verify multinomial-tv-conjecture-$(cat VERSION).bundle
sha256sum multinomial-tv-conjecture-$(cat VERSION).bundle
```

Store the verified `.bundle` file on an external drive or secondary cloud storage independent of GitHub.

## 3. Offsite Mirrors & Archival Preservation

1. **Master Research Archive mirror:** Pinned as a Git submodule with frozen PDF, arXiv tarball, and SHA-256 registry entry inside [`0thernes/0thernes-research-archive`](https://github.com/0thernes/0thernes-research-archive) (`0TH-2026-006`).
2. **Software Heritage (SWH) public archival:** Software Heritage's unauthenticated Save Code Now endpoint (`https://archive.softwareheritage.org/api/1/origin/save/git/url/https://github.com/0thernes/multinomial-tv-conjecture/`) is currently gated by an Anubis proof-of-work anti-bot challenge, so obtaining an immutable `swh:1:rev:` identifier requires a manual browser submission at `https://archive.softwareheritage.org/save/` (tracked honestly as open in `docs/run-log.md` and `ROADMAP.md`).
3. **Optional Git remote mirror:** To mirror to a secondary host (e.g., Codeberg or GitLab):
   ```bash
   git remote add mirror <mirror-url>
   git push --mirror mirror
   ```

## 4. Data & Schema Migrations

No mutable database exists. Any future schema upgrade to `repo.yaml` (`repo-standard.schema.json`), `formalization.yaml`, or `lean/lean-toolchain` is tracked in `CHANGELOG.md` and verified via `tests/test_repo_integrity.py` and `scripts/audit-repo.sh`.
