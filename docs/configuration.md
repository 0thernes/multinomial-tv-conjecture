# Configuration & Environments (`docs/configuration.md`)

This project uses **no runtime environment variables, secrets, API keys, or external services**. All configuration is declarative and committed in version-controlled manifests.

## Configuration Files

| File | Purpose | Notes |
|---|---|---|
| `VERSION` | Single source of truth for semantic version (read dynamically by scripts & tests) | Must match `CHANGELOG.md`, `CITATION.cff`, `formalization.yaml`, `lean/lakefile.toml`, `llms.txt`, and `docs/media/social-preview.svg`. |
| `lean/lean-toolchain` | Pinned Lean 4 release (`leanprover/lean4:v4.35.0`) | Automatically respected by `elan` and `lake`. |
| `lean/lakefile.toml` | Lean package targets, `autoImplicit = false`, `weak.linter.mathlibStandardSet = true`, Batteries `lintDriver` | Defines `MultinomialTVConjecture`, `Challenge`, `Solution`, `VerifyAxioms`. |
| `lean/lake-manifest.json` | Exact Git commit lockfile for `mathlib`, `batteries`, `Qq`, `aesop`, etc. | Never edit by hand; update only intentionally with a full `lake comparator --paranoid` re-verification. |
| `lean/comparator.json` | Target theorems & permitted axioms for `lake comparator --paranoid` (10 targets) | Maps `Challenge` -> `Solution` with `[propext, Quot.sound, Classical.choice]`. |
| `requirements.txt` | Pinned Python dependencies for verification, pytest, schema validation, linting | Install via `python3 -m pip install -r requirements.txt`. |
| `repo.yaml` | Build Standard v1.2.0 machine-readable manifest | Validated against `repo-standard.schema.json`. |
| `formalization.yaml` | Palomar-compatible authorship, CRediT, toolchain, and AI provenance record | Human- and machine-readable YAML. |
| `.gitleaks.toml` | Secret-scanner allowlist excluding audit scripts' own regex definitions | Used by `gitleaks` in CI. |

## Platform-Specific Notes

- **Linux (Ubuntu 24.04 CI):** Install `bubblewrap` (`sudo apt-get install -y bubblewrap`) for sandboxed `lake comparator --config comparator.json --paranoid`. If Ubuntu 24.04 restricts unprivileged user namespaces, allow userns with `sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0` (see `.github/workflows/lean-verify.yml`).
- **Windows (PowerShell):** When storing the repository under paths containing square brackets (e.g. `C:\Projects\[MyRepo]\...`), always pass `-LiteralPath` to PowerShell file cmdlets (`Audit-Repo.ps1` uses `-LiteralPath` and `[System.IO.Path]::Combine` throughout). Upstream Lean 4.35.0 `lake comparator` requires Linux `bubblewrap`; on Windows, invoke the 5 bundled standalone checkers directly on `leanexport` output or run the full `lake comparator` (six checker runs) inside WSL2/Docker/Ubuntu CI.
- **macOS:** Python test suite, Blueprint, and Lean builds run natively; run the full sandboxed `lake comparator` inside a Linux container or Ubuntu CI.
