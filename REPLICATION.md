# Replication Protocol (`REPLICATION.md`)

Any independent researcher can reproduce every formal theorem, 6-kernel proof check, exact rational calculation, 80-digit numerical check, Blueprint graph, and PDF build from a clean clone without trusting the author or any pre-computed log.

## 1. Prerequisites

| Tool | Pinned Version | Install |
|---|---|---|
| **Git** | Any modern 2.x | https://git-scm.com |
| **elan / Lean 4** | `leanprover/lean4:v4.35.0` (auto-selected by `lean/lean-toolchain`) | https://github.com/leanprover/elan |
| **Python** | `3.12+` (`requirements.txt` pinned) | https://www.python.org |
| **bubblewrap** *(Linux only, for sandboxed `lake comparator`)* | distro package | `sudo apt-get install -y bubblewrap` |
| **Tectonic** *(optional, for compiling `paper/main.tex`)* | `0.17.0` | https://tectonic-typesetting.github.io |
| **just** *(optional convenience runner)* | `1.x` | https://just.systems |

## 2. Clean-Clone End-to-End Replication Steps

```bash
# 1. Clone and install pinned Python deps
git clone https://github.com/0thernes/multinomial-tv-conjecture.git
cd multinomial-tv-conjecture
python3 -m pip install -r requirements.txt

# 2. Fetch prebuilt Mathlib cache & compile all Lean libraries + isolated Challenge/Solution
cd lean
lake exe cache get
lake build MultinomialTVConjecture Challenge Solution VerifyAxioms

# 3. Run exhaustive axiom audit (verify ALL_THEOREMS_AXIOM_AUDIT_PASS & strict 3-axiom allowlist)
lake env lean VerifyAxioms.lean

# 4. Run 6-kernel comparator (Linux with bubblewrap; add --inadvisably-no-sandbox on Windows/macOS)
lake comparator --config comparator.json --paranoid

# 5. Return to repo root and run Python exact + 80-digit verifier, full test ladder, citations, blueprint, site
cd ..
python3 scripts/verify_conjecture.py
python3 -m pytest -v tests/
python3 scripts/check_citations.py
python3 scripts/check_readme_axioms.py --require-exhaustive
python3 scripts/build_blueprint.py
python3 scripts/build_site.py
bash scripts/audit-repo.sh .
```

## 3. Expected Pass Criteria

1. `lake env lean VerifyAxioms.lean` exits `0`, prints `ALL_THEOREMS_AXIOM_AUDIT_PASS`, and shows every theorem depending on a subset of `[propext, Classical.choice, Quot.sound]`.
2. `lake comparator --config comparator.json --paranoid` exits `0` across all 6 independent kernels (`Lean 4.35.0`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
3. `python3 scripts/verify_conjecture.py` exits `0` with `PASS: Exact rational equality verified for all 43 values L = 3..45 (0/1 error)` and `PASS: All 6 constants match closed forms to > 40 decimal digits!` (actual Richardson errors $< 3\times 10^{-55}$).
4. `python3 -m pytest -v tests/` passes 100% of exact, property-based (`hypothesis`), negative, regression, golden, differential, metamorphic, numeric stability, mutation, and repo-integrity tests.
5. `python3 scripts/check_readme_axioms.py --require-exhaustive` confirms `README.md` matches `results/lean-axioms-all.log` verbatim.

## 4. Replication Log

| Date | Replicator | Environment | Commit / Tag | Lean 6-Kernel | Python / Pytest | Notes |
|---|---|---|---|---|---|---|
| 2026-11-25 | Alexander S. Donahue (author, local clean check) | Windows 11, Lean 4.35.0, Python 3.13.12, Tectonic 0.17.0 | `v2.0.0` | PASS (6 kernels, `--inadvisably-no-sandbox`) | PASS | Full Cycle 1–3 audit; see `docs/run-log.md`. |
| 2026-11-25 | GitHub Actions CI (`ubuntu-24.04`, `windows-latest`, `macos-latest`) | Hosted runners, Lean 4.35.0 + `bubblewrap`, Python 3.12 | `v2.0.0` | PASS (6 kernels, sandboxed Linux) | PASS (3 OSes) | Automated clean-room CI runs on `main`. |

*Independent external replications are invited! Open an issue with the `replication` label containing your environment, commit SHA, and command output to be added to this table.*
