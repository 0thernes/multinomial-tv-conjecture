# Replication Protocol (`REPLICATION.md`)

Any independent researcher can reproduce every formal theorem, comparator replay (six checker runs), exact rational calculation, 80-digit numerical check, Blueprint graph, and PDF build from a clean clone without trusting the author or any pre-computed log.

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

# 4. Run comparator (six checker runs; Linux with bubblewrap, or WSL2/Docker on Windows/macOS)
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
2. `lake comparator --config comparator.json --paranoid` exits `0` across all six checker runs (`Lean paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`, `Lean default`; two of the six runs are the Lean kernel).
3. `python3 scripts/verify_conjecture.py` exits `0` with `PASS: Exact rational equality verified for all 43 values L = 3..45 (0/1 error)` and `PASS: All 6 constants match closed forms to > 40 decimal digits!` (actual Richardson errors $< 3\times 10^{-55}$).
4. `python3 -m pytest -v tests/` passes 100% of exact, property-based (`hypothesis`), negative, regression, golden, differential, metamorphic, numeric stability, mutation, and repo-integrity tests.
5. `python3 scripts/check_readme_axioms.py --require-exhaustive` confirms `README.md`'s 23-line excerpt and exact theorem count match `results/lean-axioms-all.log`.

## 4. Replication Log

> **Independent External Operator Status (`B44: partial`):** All clean-room replications logged below were executed either by the author locally or by public GitHub Actions hosted runners across Linux (`ubuntu-24.04`), Windows, and macOS. **Zero independent outside human operators have yet submitted an external replication.** Build Standard item `B44` is therefore recorded honestly as `partial` in `repo.yaml` until an external researcher submits an independent replication log.
>
> **Note on historical entries (`2026-11-26`):** Older rows (`v2.0.0`–`v2.3.0`) below are kept as dated records; where they say `"6/6 kernels"` or `"live negative rejection"`, read six checker runs of `lake comparator --paranoid` (two of which are the Lean kernel) and an elaboration smoke test (the mathematical refutation of `aTriangle = 1/32` is the proved theorem `adversarial_aTriangle_ne_one_div_32`). See [ERRATA.md](ERRATA.md).

| Date | Replicator | Environment | Commit / Tag | Lean Comparator (6 Checker Runs) | Python / Pytest | Notes |
|---|---|---|---|---|---|---|
| 2026-11-25 | Alexander S. Donahue (author, local clean check) | Windows 11, Lean 4.35.0, Python 3.13.12, Tectonic 0.17.0 | `v2.0.0` | PASS (5/6 kernels directly on Windows: `lean`, `leanchecker-paranoid`, `nanoda`, `con-leche`, `con-ron`; full 6/6 incl. `lean4lean` in Ubuntu 24.04 CI) | PASS (24/24 pytest) | Initial v2.0.0 release check; see `docs/run-log.md`. |
| 2026-11-25 | GitHub Actions CI (`ubuntu-24.04`, `windows-latest`, `macos-latest`) | Hosted runners, Lean 4.35.0 + `bubblewrap`, Python 3.12 | `v2.0.0` (`18d95f0`) | PASS (6/6 kernels, sandboxed Linux CI `#45723630668`, Rekor `4114226539`) | PASS (3 OSes, `#45723630598`) | Automated clean-room CI runs on `main`. |
| 2026-11-25 | Alexander S. Donahue + GitHub Actions CI | Windows 11 local + Ubuntu 24.04 / Windows / macOS CI | `v2.1.0` (`6b0bca3`) | PASS (6/6 kernels + live negative kernel rejection, `#45741323731`, Rekor `4116347212`) | PASS (3 OSes, `#45741323610` + DigiCert RFC 3161 TSA) | Full Cycle 1–3 hardening (`F-17`–`F-29`); zero-overfull PDF; `pytest==9.0.3` (0 Dependabot alerts). |
| 2026-11-25 | Alexander S. Donahue + GitHub Actions CI | Windows 11 local + Ubuntu 24.04 / Windows / macOS CI | `v2.2.0` (`5ceae10`) | PASS (all 10 Lean files on `module` headers, 723 theorems audited, 6/6 kernels + live negative rejection, `#45747471704`, Rekor `4117130014`) | PASS (3 OSes `#45747471636` + RFC 3161 TSA + OpenTimestamps `.ots`) | Deep Playbook v1.3 + Build Standard v1.2.0 pass (`F-30`–`F-44`, `66/66` `100.0%`); SPDX headers, `plainurl` clickable DOIs, dynamic `mpmath` tail cutoff. |
| 2026-11-26 | Alexander S. Donahue + GitHub Actions CI | Windows 11 local + Ubuntu 24.04 / Windows / macOS CI | `v2.3.0` (`a1d84d7` + LF/CVE fix) | PASS (`weak.linter.mathlibStandardSet = true`, 0 warnings, Corollary 1.2(iii) formalized, 8 targets / 20 NonVacuity / 730 audited theorems, 6/6 kernels `#45830919144`, Rekor `4127149586`) | PASS (3 OSes + strict CSP/SRI + `osv-scanner v2.7.1` 0 CVEs w/ `pygments==2.20.0` + dual `.tsr`/`.ots`) | Round 4 3-cycle audit (`F-45`–`F-54`): R4 auto-PRs disabled, LF manifest guard, dynamic portal counts, `0.00pt` 20-page PDF, `66/66` Build Standard v1.2.0. |
| 2026-11-26 | Alexander S. Donahue + GitHub Actions CI | Windows 11 local + Ubuntu 24.04 / Windows / macOS CI | `v2.5.0` (`ad699d8`) | PASS (`lemma_7_3_O_inv_sq` Target 9 proved, 9 targets / 20 NonVacuity / 187 author theorems / 892 audited constants, six comparator checker runs `lean4lean` 41,897 / `con-leche` & `con-ron` 41,900 / `nanoda` / Lean paranoid & default, `#45942992816`, Rekor `4141986348` / att. `72947181`) | PASS (42/42 pytest across 3 OSes `#45942992834`, 20/20 isolated code mutants killed, 3,000+ Hypothesis cases, 1,140-input differential oracle, Release `#45942993056` Rekor `4141888347` verified live via `gh attestation verify`) | Unified `v2.4.0` + 2026-11-26 statement audit closure (`E-2026-015`..`018`, `F-55`–`F-63`); `0.00pt` 22-page PDF; honest `B44: partial`; SWH unauthenticated endpoint gated by Anubis PoW (awaiting manual browser submission). |

*Independent external replications are invited! Open an issue with the `replication` label containing your environment, commit SHA, and command output to be added to this table.*
