# Proof of Conjecture 7.7 on the Second-Order Variance Constant of Multinomial Discrete Total Variation

[![Lean 4.35.0 & 6-Kernel Verify](https://github.com/0thernes/multinomial-tv-conjecture/actions/workflows/lean-verify.yml/badge.svg)](https://github.com/0thernes/multinomial-tv-conjecture/actions/workflows/lean-verify.yml)
[![Cross-Platform CI](https://github.com/0thernes/multinomial-tv-conjecture/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/multinomial-tv-conjecture/actions/workflows/ci.yml)
[![Lean Blueprint](https://img.shields.io/badge/Lean%204-Interactive%20Blueprint-0284c7)](https://0thernes.github.io/multinomial-tv-conjecture/blueprint/)
[![License: Apache-2.0](https://img.shields.io/badge/Code%20License-Apache--2.0-blue.svg)](LICENSE)
[![Docs: CC BY 4.0](https://img.shields.io/badge/Paper%20%26%20Docs-CC%20BY%204.0-lightgrey.svg)](LICENSE-DOCS)
[![Project Status: Active](https://www.repostatus.org/badges/latest/active.svg)](https://www.repostatus.org/#active)

A complete, machine-checked **Lean 4.35.0** formal proof (verified across **6 independent proof kernels**), independent exact-rational and 80-digit Python verification suite, interactive Lean 4 Blueprint, and AMS-LaTeX preprint resolving **Conjecture 7.7 (`conj:atriangle`)** of Nikola Banić and Neven Elezović, *Discrete total variation under the multinomial, Part 2: variance under the uniform null* (`arXiv:2610.17046v1`, 2026), together with its cyclic corollary in Part 5 (`arXiv:2611.14735v1`, Theorem 5.2).

**Author:** Alexander Stephen Donahue · Independent Researcher, Spokane, WA, USA · ORCID [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648) · `0_0@0thernes.art`
**Status:** Active research preprint (`v2.0.0`, 2026-11-25) — **NOT externally peer reviewed**; independent human line-by-line statement-fidelity audit remains open (see [docs/statement-fidelity.md](docs/statement-fidelity.md) and [LIMITATIONS.md](LIMITATIONS.md)).

---

## Main Theorem (Conjecture 7.7 Proved)

For $(X_1, X_2, X_3) \sim \mathrm{Mult}(L; \tfrac{1}{3}, \tfrac{1}{3}, \tfrac{1}{3})$, define the adjacent pair expectation $h_{\mathrm{adj}}(L) := \mathbb{E}[|X_2 - X_1|\,|X_3 - X_2|]$, $c_L := \frac{2\sqrt{3}}{3\pi} + \frac{1}{9}$, and $a_* := -\frac{2\sqrt{3}}{9\pi}$. For each residue class $r \in \{0, 1, 2\}$, the $1/L$-order limit
$$b_r := \lim_{\substack{L \to \infty \\ L \equiv r \pmod{3}}} L\bigl(h_{\mathrm{adj}}(L) - c_L L - a_*\bigr)$$
exists and equals:

$$b_0 = \frac{32\sqrt{3}}{81\pi}, \qquad b_1 = b_2 = -\frac{22\sqrt{3}}{81\pi}, \qquad d_0 = \frac{b_0 + b_1 + b_2}{3} = -\frac{4\sqrt{3}}{81\pi},$$

$$b_r = d_0 + \frac{4\sqrt{3}}{9\pi}\cos\!\left(\frac{2\pi r}{3}\right) \quad (r \in \{0, 1, 2\}),$$

$$a_\triangle = \frac{1}{32} + \frac{\pi}{9}(b_0 + b_1 + b_2) = \frac{1}{32} - \frac{4\sqrt{3}}{243}, \qquad \gamma_2 = \frac{64 a_\triangle - 3}{32\pi} = -\frac{1}{32\pi} - \frac{8\sqrt{3}}{243\pi}.$$

Conditioned on Theorem 7.6 of Banić & Elezović Part 2 (`arXiv:2610.17046v1`) and Theorem 5.2 of Part 5 (`arXiv:2611.14735v1`), substituting $a_\triangle$ immediately gives the exact closed-form $O(N^{-2})$ variance coefficients for all $n \ge 5$:
$$\gamma(n) = -\frac{n(n+1)}{32\pi} - \frac{8\sqrt{3}\,n(n-2)}{243\pi} + \frac{n-1}{8\pi n}, \qquad \gamma_c(n) = -\frac{n(n+4)}{32\pi} - \frac{8\sqrt{3}\,n^2}{243\pi}.$$

---

## 5-Second Proof Verification (Verbatim `#print axioms` Output)

Every theorem in the formalization—**576 theorems** exhaustively checked by `Lean.collectAxioms` in [lean/VerifyAxioms.lean](lean/VerifyAxioms.lean)—depends strictly on Lean's three standard classical axioms `[propext, Classical.choice, Quot.sound]`, with **zero `sorry`**, **zero `admit`**, **zero custom `axiom`**, **zero `native_decide`**, and **zero `unsafe`** anywhere in `lean/MultinomialTVConjecture/` or `lean/Solution.lean`.

Verbatim output of `cd lean && lake env lean VerifyAxioms.lean` (enforced against `results/lean-axioms-all.log` by `scripts/check_readme_axioms.py --require-exhaustive` in CI):

```text
'MultinomialTV.hAdj_eq_nested_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.hAdj_mod0' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.hAdj_mod1' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.hAdj_mod2' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.tendsto_hAdj_mod0' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.tendsto_hAdj_mod1' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.tendsto_hAdj_mod2' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.conjecture_7_7_aTriangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.conjecture_7_7_gamma2' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.conjecture_7_7_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.bRes_cosine_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.conjecture_7_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.gamma_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.gamma_cyclic_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.ComparatorTarget.target_conjecture_7_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.ComparatorTarget.target_gamma_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'MultinomialTV.ComparatorTarget.target_gamma_cyclic_closed_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ALL_THEOREMS_AXIOM_AUDIT_PASS: checked 576 theorems across MultinomialTV — 0 disallowed axioms.
```

---

## Six-Kernel Verification & Non-Vacuity Stack

To separate statement auditing from proof internals, [lean/Challenge.lean](lean/Challenge.lean) (~105 lines) imports **only Mathlib** (zero files from our proof library) and states the 6 target theorems verbatim. [lean/Solution.lean](lean/Solution.lean) proves those exact declarations without `sorry`, and `lake comparator --config comparator.json --paranoid` checks exported proof terms across **six independent kernels**:

| Verification Check | Tool / File | Scope |
|---|---|---|
| **Official C++ kernel** | `lean 4.35.0` / `lake build` | All 576 theorems across `MultinomialTVConjecture`, `Solution`, `VerifyAxioms` |
| **Five independent external kernels** | `lake comparator --config comparator.json --paranoid` (`leanchecker-paranoid`, `lean4lean`, `nanoda 0.4.19`, `con-leche`, `con-ron`) | All 6 headline theorems (`Challenge.lean` vs. `Solution.lean`) |
| **Exhaustive axiom audit** | `lean/VerifyAxioms.lean` (`Lean.collectAxioms`) | 576/576 theorems strictly within `[propext, Classical.choice, Quot.sound]` |
| **Batteries / Mathlib linters** | `lake exe runLinter MultinomialTVConjecture` | 0 warnings across 15 linters (`autoImplicit = false`) |
| **Non-vacuity & adversarial refutations** | `lean/MultinomialTVConjecture/NonVacuity.lean` | 18 witnesses (`hAdj 0..5`, strict signs, `aTriangle ≠ 1/32`, `d0 ≠ 0`, `n=5`) |
| **Exact rational & 80-digit numerical oracle** | `scripts/verify_conjecture.py` & `tests/` | Exact `Fraction` equality for $L=3..45$ (0/1 error); 28-pt Richardson error $< 3 \times 10^{-55}$ (>54 digits) |

See [docs/statement-fidelity.md](docs/statement-fidelity.md) for the declaration-by-declaration mapping to Banić & Elezović (`arXiv:2610.17046v1`), and [CLAIMS.md](CLAIMS.md) for explicit falsification criteria ("What Would Prove Us Wrong").

---

## Quickstart

Verify the formal proof and independent numerical checks from a clean clone:

```bash
git clone https://github.com/0thernes/multinomial-tv-conjecture.git
cd multinomial-tv-conjecture

# 1. Install pinned Python verification & test dependencies
python3 -m pip install -r requirements.txt

# 2. Fetch pinned Mathlib cache, build Lean 4.35.0 proofs, audit axioms & run 6-kernel comparator
cd lean
lake exe cache get
lake build MultinomialTVConjecture Challenge Solution VerifyAxioms
lake env lean VerifyAxioms.lean
lake comparator --config comparator.json --paranoid   # Linux with bubblewrap
cd ..

# 3. Run independent exact rational + 80-digit checks, pytest ladder, citations, Blueprint & repo audit
python3 scripts/verify_conjecture.py
python3 -m pytest -v tests/
python3 scripts/check_citations.py
python3 scripts/check_readme_axioms.py --require-exhaustive
python3 scripts/build_blueprint.py
python3 scripts/build_site.py
```

Full step-by-step instructions for Linux, macOS, and Windows appear in [REPLICATION.md](REPLICATION.md).

---

## Usage

Common one-word workflows via `just` (see [justfile](justfile) and [scripts/dev.sh](scripts/dev.sh)):

```bash
just verify-lean     # Build Lean, scan forbidden tokens, run VerifyAxioms + 6-kernel comparator
just verify-numeric  # Run exact rational (L=3..45) and 80-digit mpmath checks
just test            # Run full pytest ladder (exact, Hypothesis, negative, regression, golden, mutation, stability)
just blueprint       # Validate every \lean{...} tag and build interactive SVG dependency Blueprint
just paper           # Compile AMS-LaTeX preprint via Tectonic & build byte-reproducible arXiv bundle
just reproduce       # End-to-end clean reproduction & Build Standard v1.2.0 audit
just audit           # Score repository against Build Standard v1.2.0 (90 items)
```

---

## Repository Structure

| Path | Description |
|---|---|
| `lean/MultinomialTVConjecture/` | Core Lean 4.35.0 proof (`Combinatorial`, `StirlingRefined`, `GaussianEulerMaclaurin`, `LocalAsymptotics`, `Main`, `NonVacuity`) |
| `lean/Challenge.lean`, `Solution.lean`, `comparator.json` | Isolated Mathlib-only target statements & 6-kernel comparator bridge |
| `lean/VerifyAxioms.lean` | Exhaustive `Lean.collectAxioms` metaprogram + 43 explicit `#print axioms` checks |
| `paper/main.tex`, `paper/refs.bib`, `paper/figures/` | AMS-LaTeX manuscript source (`v2.0.0`), verified BibTeX, and publication figures |
| `dist/` | Compiled PDF (`Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf`) and byte-reproducible `arxiv_submission.tar.gz` |
| `blueprint/src/content.tex` | Lean 4 dependency Blueprint validated against `lean/` by `scripts/build_blueprint.py` |
| `scripts/` | Independent numerical verifier, arXiv bundler, axiom/citation/Blueprint/site/manifest/Build Standard scripts |
| `tests/` | Automated `pytest` + `hypothesis` test ladder |
| `docs/` | Architecture, statement-fidelity table, verification stack, ADRs, threat model, operations, FAQ, glossary, red-team review |
| `results/`, `data/MANIFEST.sha256` | Live axiom/comparator/linter/citation logs and cryptographic SHA-256 artifact manifest |

---

## Maintenance Status

**Status: Active** (repostatus: `active`). The formal proof of Conjecture 7.7 is complete and frozen at `v2.0.0`. Maintenance covers toolchain updates if requested, recording external human statement-fidelity audits in [docs/statement-fidelity.md](docs/statement-fidelity.md) and clean-room replications in [REPLICATION.md](REPLICATION.md), and logging any errata in [ERRATA.md](ERRATA.md).

## Citation & Licensing

- **Code, Lean 4 proofs, scripts, and tests:** [Apache License 2.0](LICENSE) (`SPDX-License-Identifier: Apache-2.0`).
- **Manuscript, figures, Blueprint, and documentation:** [CC BY 4.0](LICENSE-DOCS) (`SPDX-License-Identifier: CC-BY-4.0`).
- **Attribution & third-party notices:** See [NOTICE](NOTICE), [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), [CITATION.cff](CITATION.cff), and [formalization.yaml](formalization.yaml).
