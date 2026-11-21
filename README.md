# Resolution and Lean 4 Verification of Conjecture 7.7 on Multinomial Discrete Total Variation

[![Formal Verification & Reproducibility CI](https://github.com/0thernes/multinomial-tv-conjecture/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/multinomial-tv-conjecture/actions/workflows/ci.yml)
[![Lean 4.35.0](https://img.shields.io/badge/Lean_4-v4.35.0_%7C_Zero_Sorry_%7C_Standard_Axioms-2ea44f.svg)](lean/VerifyAxioms.lean)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--8168--9648-A6CE39.svg)](https://orcid.org/0009-0006-8168-9648)
[![License: MIT / CC BY 4.0](https://img.shields.io/badge/License-MIT_(code)_%7C_CC_BY_4.0_(paper)-blue.svg)](LICENSE)

> **Author:** Alexander Stephen Donahue, **0thernes LLC** (`0_0@0thernes.art`)  
> **Manuscript PDF:** [`dist/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf`](dist/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf) · **arXiv Source Bundle:** [`dist/arxiv_submission.tar.gz`](dist/arxiv_submission.tar.gz)

This repository contains a complete, self-contained mathematical proof, publication-ready LaTeX manuscript, independent arbitrary-precision numerical verification suite, and sorry-free **Lean 4** formal verification of **Conjecture 7.7** (`conj:atriangle`, *"Closed form of the adjacent second-order constant"*) from:

- **N. Banić and N. Elezović**, *Discrete total variation under the multinomial, Part 2: variance under the uniform null*, [arXiv:2610.17046v1](https://arxiv.org/abs/2610.17046v1) (2026).
- Confirmed still open as of November 2026 in **Part 5**, *Discrete total variation under the multinomial, Part 5: cyclic total variation*, [arXiv:2611.14735v1](https://arxiv.org/abs/2611.14735v1) (2026).

---

## Main Theorem (Now Proved and Machine-Checked)

For uniform three-bin multinomial counts $(X_1, X_2, X_3) \sim \mathrm{Mult}(\ell; \frac{1}{3}, \frac{1}{3}, \frac{1}{3})$, consider the adjacent skeleton
$$h_{\mathrm{adj}}(\ell) := \mathbb{E}\bigl[|X_2 - X_1|\,|X_3 - X_2|\bigr] = 3^{-\ell}\sum_{\substack{x_1+x_2+x_3=\ell \\ x_i \ge 0}} \frac{\ell!}{x_1!\,x_2!\,x_3!}\,|x_2 - x_1|\,|x_3 - x_2|.$$
With $c_L := \frac{2\sqrt{3}}{3\pi} + \frac{1}{9}$ and $a_* := -\frac{2\sqrt{3}}{9\pi}$, define for each residue class $r \in \{0, 1, 2\}$ the $1/\ell$ limit
$$b_r := \lim_{\substack{\ell \to \infty \\ \ell \equiv r \pmod 3}} \ell\bigl(h_{\mathrm{adj}}(\ell) - c_L \ell - a_*\bigr),$$
and set $d_0 := \frac{1}{3}(b_0 + b_1 + b_2)$, $a_\triangle := \frac{1}{32} + \frac{\pi}{9}(b_0 + b_1 + b_2)$, and $\gamma_2 := \frac{64 a_\triangle - 3}{32\pi}$.

**Theorem (`MultinomialTV.conjecture_7_7`):**
$$b_0 = \frac{32\sqrt{3}}{81\pi}, \qquad b_1 = b_2 = -\frac{22\sqrt{3}}{81\pi}, \qquad d_0 = -\frac{4\sqrt{3}}{81\pi},$$
$$b_r = d_0 + \frac{4\sqrt{3}}{9\pi}\cos\!\left(\frac{2\pi r}{3}\right) \quad (r \in \{0, 1, 2\}),$$
$$a_\triangle = \frac{1}{32} - \frac{4\sqrt{3}}{243}, \qquad \gamma_2 = -\frac{1}{32\pi} - \frac{8\sqrt{3}}{243\pi}.$$

### Unconditional Consequences for Discrete Total Variation Variance

Combining Theorem 1.1 with Theorem 7.6 of [arXiv:2610.17046v1](https://arxiv.org/abs/2610.17046v1) and Theorem 5.2 / Proposition 6.2 of [arXiv:2611.14735v1](https://arxiv.org/abs/2611.14735v1) makes the $O(N^{-2})$ variance coefficients of both the linear statistic $d = \sum_{i=1}^{n-1}|X_{i+1}-X_i|$ and the cyclic statistic $d^c = \sum_{i=1}^{n}|X_{i+1}-X_i|$ **unconditional** for all $n \ge 5$:
$$\gamma(n) = -\frac{n(n+1)}{32\pi} - \frac{8\sqrt{3}\,n(n-2)}{243\pi} + \frac{n-1}{8\pi n}, \qquad \gamma_c(n) = -\frac{n(n+4)}{32\pi} - \frac{8\sqrt{3}\,n^2}{243\pi},$$
together with the degenerate small-bin regimes $\gamma(3; N)$, $\gamma(4; N)$ and the exact algebraic input $\gamma_2$ entering the sub-leading ridge-mode constant $C_{1/2} = 2\gamma_2 K_0^{3/2}/\beta_1 \approx -42.0471$.

---

## Key Mathematical Insight

The Fourier/characteristic-function approach in [arXiv:2610.17046v1](https://arxiv.org/abs/2610.17046v1) required evaluating two-dimensional Hadamard finite-part distributional pairings at order $\ell^{-5/2}$. We bypass two-dimensional distributions completely via an **exact combinatorial 2D-to-1D reduction**:
1. $S_3$-symmetrization folds the simplex $\Delta_\ell$ onto the strict wedge $a < b < c$.
2. Two exact finite-difference telescopes plus a 6-way orbit partition collapse $h_{\mathrm{adj}}(\ell)$ identically into the central trinomial probability $p_{3q}(q) = (3q)!/(3^{3q}(q!)^3)$ and three 1D normalized central sums $A(q), B(q), C(q)$.
3. Sharp non-asymptotic Stirling bounds ($\frac{1}{12n} - \frac{1}{15n^3} \le R(n) \le \frac{1}{12n}$), consecutive-ratio Gaussian tail bounds beyond $K_q = \lfloor q^{5/8} \rfloor$, and a self-contained cubic Euler–Maclaurin theorem for $t^{2j+1}e^{-3t^2}$ (capturing the exact $-\frac{h^2}{12}$ Bernoulli shift at $j=0$) yield $A(q), B(q), C(q)$ to $o(q^{-1})$ and close all three residue classes.

---

## Repository Structure & Lean 4 Audit

| Path | Role | Size / Verification |
|---|---|---|
| [`lean/MultinomialTVConjecture/Combinatorial.lean`](lean/MultinomialTVConjecture/Combinatorial.lean) | Exact 2D-to-1D reduction (`hAdj_mod0`, `hAdj_mod1`, `hAdj_mod2`) | 1,615 lines · 0 `sorry` |
| [`lean/MultinomialTVConjecture/StirlingRefined.lean`](lean/MultinomialTVConjecture/StirlingRefined.lean) | Non-asymptotic Stirling bounds & $O(q^{-3})$ central expansion | 399 lines · 0 `sorry` |
| [`lean/MultinomialTVConjecture/GaussianEulerMaclaurin.lean`](lean/MultinomialTVConjecture/GaussianEulerMaclaurin.lean) | Cubic odd-Gaussian Euler–Maclaurin theorem (`oddGauss_sum_approx`) | 608 lines · 0 `sorry` |
| [`lean/MultinomialTVConjecture/LocalAsymptotics.lean`](lean/MultinomialTVConjecture/LocalAsymptotics.lean) | Consecutive-ratio tails, local Taylor expansions, `tendsto_sumA/B/C` | 1,997 lines · 0 `sorry` |
| [`lean/MultinomialTVConjecture/Main.lean`](lean/MultinomialTVConjecture/Main.lean) | Fidelity check `hAdj_eq_nested_sum`, `conjecture_7_7`, `gamma_[cyclic_]closed_form` | 341 lines · 0 `sorry` |
| [`lean/VerifyAxioms.lean`](lean/VerifyAxioms.lean) | `#print axioms` audit across all 19 exported theorems | `[propext, Classical.choice, Quot.sound]` |
| [`paper/main.tex`](paper/main.tex) | Complete AMS-LaTeX manuscript + BibTeX ([`refs.bib`](paper/refs.bib)) | Compiles cleanly with Tectonic / pdfLaTeX |
| [`dist/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf`](dist/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf) | Typeset publication PDF | Ready to read / archive |
| [`dist/arxiv_submission.tar.gz`](dist/arxiv_submission.tar.gz) | Self-contained arXiv LaTeX + `.bbl` + vector PDF figures bundle | Verified standalone compile |
| [`scripts/verify_conjecture.py`](scripts/verify_conjecture.py) | Exact rational ($\ell=3\dots45$, $0/1$ error) & 80-digit Richardson audit | Matches closed forms to $< 3\times 10^{-55}$ |
| [`scripts/generate_figures.py`](scripts/generate_figures.py) | Reproducible publication vector figure generator | Produces `paper/figures/*.pdf` |

---

## Reproducing All Results Locally

### 1. Lean 4 Machine-Checked Verification (`v4.35.0`)
```bash
cd lean
lake exe cache get   # fetches prebuilt Mathlib oleans
lake build
lake env lean VerifyAxioms.lean
```
Expected axiom audit: all 19 theorems print strictly `[propext, Classical.choice, Quot.sound]`.

### 2. Independent Exact-Rational & 80-Digit Numerical Audit
```bash
pip install mpmath
python scripts/verify_conjecture.py
```

### 3. Rebuilding Figures and Manuscript PDF
```bash
uv run --with matplotlib --with mpmath --with numpy python scripts/generate_figures.py
cd paper && tectonic -X compile main.tex --outdir build
```

---

## Citation

If you build upon this proof or Lean 4 formalization, please cite [`CITATION.cff`](CITATION.cff) or use:

```bibtex
@misc{donahue2026conjecture77,
  author       = {Alexander Stephen Donahue},
  title        = {Resolution and Lean 4 Formal Verification of Conjecture 7.7 on the Second-Order Variance of Multinomial Discrete Total Variation},
  year         = {2026},
  month        = nov,
  howpublished = {0thernes LLC, GitHub Repository},
  url          = {https://github.com/0thernes/multinomial-tv-conjecture},
  note         = {ORCID: 0009-0006-8168-9648; Lean 4 v4.35.0 formal verification}
}
```

## Methodology & Licensing

- **Transparent methodology:** The proof discovery, Lean 4 formalization, verification scripts, and manuscript preparation were conducted by the author with interactive AI assistance. Mathematical correctness is established independently of authoring provenance by the Lean 4 kernel (`v4.35.0`) with zero `sorry` and strictly standard logical axioms.
- **License:** Dual-licensed under the **MIT License** (Lean 4 & Python code) and **CC BY 4.0** (manuscript, PDF, and figures); see [`LICENSE`](LICENSE).
- **Primary problem provenance:** Conjecture 7.7 is due to N. Banić and N. Elezović ([arXiv:2610.17046v1](https://arxiv.org/abs/2610.17046v1), [arXiv:2611.14735v1](https://arxiv.org/abs/2611.14735v1)). No third-party arXiv paper sources are redistributed in this repository.
