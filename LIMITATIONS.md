# Limitations, Verification Boundaries & Real-vs-Metaphor (`LIMITATIONS.md`)

This document states explicitly what our Lean 4 formalization and numerical verification **do** establish, what they **do not** establish, and where literal mathematical claims stop.

## 1. Formal Verification Boundary (What Lean Checks vs. What Lies Outside)

| Layer | Inside Lean 4 (6-Kernel Checked) | Outside Lean 4 (Cited / Scripted / Human-Audited) |
|---|---|---|
| **Combinatorial definition & reduction** | `hAdj L` equals exact nested multinomial sum (`hAdj_eq_nested_sum`); exact 1D identities for `L = 3q, 3q+1, 3q+2`. | Equivalence between the discrete sum and probabilistic measure-space notation `E[|X_2 - X_1||X_3 - X_2|]` is standard finite-support probability (audited in [docs/statement-fidelity.md](docs/statement-fidelity.md)). |
| **Conjecture 7.7 (`b_0, b_1, b_2, d_0, a_△, γ_2`)** | **100% kernel-checked** from Mathlib primitives via 6 independent kernels (`Lean 4.35.0`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`). | Independent human line-by-line fidelity review of `Challenge.lean` against `arXiv:2610.17046v1` is **OPEN** (`human_line_by_line_review_recorded: false` in `formalization.yaml`). |
| **Linear & cyclic variance formulas `γ(n)`, `γ_c(n)`** | Exact algebraic simplification substituting `aTriangle` into `p_1(n), q_1(n), r_1(n)` (`gamma_closed_form`, `gamma_cyclic_closed_form`). | Upstream Theorem 7.6 of Banić & Elezović Part 2 (`arXiv:2610.17046v1`) and Theorem 5.2 of Part 5 (`arXiv:2611.14735v1`) linking `γ(n), γ_c(n)` to `p_1, q_1, r_1` are **cited external results, NOT proved in Lean**. |
| **Numerical verification (`scripts/verify_conjecture.py`)** | Exact rational `hAdj 0..5` proved in `NonVacuity.lean`. | Exact rational checks for $L=3..45$ (43 values) and 80-digit `mpmath` checks up to $q=3{,}000$ ($L=9{,}001$; 28-point Neville–Richardson error $< 3\times 10^{-55}$) run in Python (`fractions` + `mpmath`), outside the Lean kernel. |
| **Manuscript & prose (`paper/main.tex`)** | Theorem statements correspond 1-to-1 to Lean declarations (`docs/statement-fidelity.md`, `blueprint/src/content.tex`). | LaTeX typesetting, historical context, and prose exposition are human/AI-authored and NOT checked by a proof assistant. |

## 2. Specific Technical & Process Limitations

1. **No external peer review yet:** The manuscript is an independent research preprint. It has NOT yet undergone journal peer review, arXiv moderation, or Palomar Registry acceptance.
2. **Human line-by-line fidelity audit is open:** Although `Challenge.lean` is only ~105 lines of Mathlib-only Lean 4 and `NonVacuity.lean` proves 18 concrete small-$L$ and adversarial checks, no independent third-party mathematician has yet signed off line-by-line on `docs/statement-fidelity.md`.
3. **Lean 4.35.0 `module` system warning:** Mathlib v4.35.0 emits non-fatal informational warnings encouraging the new Lean 4.35 `module` header. Our files compile cleanly without `module` under both `lake build` and 6-kernel `lake comparator --paranoid`; migrating to `module` syntax is tracked in `ROADMAP.md`.
4. **Windows vs. Linux sandbox for `lake comparator`:** On Linux (`ubuntu-24.04` CI), `lake comparator --config comparator.json --paranoid` executes inside a `bubblewrap` kernel namespace sandbox. On Windows (where `bubblewrap` does not exist), local execution requires `--inadvisably-no-sandbox` (all 6 independent proof checkers still verify the full exported proof terms identically).
5. **AI-assisted provenance:** Mathematical exploration, Lean 4 proof engineering, Python test scaffolding, and LaTeX drafting were conducted with AI assistance under Alexander S. Donahue's direction (see `formalization.yaml` and Section "AI Assistance and CRediT Disclosure" in `paper/main.tex`). Epistemic warrant rests strictly on the reproducible 6-kernel verification and independent exact calculations, never on author or model authority.

## 3. Real vs. Metaphor

- Every mathematical term in this repository (`multinomial distribution`, `discrete total variation`, `Euler–Maclaurin summation`, `Stirling expansion`, `asymptotic variance`, `residue class`) is used strictly in its **literal, standard mathematical definition**—there are no physical, biological, or heuristic metaphors.
- The colloquial phrase **"5-second proof verification"** in `README.md` means inspecting the committed verbatim `#print axioms` block and re-running `lake env lean VerifyAxioms.lean` against pre-built `.olean` caches; a cold build without Mathlib's `lake exe cache get` takes substantially longer (~2–5 minutes with cache, >30 minutes compiling Mathlib from source).
- **"Six-kernel verified"** refers literally to executing the six independent type-checkers bundled with Lean 4.35.0 (`Lean 4.35.0` C++ kernel, `leanchecker-paranoid`, `lean4lean`, `nanoda 0.4.19`, `con-leche`, `con-ron`) over `Challenge.lean` and `Solution.lean`; it does **not** eliminate the need to inspect `Challenge.lean` itself for statement fidelity against Banić & Elezović (2026).
