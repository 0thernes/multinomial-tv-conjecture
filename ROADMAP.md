# Roadmap

## Completed (v2.0.0)
- Complete machine-checked Lean 4.35.0 proof of Conjecture 7.7 (`b_0`, `b_1`, `b_2`, `d_0`, `a_△`, `γ_2`) and unconditional closed forms for `γ(n)` and `γ_c(n)` (`n ≥ 5`).
- Non-vacuity and adversarial false-constant refutation witnesses (`MultinomialTVConjecture/NonVacuity.lean`).
- Isolated Mathlib-only `Challenge.lean` / `Solution.lean` specification and 6-kernel `lake comparator --paranoid` verification.
- Lean 4 interactive SVG Dependency Blueprint and GitHub Pages site.
- Full Build Standard v1.2.0 and Independent Research Verification Playbook v1.3 compliance.

## Planned
- Independent human line-by-line statement-fidelity sign-off recorded in `docs/statement-fidelity.md` and `formalization.yaml`.
- Submission of the manuscript and frozen artifacts to Zenodo (for persistent versioned DOI) and arXiv (`math.ST` / `math.CO`) upon endorsement, plus Palomar Registry submission once `module` system support stabilizes across Mathlib4.
- Optional upstreaming of reusable refined-Stirling (`StirlingRefined.lean`) and Gaussian Euler–Maclaurin (`GaussianEulerMaclaurin.lean`) lemmas toward Mathlib4.

## Not Planned
- Formalizing the entirety of Banić & Elezović Part 1 (`arXiv:2610.13366`), Part 2 Theorems 1–7.6 (`arXiv:2610.17046v1`), or Part 5 Theorem 5.2 (`arXiv:2611.14735v1`) inside this repository; those upstream results remain explicitly cited external theorems outside our Lean kernel boundary (see `LIMITATIONS.md`).
- Adding a web backend, database, or runtime AI inference service.
- Changing the solo-maintainer direct-to-`main` workflow (`R1`–`R4`).
