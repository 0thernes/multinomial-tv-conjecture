# Roadmap

## Completed (v2.0.0 – v2.3.0)
- Complete machine-checked Lean 4.35.0 proof of Conjecture 7.7 (`b_0`, `b_1`, `b_2`, `d_0`, `a_△`, `γ_2`) and unconditional closed forms for `γ(n)`, `γ_c(n)` (`n ≥ 5`), `γ(3; N)`, and `γ(4; N)` (Corollary 1.2(i)–(iii)).
- Full Lean 4.35.0 `module`-header migration across all 10 `.lean` files with `weak.linter.mathlibStandardSet = true` enabled (Palomar Registry compliant, 0 compiler, Batteries, or Mathlib style-linter warnings) and REUSE/SPDX headers across all source and manuscript files.
- Non-vacuity and adversarial false-constant refutation witnesses (`MultinomialTVConjecture/NonVacuity.lean`, 20 theorems), exhaustive 730-theorem `Lean.collectAxioms` audit, and live negative Lean kernel rejection in CI.
- Isolated Mathlib-only `Challenge.lean` (143 lines, 8 targets) / `Solution.lean` specification and sandboxed 6-kernel `lake comparator --paranoid` verification.
- Accessible interactive Lean 4 SVG Dependency Blueprint and strict-CSP/SRI GitHub Pages site (`A05` & `A38` done).
- Dual cryptographic timestamping (DigiCert RFC 3161 TSA `.tsr` + multi-calendar Bitcoin OpenTimestamps `.ots`), Sigstore SLSA attestations, live Crossref retraction checks, SHA-256-verified `osv-scanner v2.7.1`, and full Build Standard v1.2.0 (`100.0%`, `66/66`) + Independent Research Verification Playbook v1.3 compliance.

## Planned
- Independent human line-by-line statement-fidelity sign-off recorded in `docs/statement-fidelity.md` and `formalization.yaml`.
- Submission of the frozen `v2.3.0` commit and artifacts to Palomar Registry (`submit.palomar-registry.org`), Zenodo / OSF Preprints (for persistent DOI), Software Heritage (SWHID), and arXiv (`math.ST` / `math.CO`) upon endorsement.
- Optional upstreaming of reusable refined-Stirling (`StirlingRefined.lean`) and Gaussian Euler–Maclaurin (`GaussianEulerMaclaurin.lean`) lemmas toward Mathlib4.

## Not Planned
- Formalizing the entirety of Banić & Elezović Part 1 (`arXiv:2610.13366`), Part 2 Theorems 1–7.6 (`arXiv:2610.17046v1`), or Part 5 Theorem 5.2 (`arXiv:2611.14735v1`) inside this repository; those upstream results remain explicitly cited external theorems outside our Lean kernel boundary (see `LIMITATIONS.md`).
- Adding a web backend, database, or runtime AI inference service.
- Changing the solo-maintainer direct-to-`main` workflow (`R1`–`R4`).
