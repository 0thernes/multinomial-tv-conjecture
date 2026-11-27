# Roadmap

## Completed (v2.0.0 – v2.5.0)
- Complete machine-checked Lean 4.35.0 proof of Conjecture 7.7 (`b_0`, `b_1`, `b_2`, `d_0`, `a_△`, `γ_2`) and the quantitative $O(L^{-2})$ remainder of Lemma 7.3 (`lemma_7_3_O_inv_sq`), plus the four algebraic identities behind `γ(n)`, `γ_c(n)` (`n ≥ 5`, cited via Part 2 Thm 7.6 and Part 5 Thm 3.10), `γ(3; N)`, and `γ(4; N)` (Corollary 1.2(i)–(iii)).
- Full Lean 4.35.0 `module`-header migration across all 10 `.lean` files with `weak.linter.mathlibStandardSet = true` enabled (Palomar Registry compliant, no compiler or style-linter warnings except the 9 intentional `sorry` warnings of statement-only `Challenge.lean`) and REUSE/SPDX headers across all source and manuscript files.
- Non-vacuity and adversarial false-constant refutation witnesses (`MultinomialTVConjecture/NonVacuity.lean`: 20 theorems — 6 direct `hAdj 0..5` definition checks and 14 sign/witness/refutation corollaries including `adversarial_aTriangle_ne_one_div_32`), exhaustive `Lean.collectAxioms` audit across 892 theorem constants (187 author-written theorems and lemmas + 705 compiler-generated auxiliaries), and isolated AST source-code mutation audit (`20/20` mutants killed).
- Isolated Mathlib-only `Challenge.lean` (153 lines, 9 targets) / `Solution.lean` specification replayed in CI by `lake comparator --paranoid` (six checker runs: Lean paranoid and default kernel, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
- Accessible interactive Lean 4 SVG Dependency Blueprint and strict-CSP/SRI GitHub Pages site (`A05` & `A38` done).
- Dual cryptographic timestamping (DigiCert RFC 3161 TSA `.tsr` + multi-calendar Bitcoin OpenTimestamps `.ots`), Sigstore SLSA attestations, live Crossref retraction checks, SHA-256-verified `osv-scanner v2.7.1`, and Build Standard v1.2.0 + Independent Research Verification Playbook v1.3 compliance (`B44` honestly `partial` pending external human operator replication).

## Planned
- Independent human line-by-line statement-fidelity sign-off recorded in `docs/statement-fidelity.md` and `formalization.yaml`, plus an independent external clean-room replication logged in `REPLICATION.md` (to promote `B44` from `partial` to `done`).
- Submission of the frozen `v2.5.0` commit and artifacts to Palomar Registry (`submit.palomar-registry.org`), Zenodo / OSF Preprints (for persistent DOI), Software Heritage (SWHID), and arXiv (`math.ST` / `math.CO`) upon endorsement.
- Optional upstreaming of reusable refined-Stirling (`StirlingRefined.lean`) and Gaussian Euler–Maclaurin (`GaussianEulerMaclaurin.lean`) lemmas toward Mathlib4.

## Not Planned
- Formalizing the entirety of Banić & Elezović Part 1 (`arXiv:2610.13366`), Part 2 Theorems 1–7.6 (`arXiv:2610.17046v1`), or Part 5 Theorem 3.10 (`arXiv:2611.14735v1`) inside this repository; those upstream results remain explicitly cited external theorems outside our Lean kernel boundary (see `LIMITATIONS.md`).
- Adding a web backend, database, or runtime AI inference service.
- Changing the solo-maintainer direct-to-`main` workflow (`R1`–`R4`).
