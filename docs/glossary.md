# Glossary (`docs/glossary.md`)

## Mathematical Terms

- **Discrete Total Variation ($D_n$):** For a multinomial count vector $(X_1, \dots, X_n) \sim \mathrm{Mult}(N; 1/n, \dots, 1/n)$, the sum of adjacent absolute differences $D_n = \sum_{i=1}^{n-1} |X_{i+1} - X_i|$ (or cyclic $D_n^{(c)} = D_n + |X_1 - X_n|$).
- **Adjacent Pair Expectation ($h_{\mathrm{adj}}(L)$):** The exact expectation $\mathbb{E}[|X_2 - X_1|\,|X_3 - X_2|]$ for $(X_1, X_2, X_3) \sim \mathrm{Mult}(L; \frac13, \frac13, \frac13)$.
- **Residue Constants ($b_0, b_1, b_2$):** The mod-3 sub-sequence limits $b_r = \lim_{q\to\infty} (3q+r)(h_{\mathrm{adj}}(3q+r) - c_L(3q+r) - a_*)$ for $r \in \{0,1,2\}$.
- **Mean Residue Constant ($d_0$):** The average $d_0 = \frac{1}{3}(b_0 + b_1 + b_2) = -\frac{4\sqrt{3}}{81\pi}$.
- **Adjacent Triangular-Lattice Constant ($a_\triangle$):** $a_\triangle = \frac{1}{32} + \frac{\pi}{9}(b_0 + b_1 + b_2) = \frac{1}{32} - \frac{4\sqrt{3}}{243}$.
- **Second-Order Variance Coefficients ($\gamma(n), \gamma_c(n), \gamma_2$):** The $O(N^{-2})$ coefficients in the large-$N$ asymptotic expansions of the normalized variances $\mathrm{Var}(d)/N$ and $\mathrm{Var}(d^c)/N$ (equivalently the $O(N^{-1})$ coefficients of $\mathrm{Var}(d)$ and $\mathrm{Var}(d^c)$, one order beyond the $O(1)$ constant $-\beta(n)$), with quadratic leading coefficient $\gamma_2 = \frac{64 a_\triangle - 3}{32\pi} = -\frac{1}{32\pi} - \frac{8\sqrt{3}}{243\pi}$.

## Formal Verification Terms

- **Six-Kernel Verification (`lake comparator --paranoid`):** Checking a single proof export independently across six distinct type checkers (`Lean 4.35.0`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
- **Palomar Isolation (`Challenge.lean` / `Solution.lean`):** Separating minimal Mathlib-only target specifications from proof internals so auditors only inspect the concise `Challenge.lean` statement file (under Palomar's 1,000-line / 100 KiB limit).
- **Statement Fidelity:** Exact mathematical correspondence between an informal literature statement and its formal Lean 4 type.
- **Non-Vacuity Witness:** A formal theorem proving that hypotheses are concretely inhabited and that definitions evaluate to known exact values and refute deliberately false variants.
- **Standard Lean Axioms:** `[propext, Classical.choice, Quot.sound]` — the three foundational axioms of classical mathematics in Lean 4 / Mathlib4.

## Ten Finding Classes (Build Standard v1.2.0 Rule `R7`)

| Class | Meaning |
|---|---|
| `bug` | Code does something different from its spec or intent (a defect in program logic). |
| `error` | Wrong number, claim, doc, config, version, build, or command. |
| `issue` | Works and is not wrong, but is unclear, inconsistent, fragile, or hard to maintain. |
| `problem` | External obstacle (network, account, toolchain, legal-entity status) blocks progress or validity. |
| `concern` | Risk that has not caused harm yet (security, cost, legal, reliability). |
| `dilemma` | Trade-off between valid options; the owner decides. |
| `conflict` | Two requirements or rules contradict each other. |
| `gap` | Something required or expected is missing; nothing present is wrong. |
| `hole` | Missing check or safeguard, so a defect could pass unnoticed. |
| `blindspot` | A user, platform, failure mode, or assumption nobody has examined yet. |
