# ADR 0002: Apache-2.0 / CC-BY-4.0 Dual Licensing and Comparator Challenge/Solution Isolation

- **Status:** Accepted
- **Date:** 2026-11-25

## Context

`v1.0.0` shipped a combined MIT/CC-BY-4.0 `LICENSE` file and verified axioms only via a single-kernel `lake env lean VerifyAxioms.lean` command checked with `grep -v` in CI. Hardening to Build Standard v1.2.0 and Independent Research Verification Playbook v1.3 identified two structural weaknesses:
1. MIT lacks an explicit patent grant and diverges from Mathlib4's Apache-2.0 license, complicating potential upstreaming of `StirlingRefined.lean` and `GaussianEulerMaclaurin.lean`.
2. Relying solely on one kernel and a single `grep` leaves formal-verification trust vulnerable to kernel bugs, definition drift, or log-wrapping parsing bugs.

## Decision

1. Split licensing cleanly into **`LICENSE` (Apache-2.0)** for code/Lean/scripts/tests and **`LICENSE-DOCS` (CC-BY-4.0)** for manuscript/docs/blueprint, accompanied by `NOTICE` and `THIRD_PARTY_NOTICES.md`.
2. Add Palomar-compatible isolation: a 108-line Mathlib-only `lean/Challenge.lean`, a sorry-free `lean/Solution.lean`, `lean/comparator.json`, `formalization.yaml`, `lean/MultinomialTVConjecture/NonVacuity.lean` (18 concrete/adversarial witnesses), and exhaustive `Lean.collectAxioms` verification with the comparator targets replayed in six checker runs of `lake comparator --config comparator.json --paranoid`.

## Consequences

- **Positive:** Auditors can verify statement fidelity by reading the 153 lines of `Challenge.lean` (9 targets as of `v2.5.0`, evolved from the initial 108-line / 6-target stub) and replay it in six checker runs (the Lean kernel in paranoid and default mode, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
- **Positive:** Code is 100% license-compatible with Mathlib4 and JOSS; papers remain freely reusable under CC-BY-4.0.
- **Trade-off:** `Challenge.lean` contains intentional `sorry` stubs (initially 6, expanded to 9 as of `v2.4.0`/`v2.5.0`), so the CI forbidden-token lexer explicitly excludes `Challenge.lean` while strictly policing every proof module and `Solution.lean`.
