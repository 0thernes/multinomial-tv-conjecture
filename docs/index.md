# Documentation Index

Welcome to the documentation for **Multinomial TV Conjecture (`v2.3.0`)** — the Lean 4.35.0 (`module`-header Palomar spec) proof of Conjecture 7.7 of Banić & Elezović (`arXiv:2610.17046v1`, 2026; an arXiv preprint, not peer reviewed), replayed in CI by `lake comparator --paranoid` (six checker runs).

## Verification & Epistemology
- [Statement-Fidelity Audit Table](statement-fidelity.md) — Maps every Lean 4 theorem to Banić & Elezović's literal definitions and highlights what lies inside vs. outside the Lean kernel.
- [Verification Architecture](verification.md) — Details the `lake comparator --paranoid` replay (six checker runs), exhaustive `Lean.collectAxioms` metaprogram, non-vacuity checks, and Python test ladder.
- [Literature & Novelty Search Log](literature-search.md) — Dated novelty search across arXiv, Crossref, OEIS, classical probability literature, and the 1,900-problem Unsolved Problems Mega-Atlas.
- [Red-Team & Hardening Review (2026-11-25)](reviews/red-team-2026-11-25.md) — Complete multi-cycle, 10-class defect log (`F-01`–`F-44`) and Playbook v1.3 10-pass review scorecard.
- [Run & Audit Log](run-log.md) — Timestamped execution record of local and CI verification runs.

## Engineering & Architecture
- [Architecture](architecture.md) — Proof dependency DAG from `Combinatorial.lean` through `Main.lean`, `NonVacuity.lean`, and `Challenge`/`Solution`.
- [Configuration & Toolchains](configuration.md) — Pinned Lean 4.35.0, Mathlib4, Python, and Tectonic environments across Linux, macOS, and Windows.
- [Operations, Backups & Offsite Mirror](operations.md) — Git bundle backups, offsite mirroring, Software Heritage archival, and release checksum workflow.
- [Threat Model](threat-model.md) — Formal-proof soundness threats, supply-chain risks, and mitigations.
- [Build Standard Reference](build-standard.md) — Local reference copy of Build Standard for LLMs v1.2.0.

## Decisions & Reference
- [ADR 0001: Exact 2D-to-1D Combinatorial Reduction](adr/0001-combinatorial-2d-to-1d-reduction.md)
- [ADR 0002: Apache-2.0 / CC-BY-4.0 Dual Licensing & Comparator Isolation](adr/0002-dual-licensing-and-six-kernel-verification.md)
- [FAQ](faq.md)
- [Glossary](glossary.md)
