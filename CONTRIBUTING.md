# Contributing

Independent audits, statement-fidelity reviews, clean-room replications, bug reports, and Lean proof simplifications are warmly welcomed.

## How to Report a Finding

Open an issue using one of the structured forms in `.github/ISSUE_TEMPLATE/`, classifying every finding into **exactly one** of the ten Build Standard classes (`bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot` — see [docs/glossary.md](docs/glossary.md)).

## Submitting Improvements or Replications

1. Read [AGENTS.md](AGENTS.md), [CLAIMS.md](CLAIMS.md), [LIMITATIONS.md](LIMITATIONS.md), and [REPLICATION.md](REPLICATION.md).
2. Run the full verification suite locally:
   ```bash
   just reproduce
   ```
3. For Lean edits, verify zero forbidden tokens (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`), pass `lake env lean VerifyAxioms.lean`, and pass `lake comparator --config comparator.json --paranoid`.
4. To log an independent human statement-fidelity audit or clean-room replication, open an issue with the `replication` label containing your Lean version, OS, SHA-256 checksums, and command log.

## Maintainer Workflow Note

This repository follows Build Standard v1.2.0 solo-maintainer rules (`R1`–`R4`): the maintainer commits directly to `main`, CI is informational, and there is no pull request template. External contributors may still fork and open issues or discussions; all accepted code contributions are licensed under Apache-2.0 (`LICENSE`) and documentation under CC-BY-4.0 (`LICENSE-DOCS`).
