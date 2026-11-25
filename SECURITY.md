# Security Policy

## Scope

This repository contains Lean 4 formal proofs, Python exact/high-precision verification scripts, a LaTeX manuscript, and static documentation. It runs no network services, collects no personal data, and uses no runtime credentials.

Security-relevant issues still include:
- Supply-chain compromises in pinned dependencies (`lean/lake-manifest.json`, `requirements.txt`, GitHub Actions workflows).
- Formal verification soundness bypasses (`sorry`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, `@[extern]`, or definition-drift mismatches between `Challenge.lean` and `Solution.lean`).
- Secret leakage or build-script command/path injection.

## Reporting a Vulnerability

Please report security issues privately using GitHub Security Advisories:
https://github.com/0thernes/multinomial-tv-conjecture/security/advisories/new

Alternatively, email `0_0@0thernes.art` with `[SECURITY] multinomial-tv-conjecture` in the subject line.

We aim to acknowledge reports within 72 hours and publish a fix or honest erratum as soon as verified.
