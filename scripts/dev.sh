#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 Alexander S. Donahue
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

cmd="${1:-help}"
shift || true

case "$cmd" in
  setup)
    python3 -m pip install -r requirements.txt
    (cd lean && lake exe cache get)
    ;;
  build)
    (cd lean && lake build MultinomialTVConjecture Challenge Solution VerifyAxioms)
    ;;
  test)
    python3 -m pytest -v tests/
    ;;
  lint)
    (cd lean && lake exe runLinter MultinomialTVConjecture) || true
    ;;
  verify-lean)
    python3 scripts/check_lean_tokens.py
    (cd lean && lake build MultinomialTVConjecture Challenge Solution VerifyAxioms)
    (cd lean && lake env lean VerifyAxioms.lean) | tee results/lean-axioms-ci.log
    python3 scripts/check_readme_axioms.py --log results/lean-axioms-ci.log --require-exhaustive
    (
      cd lean
      # Note: the actual kernel-checked refutation of aTriangle = 1/32 is the proved theorem
      # `MultinomialTV.NonVacuity.adversarial_aTriangle_ne_one_div_32`; this step is an
      # elaboration smoke test verifying that a mutated goal leaves unsolved goals.
      tmp_neg="$(mktemp /tmp/neg_smoke_test.XXXXXX.lean)"
      printf 'import MultinomialTVConjecture.Main\ntheorem mutated_aTriangle_must_fail : MultinomialTV.aTriangle = 1 / 32 := by\n  rw [MultinomialTV.conjecture_7_7_aTriangle]\n  norm_num\n' > "$tmp_neg"
      OUT="$(lake env lean "$tmp_neg" 2>&1 || true)"
      rm -f "$tmp_neg"
      if ! printf '%s\n' "$OUT" | grep -q "unsolved goals"; then
        echo "ERROR: Expected 'unsolved goals' on mutated constant smoke test!" >&2
        exit 1
      fi
      echo "PASS: Elaboration smoke test failed with expected 'unsolved goals' on mutated constant."
    )
    (cd lean && lake env leanchecker MultinomialTVConjecture.NonVacuity)
    (cd lean && lake comparator --config comparator.json --paranoid) | tee results/comparator-paranoid-ci.log
    ;;
  verify-numeric)
    python3 scripts/verify_conjecture.py
    ;;
  blueprint)
    python3 scripts/build_blueprint.py
    ;;
  site)
    python3 scripts/build_blueprint.py
    python3 scripts/build_site.py
    ;;
  paper)
    (cd paper && tectonic -X compile main.tex --outdir build --keep-intermediates)
    cp paper/build/main.pdf dist/Donahue_2026_Conjecture_7_7_Multinomial_TV.pdf
    python3 scripts/build_arxiv_bundle.py
    ;;
  reproduce)
    python3 scripts/verify_conjecture.py
    python3 -m pytest -v tests/
    python3 scripts/check_citations.py
    python3 scripts/check_readme_axioms.py --require-exhaustive
    python3 scripts/build_blueprint.py
    python3 scripts/build_site.py
    python3 scripts/generate_manifest.py --verify
    python3 scripts/stamp_timestamps.py --verify
    bash scripts/audit-repo.sh .
    ;;
  release)
    ver="${1:?Usage: dev.sh release X.Y.Z}"
    cur="$(tr -d '\r\n' < VERSION)"
    if [ "$cur" != "$ver" ]; then
      echo "ERROR: VERSION ($cur) != requested release ($ver). Sync VERSION, CITATION.cff, formalization.yaml, lean/lakefile.toml, CHANGELOG.md, paper/main.tex, and MANIFEST.sha256 first." >&2
      exit 1
    fi
    python3 scripts/check_lean_tokens.py
    python3 -m pytest -q tests/
    python3 scripts/generate_manifest.py --verify
    python3 scripts/stamp_timestamps.py --verify
    git add -A
    git -c commit.gpgsign=false commit -m "chore: release v${ver}"
    git -c tag.gpgsign=false tag "v${ver}"
    git push origin main --tags
    ;;
  *)
    echo "Usage: scripts/dev.sh {setup|build|test|lint|verify-lean|verify-numeric|blueprint|site|paper|reproduce|release}"
    exit 1
    ;;
esac
