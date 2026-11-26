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
    (cd lean && lake build MultinomialTVConjecture Challenge Solution VerifyAxioms)
    (cd lean && lake env lean VerifyAxioms.lean) | tee results/lean-axioms-ci.log
    python3 scripts/check_readme_axioms.py --log results/lean-axioms-ci.log --require-exhaustive
    (
      cd lean
      tmp_neg="$(mktemp /tmp/neg_false_conjecture.XXXXXX.lean)"
      printf 'import MultinomialTVConjecture.Main\ntheorem false_conj : MultinomialTV.aTriangle = 1 / 32 := by exact MultinomialTV.conjecture_7_7_aTriangle\n' > "$tmp_neg"
      if lake env lean "$tmp_neg" >/dev/null 2>&1; then
        rm -f "$tmp_neg"
        echo "ERROR: Lean kernel unexpectedly accepted false conjecture!" >&2
        exit 1
      fi
      rm -f "$tmp_neg"
      echo "PASS: Lean kernel rejected false statement aTriangle = 1/32."
    )
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
    echo "$ver" > VERSION
    git add -A
    git commit -m "chore: release v${ver}"
    git tag "v${ver}"
    git push origin main --tags
    ;;
  *)
    echo "Usage: scripts/dev.sh {setup|build|test|lint|verify-lean|verify-numeric|blueprint|site|paper|reproduce|release}"
    exit 1
    ;;
esac
