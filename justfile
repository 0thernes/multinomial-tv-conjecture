# Task runner for multinomial-tv-conjecture (Build Standard v1.2.0, item A31)
set shell := ["bash", "-euo", "pipefail", "-c"]

# List available recipes
default:
    @just --list

# Install pinned Python dependencies and fetch pinned Mathlib cache
setup:
    bash scripts/dev.sh setup

# Build Lean 4.35.0 proof library, isolated Challenge/Solution, and VerifyAxioms
build:
    bash scripts/dev.sh build

# Run full pytest ladder (exact, property, negative, regression, golden, differential, metamorphic, mutation, integrity)
test:
    bash scripts/dev.sh test

# Report-only linters & type checks (ruff, mypy, Lean Batteries runLinter)
lint:
    python3 -m ruff check scripts/ tests/ || true
    python3 -m mypy --ignore-missing-imports scripts/ || true
    bash scripts/dev.sh lint

# Build Lean libraries, scan forbidden tokens, run VerifyAxioms, sync README, and run 6-kernel lake comparator --paranoid
verify-lean:
    bash scripts/dev.sh verify-lean

# Run independent exact rational & 80-digit numerical verification of Conjecture 7.7
verify-numeric:
    bash scripts/dev.sh verify-numeric

# Validate all \lean{...} declarations in blueprint/src/content.tex and build interactive SVG Blueprint
blueprint:
    bash scripts/dev.sh blueprint

# Assemble and link-check the static GitHub Pages site (portal + Blueprint + paper PDF)
site:
    bash scripts/dev.sh site

# Compile AMS-LaTeX manuscript via Tectonic and build byte-reproducible arXiv tarball
paper:
    bash scripts/dev.sh paper

# Clean-clone end-to-end reproduction of numeric verifier, tests, citations, axioms, blueprint, and site
reproduce:
    bash scripts/dev.sh reproduce

# Score repository against Build Standard for LLMs v1.2.0 (90 items)
audit:
    bash scripts/audit-repo.sh .

# Tag and push a semantic version release straight to main
release version:
    bash scripts/dev.sh release "{{version}}"
