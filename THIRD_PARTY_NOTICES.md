# Third-Party Notices

This repository does not vendor third-party source code directly, but builds upon and verifies against the following open-source toolchains and libraries (fetched via pinned lockfiles):

| Component | License | Role | Upstream |
|---|---|---|---|
| **Lean 4** (`v4.35.0`) | Apache-2.0 | Theorem prover, C++ kernel, `lake`, `lake comparator`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron` | https://github.com/leanprover/lean4 |
| **Mathlib4** (`lean/lake-manifest.json` pinned rev) | Apache-2.0 | Mathematical library for Lean 4 | https://github.com/leanprover-community/mathlib4 |
| **Batteries** (`lean/lake-manifest.json` pinned rev) | Apache-2.0 | Core data structures and `runLinter` | https://github.com/leanprover-community/batteries |
| **Python 3** | PSF-2.0 | Independent verification scripts and test runner | https://www.python.org |
| **mpmath** (`requirements.txt`) | BSD-3-Clause | 80-digit arbitrary-precision numerical verification | https://github.com/mpmath/mpmath |
| **pytest** (`requirements.txt`) | MIT | Automated test framework | https://github.com/pytest-dev/pytest |
| **Hypothesis** (`requirements.txt`) | MPL-2.0 | Property-based testing | https://github.com/HypothesisWorks/hypothesis |
| **PyYAML** (`requirements.txt`) | MIT | `repo.yaml` / `formalization.yaml` / `CITATION.cff` validation | https://github.com/yaml/pyyaml |
| **jsonschema** (`requirements.txt`) | MIT | JSON Schema Draft 2020-12 validation of `repo.yaml` | https://github.com/python-jsonschema/jsonschema |
| **Ruff** (`requirements.txt`) | MIT | Static analysis linter (report-only) | https://github.com/astral-sh/ruff |
| **mypy** (`requirements.txt`) | MIT | Static type checker (report-only) | https://github.com/python/mypy |
| **Tectonic** | MIT | Reproducible LaTeX compilation engine | https://tectonic-typesetting.github.io |
| **MathJax** (CDN in Blueprint HTML) | Apache-2.0 | Client-side mathematical rendering in static Blueprint page | https://www.mathjax.org |

The original conjecture proved in this repository is Conjecture 7.7 of Nikola Banić and Neven Elezović, *Discrete total variation under the multinomial, Part 2: variance under the uniform null* (arXiv:2610.17046v1, 2026), with cyclic application in Part 5 (arXiv:2611.14735v1, 2026). No text or code from those preprints is copied here.
