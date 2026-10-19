# Archive preservation check

Date: 2026-10-12.

- SHA-256 checks matched for all **58** inventoried existing files: 34 campaign archive files and 24 nearby original/scratch/build artifacts.
- A recursive rescan including hidden files found the same **34** files in `fbm`, `ibm` and `spde`; no additions, deletions or path changes occurred there.
- Both requested folders exist. The additional relevant manuscript folder is `C:/Operator/spde`.
- Active repository HEAD remained `61548d19f1f0020b35942783b8056b8b4b826fe4`.
- Final read-only `git status --porcelain=v1` matched the initial state: no tracked changes and the same 12 pre-existing untracked audit/plan documents listed below.
- `git diff --exit-code HEAD -- lean-toolchain lake-manifest.json lakefile.toml lakefile.lean` exited 0.
- Lean pin remains `leanprover/lean4:v4.34.1`; Mathlib remains `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Only new research documentation under `C:/Operator/ResearchAudits` was created. No archive file was edited, moved, renamed or deleted. No Lake build, Lean source edit, commit or push was performed.

The archive hash baseline was taken before creating these research documents. The repository status check detects tracked content changes and untracked path changes; it is not a byte hash of the entire repository. No write operation in this inventory targeted the repository.

## Pre-existing untracked repository files

- BAKRY_EMERY_REPLACEMENT_PLAN.md
- INDEPENDENT_BANACH_RECONSTRUCTION_AUDIT.md
- INDEPENDENT_FULL_GAUSSIAN_LSI_AUDIT.md
- INDEPENDENT_GAUSSIAN_LSI_AUDIT.md
- INDEPENDENT_GRAPH_CORE_AUDIT.md
- INDEPENDENT_POISSON_AUDIT.md
- M3_ENTROPY_DISSIPATION_STRATEGY.md
- OPERATOR_DERIVATIVE_NON_GAUSSIAN_RESEARCH_AUDIT.md
- PAPER1_BLOCKING_OBLIGATIONS.md
- PAPER1_COMPLETION_PLAN.md
- PAPER1_LEAN_CROSSWALK.md
- PAPER1_THEOREM_INVENTORY.md

All manuscript claims remain UNVERIFIED. This preservation check is not a mathematical or Lean axiom audit.
