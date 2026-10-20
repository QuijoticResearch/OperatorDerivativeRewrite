# Stardust verification pipeline: measured Windows workflow

Permanent operating configuration, mandatory future-session consultation, rebenchmark triggers and rollback are recorded in `STARDUST_BUILD_OPTIMIZATION.md`. This file retains the detailed October 20 benchmark report.

Measured October 20, 2026 at mathematical commit `c2c2e36b30c538454ade7f2bb5e903a5881330df`, using native Windows Lean 4.34.1/Lake 5.0.0 and the unchanged Mathlib manifest (`d13f23b723b8a846827a245b89c10fc7d3f11612`). The registry identifies an Intel Core Ultra 9 285K; Windows reports 24 logical processors and 63.4 GiB usable physical RAM. These are warm-workspace wall-clock measurements, not cold-build or general hardware-performance claims. No research source was edited for benchmarking.

## Adopted improvement: preliminary type review

Use `tools/stardust_type_review.py` for intermediate review of declarations in a small selection of Foundation modules. It first builds those modules with Lake, then imports those modules to print explicit `#check @...` types. It records commands, elapsed times, exit codes and source/configuration hashes, rejects changing inputs, serializes helper invocations with a lock, and never overwrites existing results.

For example, from the repository root with the installed Python:

```powershell
python tools/stardust_type_review.py --run-dir .lake/my-fresh-type-review `
  --module Foundation.FractionalEndpointLaplace `
  --declaration OperatorDerivativeRewrite.Foundation.FractionalEndpointLaplace.scaled_sine_limit
```

Repeat `--module` and `--declaration` as needed. Read `types.log` in full. Run at a natural proof break, without another Lake build in progress. The lock coordinates this helper, not arbitrary external Lake commands. If a process is killed, check that no helper/build remains before removing its single stale `.lake/stardust-verification.lock` file.

This is **preliminary feedback only**, explicitly `checkpoint_eligible: false`. It cannot replace the final complete root build, complete transitive axiom audit, review of every new public type and complete proof/definition, independent mathematical checks, manuscript integrity, ledgers, audited commit, exact receipt or private sync. Keep final `#check @...` declarations in the complete root audit. No automatic audit approval or commit is performed.

Two matched pairs printed the same 15 declaration types, byte for byte:

| Preliminary review | Run 1 | Run 2 | Mean |
|---|---:|---:|---:|
| Existing root-import type file | 33.989 s | 32.824 s | 33.406 s |
| Selected-module helper, including its Lake build | 25.605 s | 25.711 s | 25.658 s |

The measured reduction is **23.2%**, or 7.75 seconds per review in this case. The selected leaf has no other Foundation dependencies; the root reaches 1,921 Foundation modules. Savings depend on the selected modules' import closure. This is not a 23% full-build or full-checkpoint speedup.

## Other measurements and decisions

| Operation with existing cached artifacts | Wall time |
|---|---:|
| Targeted Lake build, two runs | 6.109 / 6.246 s |
| Incremental full root build, two runs | 9.685 / 9.594 s |
| Complete root axiom audit plus 15 types, initial run | 39.034 s |
| Separate root-import type review, initial run | 33.070 s |
| Re-elaboration of the actual 200-line module through `lake env lean` | 24.653 s |

Direct Lean invocations used a freshly obtained Lake environment. Thread tests did not justify a global override:

| Lean process threads | Module re-elaboration | Root type review | Root audit plus types |
|---|---:|---:|---:|
| 1 | 18.901 s | 29.089 s | 33.307 s |
| 4 | 19.993 s | 29.689 s | not measured |
| 8 | 17.733 s | 32.939 s | 34.410 s |
| 24 | 19.076 s | 31.977 s | 31.720 s |

These individual observations vary by workload and run order. All thread-count audit outputs and type outputs matched their respective baseline bytes. Keep normal Lake/Lean defaults. Lean's `-j` is a per-process setting; the inspected Lake CLI does not expose the often-assumed `lake build -j N` option. No affinity, priority, power-plan or global environment setting was changed.

A candidate that reused one Lake environment across a complete checkpoint was **rejected**: baseline totals were 63.810/67.169 seconds, prototype totals 64.841/73.275 seconds. It supplied no reliable speedup. The prototype also printed only one selected type versus the baseline's 15, so these pilots are not strict full-output equivalence comparisons; no shortcut from that prototype is adopted, and its candidate files were removed. Preparing an environment once took 2.964 seconds, but isolated setup savings did not establish an end-to-end improvement.

The existing combined final audit/type pass is retained. Do not launch another root-import type process merely to reproduce types already present and fully reviewed in that final log. During proof iteration, use cached targeted Lake builds; a raw `lean` invocation re-elaborates its input even when a successful Lake artifact already exists. At a final checkpoint use the full root build directly; an unchanged targeted no-op immediately before it adds approximately six seconds without another correctness benefit. Rerun after relevant source changes or unresolved failures, rather than by habit. A changed mathematical source still requires the entire final verification procedure.

## Cache, dependencies and filesystem findings

- 8,529 Mathlib `.olean` files are present. Every required artifact for the tested full 6,072-job build is available; warm builds replay existing results. No cache download or compiler/dependency update was necessary. Preserve `.olean`, `.ilean`, trace/hash files and `.lake/packages`. If an artifact is missing, the pinned Mathlib cache tool supports targeted `cache get` by module; do not routinely run clean, forced cache restoration, or an unpinned cache scope.
- The pinned Lean `Lean/Util/CollectAxioms.lean` already stores exported transitive axiom dependencies in imported artifacts. Retain `Lean.collectAxioms` for every existing non-unsafe Foundation declaration. A new hand-written dependency scanner or shallow audit would duplicate machinery or risk weakening it.
- The complete audit still passes **36,736 declarations**, allowing only `propext`, `Classical.choice`, and `Quot.sound`. A scratch theorem indirectly depending on a forbidden axiom was correctly rejected. No fixture axiom entered the library.
- Incremental root traversal has measurable startup/metadata cost, but these experiments do not isolate physical disk latency from import/decompression CPU time. No source/import graph was rewritten, no antivirus exclusion or filesystem setting was added, and no cache was deleted. GPU/PyTorch changes were neither needed nor tested for this native Lean workload.

Keep `.lake/stardust-sync` and its referenced scanner. Preserve all manuscripts and unrelated drafts. The existing research queue, October 31 stop, and private-backup requirements are unchanged.

Raw commands, individual timings, hardware/import inspection, rejected pilots and accepted pairs are preserved in `STARDUST_PIPELINE_BENCHMARK_2026_10_20.json`. Detailed local logs are in `.lake/stardust-pipeline-benchmark` and `.lake/stardust-targeted-review-{1,2}`. All 1,923 prior mathematical source hashes and pinned configuration bytes were checked unchanged. Full-build and full-audit evidence from this audit remains valid for those exact unchanged mathematical inputs; documentation-only edits do not trigger another duplicate proof run.
