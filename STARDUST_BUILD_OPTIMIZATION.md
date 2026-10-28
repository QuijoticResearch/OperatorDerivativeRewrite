# Permanent Stardust build and verification configuration

## October25,2026 dependency-invalidation observation

Checkpoint1529 retains every command, resource, compiler and trust setting below.
Its changed finite-Gaussian proof dependency caused a broad rebuild: the complete
6763-job root build passed in14607.4329544 seconds, the complete49630-declaration
axiom audit plus23 final types passed in41.4527709 seconds, and ten independent
checks passed in31.3397864 seconds. The latter required only test-elaboration
repairs; no heartbeat increase or mathematical source repair was used.

The rebuild rechecked the existing160-cell quartic kernel certificates
(`RiemannQuarticGridChecks`, Lake-reported9957 seconds) and downstream numerical
value cells. A read-only import-path audit traced that dependency to
`FiniteGaussianDensity` through Gaussian conditional calculus and quartic
analytic certificates. A live worker without recent log output was still
computing; successful bounded handle polls and increasing process CPU time
confirmed this. Preserve the running process rather than restarting on an
observation timeout. A completed module is not completion of the full root.

These are closure timings on CHANGED proof inputs, not a controlled comparison
with the cached October20 benchmarks. No speedup, regression attribution or new
optimization configuration is adopted. Retain the original settings and all
complete gates. Any future import separation or certificate-granularity change
needs its own reproducible timing/resource evidence, full verification and
reversible implementation before adoption.

This is permanent workflow infrastructure, not a mathematical campaign. Future sessions must consult this document before choosing build or verification commands. The research priorities and stopping rules remain in `STARDUST_CAMPAIGN_QUEUE.md`.

The adopted configuration is the measured October 20, 2026 configuration from commit `a2846f7f76c1aec6003c9beefbef0889ba13ff16`. Only preliminary theorem-type feedback demonstrated a reproducible improvement. **Retain the original build, compiler, parallelism and complete-audit configuration.** No full-build or full-audit speedup is claimed. The detailed experimental report is `STARDUST_VERIFICATION_PIPELINE.md`; raw commands and timings are in `STARDUST_PIPELINE_BENCHMARK_2026_10_20.json`.

## Environment and resource settings

- User-identified Lenovo Legion Tower 7i; independently verified Intel Core Ultra 9 285K and 24 logical processors.
- Windows 11, native environment reported as `Windows-11-10.0.26300-SP0`; 68,044,677,120 bytes of usable physical RAM, approximately 63.4 GiB, on the user's 64 GB system.
- Native Windows Lean `leanprover/lean4:v4.34.1`, Lake `5.0.0-src+5045d00`; pinned Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Mathematical benchmark baseline `c2c2e36b30c538454ade7f2bb5e903a5881330df`; 1,923 Foundation/root source files. The selected leaf was `Foundation.FractionalEndpointLaplace`.
- Keep existing `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, trust settings, axiom whitelist and compiler options. Use normal Lake scheduling and Lean's hardware-default threads. No CPU affinity, priority, memory cap, power-plan, GPU, antivirus or filesystem override is configured.

One-, four-, eight- and 24-thread Lean runs gave mixed results, with no reproducible global winner. Lean's process-local `-j` is not a supported `lake build -j` jobs flag in the inspected Lake CLI. Do not invent concurrency environment variables or change the permanent configuration from one favorable sample.

## Commands during proof development

Run from `C:\OperatorDerivativeRewrite`. The measured executables are:

```powershell
$stardustLake = 'C:/Users/ramir/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake.exe'
$stardustPython = 'C:/Users/ramir/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
```

Prefer the existing cache-aware targeted command while iterating:

```powershell
& $stardustLake build Foundation.FractionalEndpointLaplace
if ($LASTEXITCODE -ne 0) { throw 'Targeted build failed' }
```

Replace the module with the actual proof target. Lake follows transitive dependencies. Unlike repeatedly invoking `lake env lean Foundation/FractionalEndpointLaplace.lean`, this can reuse an unchanged successful artifact. Raw elaboration remains useful for a genuinely changed scratch proof; do not confuse its timing with a cached build.

The original preliminary type command imported the whole root:

```powershell
& $stardustLake env lean .lake/stardust-pipeline-benchmark/types.lean
if ($LASTEXITCODE -ne 0) { throw 'Type review failed' }
```

That benchmark file contains `import OperatorDerivativeRewrite` and the 15 explicit `#check @...` declarations. The optimized equivalent for preliminary feedback is:

```powershell
& $stardustPython -X utf8 tools/stardust_type_review.py `
  --run-dir .lake/my-new-type-review `
  --module Foundation.FractionalEndpointLaplace `
  --declaration OperatorDerivativeRewrite.Foundation.FractionalEndpointLaplace.scaled_sine_limit
if ($LASTEXITCODE -ne 0) { throw 'Preliminary type review failed' }
```

Use a fresh output directory. Repeat `--module` and `--declaration` for every item being reviewed; the benchmark supplied all 15 declarations to both methods. The helper builds the selected modules, prints explicit types, records wall times and exit codes, and checks source/configuration hashes before and after. Read the complete `types.log`. It does not edit proofs or suppress errors. Its output is deliberately `PRELIMINARY_TYPE_REVIEW_ONLY` and `checkpoint_eligible: false`.

Serialize proof/build work. The helper's exclusive lock coordinates helper instances, not unrelated Lake processes. Do not interrupt an active proof for routine benchmarking. After an interrupted helper, verify that its process and build have ended before removing its single stale lock file.

## Milestone commands and mandatory gates

The original and retained full-build command is unchanged:

```powershell
& $stardustLake build *> .lake/my-checkpoint-full-build.log
if ($LASTEXITCODE -ne 0) { throw 'Full build failed' }
```

The original and retained complete-audit command is unchanged:

```powershell
& $stardustLake env lean .lake/my-checkpoint-audit.lean *> .lake/my-checkpoint-audit.log
if ($LASTEXITCODE -ne 0) { throw 'Complete audit or final type check failed' }
```

Generate the checkpoint audit with `import OperatorDerivativeRewrite`, `import Lean`, and the existing canonical loop over every non-unsafe `OperatorDerivativeRewrite.Foundation` declaration, using **`Lean.collectAxioms` transitively** and accepting only `propext`, `Classical.choice`, and `Quot.sound`. Append explicit `#check @...` for all new public definitions and theorem types. A successful targeted build, preliminary review, cache hit, selected axiom print or old audit of changed sources never substitutes for this complete audit.

Before a milestone commit, retain the complete root build, complete transitive axiom audit, final unabridged public-type and complete proof/definition review, relevant independent mathematical tests, manuscript/source-integrity checks and research ledger. Then use an explicit-path commit and the exact-commit receipt/remote verification procedure in `STARDUST_SYNC.md`. Never silently disable a gate, suppress an error, change theorem semantics or certify unfinished work. The helper cannot approve a checkpoint.

Keep final type checks in the existing combined root audit/type pass. Do not start another root-import process solely to duplicate output already fully reviewed there. Do not insert an unchanged targeted no-op immediately before a required full build. Repeat verification when relevant inputs change, a check fails or a concrete concern remains. For documentation-only changes, existing successful complete-build/audit evidence may be retained **only after proving exact mathematical/configuration input identity and preserving all existing receipt requirements**; this does not authorize audit reuse after proof changes.

## Measured before and after

These are actual terminal wall-clock observations with warm artifacts. Rows retaining the same command are validation observations, not attributed speedups. No deleted-cache or cold-build experiment was performed.

| Operation | Original observation | Retained/optimized observation | Decision |
|---|---:|---:|---|
| Targeted cached Lake build | 6.109 s | 6.246 s, same command | Original configuration retained |
| Incremental complete root build | 9.685 s | 9.594 s, same command | Original configuration retained |
| Complete root audit plus 15 types | 39.034 s | 34.647 / 36.699 s, same command | Run variability; no claimed audit optimization |
| Preliminary review, matched pair 1 | 33.989 s | 25.605 s, including selected-module build | Adopt selected imports |
| Preliminary review, matched pair 2 | 32.824 s | 25.711 s, including selected-module build | Adopt selected imports |

Mean preliminary review fell from **33.4065 to 25.658 seconds: 23.19%**, with all 15 printed types byte-for-byte identical in both pairs. This improvement is reproducible for the recorded workload, not a universal promise for larger import closures. The full build still covers 6,072 jobs and the complete audit still covers 36,736 declarations on those exact mathematical inputs. The auditor also rejected a scratch theorem indirectly using a forbidden axiom.

A complete-checkpoint environment-reuse prototype was rejected: original totals 63.810/67.169 seconds versus prototype 64.841/73.275 seconds. Its printed-type subset also differed, so it was not a strict output-equivalence comparison. None of its candidate configuration is adopted. Full per-thread measurements and experimental limitations remain in the detailed report.

## Incremental compilation and cache strategy

Preserve `.lake/packages`, Lean `.olean`/`.ilean` artifacts and Lake trace/hash files. The inspected workspace contains 8,529 Mathlib `.olean` files and all artifacts needed by the tested build. No download, cache clear or forced restoration was needed. Lean already caches imported transitive axiom dependencies; use its canonical collector rather than a replacement scanner.

If a required Mathlib artifact is genuinely missing, inspect the pinned cache tool's targeted `cache get` workflow for that module. Never routinely clean dependencies, use unpinned cache scopes or run forced cache commands as a performance ritual. Preserve `.lake/stardust-sync` and its referenced scanner in every case. Keep `ResearchSources` strictly read-only and preserve unrelated work.

These measurements do not isolate physical disk latency from CPU import/decompression or other Windows activity. No filesystem/security changes were justified. Existing OS caches may affect repeats; record that limitation rather than asserting an unmeasured disk or GPU benefit.

## Rebenchmarking and rollback

Rebenchmark after material hardware, toolchain/Mathlib version, repository/import-graph/layout, storage/OS or resource-setting changes, and after a persistent regression. This instruction does not authorize changing the pinned versions. At a natural proof break, record terminal system time, exact commit/input hashes and environment; run matched warm targeted/full/audit/type workloads serially with all outputs and exit codes retained. Use multiple matched samples, identical declarations and the same verification obligations. Verify type-output equality and audit coverage, compare end-to-end costs, and preserve manuscripts/caches throughout. Adopt only reproducible, reversible improvements. If none survives, record the finding and retain the original configuration.

Immediate rollback of the only new optimization is to stop using the preliminary helper and use the original root-import type file with `lake env lean`. Continue the unchanged complete milestone procedure. No compiler setting, global environment, cache layout or mathematical source needs restoration. If retiring the helper permanently, make a reviewed workflow-only Git change to this document, the helper and its `AGENTS.md` instruction; do not reset the repository, revert mathematical commits wholesale or delete protected caches. Retain the raw benchmark record as history.

Permanent workflow ownership does not open a separate campaign or change mathematical priorities. Resume the authoritative saved research directive after workflow maintenance.


## Shared-import extraction validation, October 21, 2026

Checkpoint1259 extracts existing Jensen/canonical proofs into shared modules and
instantiates them for A2, preserving all19 existing theorem statements in three
refactored modules. Hardware, pinned toolchain, cache and resource configuration
remain unchanged. The new graph contains1960 Foundation/root source files and
6109 full-build jobs. A natural-checkpoint recheck measured:

- Dependency-invalidating full root build: 351.4603888s, terminal0.
- Cached target `lake build Foundation.RiemannQuadraticDivisor`: 8.2245605s, terminal0.
- Cached incremental `lake build`: 10.0008153s, terminal0.
- Complete transitive audit with all51 final public-type checks: 33.9355979s, terminal0;37414 declarations, only the standard three axioms.

The invalidating rebuild and cached builds are different workloads. These are
validation observations after an import-graph change, not a matched speedup study;
no additional optimization is adopted. The measured preliminary helper and the
original full-build/audit settings, verification gates and rollback remain in force.
Raw evidence is `.lake/stardust-1259-*-time.json` and the corresponding logs, with
cached observations in `.lake/stardust-1259-warm-timings.json`. Mathematical inputs
were hash-pinned before and after the timing checks. This does not reopen a separate
workflow campaign or change A2 priorities.


Checkpoint1260 continued the shared-proof extraction (1962 sources,6111 jobs),
preserving all18 prior theorem statements and the old inverse-product definition.
With the same pinned environment and original resource/cache settings, the
invalidating complete build took229.2174812s; cached target
`Foundation.RiemannQuadraticCanonical` took7.4310564s;
cached incremental root took9.8462918s; complete
37436declaration audit plus all41 final types took35.2526738s.
All terminal0. Raw evidence uses `.lake/stardust-1260-*-time.json`, corresponding
logs and `stardust-1260-warm-timings.json`. These are validation observations,
not a matched speedup study. No additional optimization or weaker gate is adopted.
