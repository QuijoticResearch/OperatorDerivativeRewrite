# Legacy Gaussian log-Sobolev integration

The source is [C:\Operator\OperatorDerivative.lean](C:/Operator/OperatorDerivative.lean). The full integration copy is [OperatorDerivativeIntegrated.lean](C:/OperatorDerivativeRewrite/Legacy/OperatorDerivativeIntegrated.lean). A separate [GaussianLogSobolevSection.lean](C:/OperatorDerivativeRewrite/Legacy/GaussianLogSobolevSection.lean) contains the unchanged source prefix through `log_sobolev_1d` with the same two edits: an import of `Foundation.GaussianLogSobolevFull` and replacement of `bakry_emery_log_sobolev` by a theorem using the proved Gaussian inequality. It ends with `#print axioms` for the replacement and its unchanged immediate consumer.

The integrated full copy differs from the original only by that import and axiom replacement. The original source and manuscript remain untouched. In particular, legacy comments that still describe an axiom, a general Bakry–Émery implication, and unproved downstream claims are preserved verbatim as historical source text; they are not endorsements of those claims.

## Verified scope

Using the repository's pinned Lean 4.34.1 toolchain:

```powershell
$lake = 'C:\Users\ramir\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lake.exe'
& $lake env lean Legacy/GaussianLogSobolevSection.lean
```

This targeted check succeeds. Both declarations print exactly `[propext, Classical.choice, Quot.sound]` as their transitive axioms, with no `sorryAx` or custom analytic axiom. The original axiom's type annotation is copied exactly; the independent audit [INDEPENDENT_FULL_GAUSSIAN_LSI_AUDIT.md](C:/OperatorDerivativeRewrite/INDEPENDENT_FULL_GAUSSIAN_LSI_AUDIT.md) additionally checked definitional equality of the fully elaborated original type and the adapter. `log_sobolev_1d` remains byte-for-byte unchanged in the two integration copies.

This proves the **one-dimensional standard Gaussian** log-Sobolev inequality under the legacy hypotheses. It does not establish an abstract Bakry–Émery curvature criterion, tensorization, hypercontractivity, or the legacy energy-space claims.

## Full legacy file status

The full integration copy is deliberately outside the default project imports. Directly checking it with

```powershell
& $lake env lean Legacy/OperatorDerivativeIntegrated.lean
```

fails at the following locations. Each corresponds to the same existing error in the unmodified original, shifted by eight lines (two import lines and six adapter lines). The axiom replacement and `log_sobolev_1d` produce no errors.

| Integrated copy line | Original line | Legacy declaration | Error |
|---:|---:|---|---|
| 3164 | 3156 | `concrete_expect_constEmb` | Rewrite pattern not found |
| 3280 | 3272 | `concrete_mul_memLp` | `MemLp.mul'` type mismatch |
| 3308 | 3300 | `pip_memLp_one` | Invalid constructor notation |
| 3617 | 3609 | `brownianEnergySpace` | `simp` made no progress |
| 3638 | 3630 | `brownianEnergySpace` | `simp` made no progress |
| 3704 | 3696 | `memLp_four_mul_of_memLp_eight` | Unresolved Hölder triple instance |
| 4464 | 4456 | `memLp_two_mul_of_memLp_four` | `MemLp.mul'` type mismatch |

The integration milestone is the **verified replacement section** and a faithful full development copy for later repairs. `lake build` checks the existing project and the focused section is checked directly. Neither result should be presented as a successful compilation of the full legacy file.
