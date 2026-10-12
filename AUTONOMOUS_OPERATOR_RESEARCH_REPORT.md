# Autonomous operator-derivative research report

**Status: PARTIAL.** The trusted one-site Poisson calculus gained verified multiplier, commutator, Lipschitz-composition, and bounded quadratic-defect theorems. The Banach candidate requires interface replacement before migration. No Poisson-process stochastic integral, stable-Lévy adjoint, or full Banach representation theorem was proved.

## Repository state and milestone commits

The assignment named `c94b49ea666905a2e44e9ee92b9185e47da1e858` as its starting verified Poisson commit. At the start of this run the actual HEAD was already `ad57c40a66bddbb9f7984610fa4c305a50df87db`, which had completed the first bounded-multiplier milestone. That work was preserved. The last Lean-source commit in this run is `821fb73aafa7e405e160522ca30d8341710c426d`. The documentation/inventory commit containing this report is the repository HEAD when this file is read (`git rev-parse HEAD`); no history was rewritten.

| Priority | Commit | Result |
| --- | --- | --- |
| A1, already at turn start | `ad57c40a66bddbb9f7984610fa4c305a50df87db` | Bounded `g` preserves `dom(D)` for every `f∈dom(D)`; both factors and all terms are genuine scalar or weighted-field L² classes; shifted and three-term jump product rules, norm and representative-independence estimates. |
| A2 | `9518984702d0479b1c37cee8d18f90907d0fab59` | Bounded multiplier addition/composition, repeated domain preservation, exact commutator, alternate shifted rule and quantitative derivative bound. |
| A3a | `0d598a8652138fa9dd65d2da2cc42181ac80d62e` | Globally Lipschitz zero-preserving scalar compositions preserve the maximal difference domain; actual jump formula and derivative norm estimate. |
| A5 reconnaissance | `c62f0a2028c65835fc69cbcc0fef3daf3869e9a2` | [Banach integration plan](BANACH_INTEGRATION_PLAN.md), including two inconsistent candidate interfaces and the invalid predictable-integrand symmetry argument. No candidate source was modified. |
| A3b | `821fb73aafa7e405e160522ca30d8341710c426d` | Exact quadratic defect as a weighted-field L² equality for bounded count functions. |
| A4/A6 | This report and [43-declaration CSV inventory](POISSON_NEW_DECLARATIONS.csv) | Consolidation and scope review. No cosmetic abstract refactor was made. |

## Exact public declarations added or reviewed

The machine-readable inventory lists **all 43 public declarations** added from A1 through A3, with source file/line, kind, assumptions profile, scope, axiom status and paper relationship. Its assumptions column is a concise profile; the exact elaborated type remains the Lean declaration, and the main types were independently queried with `#check @...` after the final source commit.

- [PoissonMultipliers.lean](Foundation/PoissonMultipliers.lean): `scalar_mul_memLp`, `scalarMul`, `scalarMul_apply`, `scalarMul_eq_of_bounds`, `field_mul_memLp`, `fieldMul`, `fieldMul_apply`, `fieldMul_eq_of_bounds`, `scalarAsField`, `scalarAsField_apply`, `bounded_difference_bound`, `boundedDifference`, `boundedDifference_apply`, `boundedDifference_bound`, `shifted_memLp`, `shifted_multiplier_term_memLp`, `shifted_multiplier_term_norm_le`, `product_difference_memLp`, `scalarMul_mem_domain`, `scalarMul_difference_shifted`, `scalarMul_difference_expanded`, `scalarMul_norm_le`, `fieldMul_norm_le`, `bounded_representatives_eq`, `scalarMul_eq_of_representatives`, `fieldMul_eq_of_representatives`, `boundedDifference_eq_of_representatives`.
- [PoissonMultiplierAlgebra.lean](Foundation/PoissonMultiplierAlgebra.lean): `bounded_add`, `bounded_mul`, `scalarMul_comp`, `product_mem_domain`, `difference_commutator`, `difference_product_norm_le`, `scalarMul_add`, `difference_product_shifted_multiplier`.
- [PoissonLipschitzChain.lean](Foundation/PoissonLipschitzChain.lean): `composition_memLp`, `composition`, `composition_apply`, `composition_difference_memLp`, `composition_mem_domain`, `composition_difference_apply`, `composition_difference_norm_le`.
- [PoissonQuadraticDefect.lean](Foundation/PoissonQuadraticDefect.lean): `bounded_square_difference`.

These names are prefixed by `OperatorDerivativeRewrite.Foundation.<module>`. Core results have exactly `rate : ℝ≥0`, `0 < rate`, and the relevant boundedness/domain assumptions; the first composition `MemLp` lemma needs only nonnegative rate, scalar `L²` input, `LipschitzWith K φ`, and `φ 0=0`. No stochastic process, filtration, Gaussianity, or abstract representation assumption is hidden in their signatures.

Write `μ_λ` for Mathlib's Poisson measure, `S=L²(μ_λ)`, `K=L²(λμ_λ)`, `D` for the verified maximal difference, and `Sf(n)=f(n+1)`. The main new mathematical results are:

- If `|g(n)|≤C` and `f∈dom(D)`, then `gf∈dom(D)` and, in **K**, `D(gf)=gDf+(Sf)Dg=fDg+(Sg)Df=fDg+gDf+(Df)(Dg)`. `Dg(n)=g(n+1)-g(n)` and `|Dg|≤2C`. The proof establishes each field-L² term before equality.
- `[D,M_g]f=(Sf)Dg` in K, with `‖gf‖_S≤C‖f‖_S` and `‖D(gf)‖_K≤C‖Df‖_K+2C‖Sf‖_K`. This is an estimate involving the **shifted graph term**; no ambient-S-to-K boundedness of the commutator is asserted.
- If `φ : ℝ→ℝ` is globally `K`-Lipschitz and `φ(0)=0`, then every `f∈dom(D)` has `φ∘f∈dom(D)`, `D(φ∘f)(n)=φ(f(n)+Df(n))-φ(f(n))`, and `‖D(φ∘f)‖_K≤K‖Df‖_K`. This is an exact finite-difference formula, not a Gaussian differential chain rule.
- If `f` is a uniformly bounded count function, then its actual square belongs to `dom(D)` and `D(f²)=2fDf+(Df)²` **as a K equality**. The existing unbounded `X=N−λ` example separately proves `D(X²)=2X+1` with actual Poisson-moment/domain proofs.

## Verification

Each Lean-source milestone was followed by a complete `lake build` and direct `lake env lean Foundation/AxiomAudit.lean`, before its commit. Most recent source verification: **4021 jobs built**, audit exit 0 with **1,122 transitive `#print axioms` reports**. All 43 new declarations have axiom dependencies contained in `propext`, `Classical.choice`, and `Quot.sound`; none reports `sorryAx` or a custom mathematical axiom. The new source files contain no `sorry`, `admit`, `axiom`, or `unsafe`. The only persistent build warnings are the two preexisting unused-section-variable warnings in `Foundation/Adjoint.lean`; Lean also displays a harmless tactic suggestion in `PoissonLipschitzChain.lean`. The Banach candidate is **not part of this build** and fails to import its old Poisson module at the current Mathlib pin.

## Mathematical corrections and boundaries

- Boundedness of `g` alone suffices for one-site maximal-domain preservation because `Dg` is automatically bounded by `2C`. Neither `g∈dom(D)` alone nor unrestricted `dom(D)` multiplication gives this result. The independent Poisson audit supplies an explicit `f∈dom(D)` with `f²∈S` but `f²∉dom(D)`.
- `[D,M_g]` need not be bounded **from ambient S to K** for bounded `g`. With `g(n)=(-1)^n` and normalized scalar singleton vectors at count `N`, `‖f_N‖_S=1` while `‖[D,M_g]f_N‖_K=2√N`. The proved domain estimate uses `‖Sf‖_K`. A standard graph-norm-only inequality is mathematically available from `Sf=f+Df` and the scalar-to-field norm scaling, but the full scaling inequality was not added as a Lean theorem in this run.
- `Foundation/MultiplierCore.lean` concerns **divergence** multipliers with a bounded ambient commutator. Its abstract algebra theorems cannot be instantiated for arbitrary bounded Poisson `g` merely from `difference_commutator`: that commutator is generally unbounded on ambient S. Existing `AdjointClosure` and `AdjointBidual` lemmas already handle reusable Hilbert graph/adjoint operations. No new general helper was added because no concrete proof required one. `PoissonMultiplierAlgebra.bounded_mul` is a narrow wrapper around the earlier `PoissonBoundedCalculus.bounded_mul`; `scalarMul`/`fieldMul` are concrete positive-atom versions of generic bounded multipliers, retained here for pointwise operator formulas. These are documented overlaps, not conflicting mathematical definitions. Do not impose ordinary Leibniz on the jump model.
- The Banach candidate's universal `mk_dual_spec` and arbitrary-value isometry fields are inconsistent; the former implies `0=1`. The candidate's symmetry argument keeps a path-dependent predictable integrand fixed under `L↦-L`, which is invalid. Its total pointwise `L^q` products and assertion that Hilbert geometry kills jump defects also require replacement. These findings and a safe Mathlib-based dependency order are detailed in [BANACH_INTEGRATION_PLAN.md](BANACH_INTEGRATION_PLAN.md). No claimed Banach theorem has been certified by the trusted build.

## Remaining obligations and next priorities

1. **Poisson graph-norm refinement:** prove the shifted-field decomposition `Sf = scalarAsField(f)+Df` and the norm identity/inequality relating `scalarAsField(f)` to `√λ‖f‖_S`. Then state a clean graph-norm multiplier bound. For ambient commutator boundedness, characterize sufficient conditions such as a bound on `(n+1)|Dg(n)|²`; preserve the counterexample above.
2. **Broader finite-difference calculus:** extend Lipschitz composition from `φ(0)=0` to affine-growth maps using the finite Poisson measure; develop restricted L⁴ hypotheses for unbounded quadratic `f` and for `R_φ(f)=D(φ∘f)-φ'(f)Df` with actual derivative and remainder bounds. The bounded square theorem and centered-count example do **not** imply a universal square rule on `dom(D)`.
3. **Banach repair first, migration later:** prove a small genuine continuous-dual/Hölder adjoint module using Mathlib `lpPairing`, without `mk_dual` or process assumptions. Only then develop marked Poisson stochastic integration and a rigorous one-parameter range obstruction by uniqueness of mark kernels. Do not port the inconsistent source wholesale.
4. **Independent review:** scrutinize the counterexample to ambient commutator boundedness, exact K-normalization, the restricted square-domain hypothesis, and especially the two logical contradictions and predictable-integrand transformation in the Banach plan. Check the provenance of `BanachFinal_v12.tex` before any manuscript correction.

The report's machine inventory covers the 43 **new** public declarations, not every historical Gaussian/Poisson helper in the repository. The existing root and axiom audit remain the authoritative declaration lists. No original manuscript, legacy source, dependency pin, or preexisting untracked audit document was changed; no remote push occurred. Later IBM, pseudoprocess and black-noise work has not begun.

