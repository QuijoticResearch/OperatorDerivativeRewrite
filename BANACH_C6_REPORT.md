# C6: infinite-dimensional quartic solvability

Starting commit: `498937d4055acdccb83f068b15809bc2a172b076`.
Pinned Lean: `leanprover/lean4:v4.34.1`.
Pinned Mathlib revision: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Library inspection before selecting the proof

The local pinned source was inspected independently before implementation.
The following are actual available APIs, not presumed library capabilities.

| Area | Module and declarations | Scope and limitation |
| --- | --- | --- |
| Continuous bidual | `Mathlib/Analysis/Normed/Module/DoubleDual.lean`: `NormedSpace.inclusionInDoubleDual`, `inclusionInDoubleDualLi`, `inclusionInDoubleDualWeak`, `isEmbedding_inclusionInDoubleDualWeak` | Canonical continuous-dual embedding and its isometry/weak embedding; no general surjectivity theorem |
| Weak compactness | Same module: `NormedSpace.isCompact_closure_of_isBounded` | Requires the weak-star closure of the image to lie in the bidual embedding's range; this hypothesis is substantive |
| Banach–Alaoglu | `Mathlib/Analysis/Normed/Module/WeakDual.lean`: `WeakDual.isCompact_of_bounded_of_closed`, `WeakDual.isCompact_closedBall` | Weak-star compactness in a dual, not automatic weak compactness in H |
| Weak closedness | `Mathlib/Analysis/LocallyConvex/WeakSpace.lean`: `Convex.toWeakSpace_closure` | Transfers closures of convex sets to the weak topology |
| Lower semicontinuity and minimization | `Mathlib/Topology/Semicontinuity/Basic.lean`: `lowerSemicontinuous_iff_isClosed_preimage`, `LowerSemicontinuousOn.exists_isMinOn` | General closed-sublevel criterion and compact-set minimum theorem; no automatic coercive minimization in a Banach space |
| Complete Lp | `Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`: `Lp.instCompleteSpace` | Complete scalar Lp for arbitrary μ and the relevant exponent; no σ-finiteness needed |
| Closed embedding | Existing `Foundation/BanachRange.lean`: `isClosed_range_of_lower_bound`, `rangeEquiv`, `rangeEquiv_symm_bound` | Complete H plus actual lower bound supplies a closed range and continuous linear equivalence to it |
| Uniform convexity | `Mathlib/Analysis/Convex/Uniform.lean`: `UniformConvexSpace` | No Lp instance found. Milman–Pettis and Hanner inequalities are listed as TODOs |
| Reflexivity / monotone surjectivity | No analytic Banach-reflexivity class, L4-reflexivity theorem, closed-subspace reflexivity transport, or Browder–Minty theorem found | `Module.IsReflexive` concerns the algebraic dual; `Module.instFiniteDimensionalOfIsReflexive` makes it unsuitable here |

The weak route is mathematically valid if reflexivity is expressed as
surjectivity of the canonical **continuous** bidual embedding. However,
formalizing the closed-subspace argument to derive this surjectivity would
require missing infrastructure. None of those analytic claims is assumed here.

## Chosen route: a norm-Cauchy minimizing sequence

For the actual energy `E(u) = ‖δu‖₄⁴/4 - f(u)`, prove a finite lower bound
and the estimate

    E((u+v)/2) + (c⁴/64) ‖u-v‖⁴ ≤ (E(u)+E(v))/2.

Choose an infimizing sequence. If both energies are less than
`inf E + (c⁴/64) ε⁴`, the midpoint estimate and the lower bound `inf E`
force `‖u-v‖ < ε`. Thus this sequence is norm-Cauchy. Completeness gives
its limit, and norm continuity gives a minimizer. The already verified
quartic Fréchet derivative and Fermat's theorem then yield `A(u)=f`.
Uniform monotonicity supplies uniqueness and the previous inverse estimate.

This route proves the solvability statement with **completeness alone**,
without explicit reflexivity. It applies in zero and infinite dimension.
It does not formalize the separate theorem that such H is reflexive.

## First verified milestone: reusable minimization

New module: `Foundation/QuarticUniformMinimization.lean`.

```lean
exists_minimizer_of_quartic_midpoint
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (E : H → ℝ) (hE : Continuous E)
    (hbelow : BddBelow (Set.range E))
    (k : ℝ) (hk : 0 < k)
    (hmid : ∀ u v,
      E ((1 / 2 : ℝ) • (u + v)) + k * ‖u - v‖ ^ 4
        ≤ (E u + E v) / 2) :
    ∃ u, ∀ v, E u ≤ E v
```

The proof uses Mathlib's `exists_seq_tendsto_sInf`, `csInf_le`,
`Metric.cauchySeq_iff`, and `cauchySeq_tendsto_of_complete`. Neither existence
of a minimizer nor convergence of a minimizing sequence is assumed. The
quantitative midpoint condition is a general structural hypothesis; the
actual L4 application must prove it from the scalar polynomial inequality.

Verification of this first milestone: the full Lake build passed (4028 jobs).
The transitive axiom audit passed for 1197 declarations. The new minimization
theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
Independent review of its body and elaborated type found no hidden
finite-dimensionality, reflexivity, nontriviality, or existence hypothesis.

## Exact remaining reflexivity infrastructure

The intended closed-range proof of analytic reflexivity needs:

1. Surjectivity of `NormedSpace.inclusionInDoubleDual ℝ (Lp ℝ 4 μ)` for
   arbitrary μ, for example from L4 uniform convexity and Milman–Pettis.
2. Inheritance of this continuous-bidual surjectivity by closed subspaces.
3. Transport under the already constructed equivalence `BanachRange.rangeEquiv`.

These are mathematically valid classical results, but are not supplied by
the inspected pinned APIs and are not proved in this milestone. They are
not necessary for the direct norm-Cauchy solvability argument. No use of
algebraic reflexivity, finite-dimensional compactness, or a surrogate
existence assumption is made.
