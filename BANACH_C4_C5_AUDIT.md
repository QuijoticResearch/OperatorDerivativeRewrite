# Banach C4–C5 mathematical and Lean audit

Baseline: `1a66f5a64fef7533b2015be9e2996bdf144d2446`.
Pinned Lean: `leanprover/lean4:v4.34.1`; Mathlib lock revision:
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Independent audit before implementation

Verdict on the two baseline modules: **PASS with scope qualifications**.
The audit read the actual definitions and proof bodies, checked elaborated
types of all 31 public declarations, and ran their transitive axiom checks.
Both modules compiled directly. Their only axiomatic dependencies were
`propext`, `Classical.choice`, and `Quot.sound`.

`Foundation/BanachUnboundedAdjoint.lean`:

- `adjointGraph` (line 22) is the transposed pairing graph in `Y* × X*`.
- `adjoint` (line 85) uses density of the original domain to prove
  single-valuedness. No default value is used in place of an undefined adjoint.
- `adjoint_graph_eq` (line 107) proves equality of the entire graphs.
- `adjoint_mem_domain_iff_exists_bound` (line 139) characterizes the domain by
  boundedness in the ambient X norm, not the graph norm. The extension has
  real values, so completeness of X or Y is unnecessary.
- `boundedAsPartial_adjoint_apply` (line 202) gives exactly composition with
  the original bounded map, with no Riesz identification.
- `isClosable_of_adjoint_domain_separates` (line 219) has an explicit,
  substantive point-separation hypothesis. It does not derive that hypothesis
  from density of the original domain. No reflexivity or bidual recovery is claimed.

`Foundation/BanachLpDualityFour.lean`:

- `cube_memLp`, `dualityFour`, and `dualityFour_ae` (lines 21–37) construct
  the actual signed cube on equivalence classes for arbitrary measures.
- The moment, norm, and pairing lemmas (lines 40–114) prove genuine
  integrability and the exact identities, including zero.
- `normalFour` (line 132) is `A(u)(v) = ∫ (δu)^3 δv`. It is the bounded
  transpose composed with the cube map. It is not an assertion that every
  functional on L4 is represented by L(4/3), nor an unbounded adjoint identification.
- `normalFour_coercive` (line 143) assumes the actual bound
  `c * ‖u‖ ≤ ‖δu‖`, with `c > 0`. There is no concealed existence assumption.
- `normalFour_monotone` (line 167) uses integrable Hölder pairings and correct
  a.e. representatives. It proves only nonnegative pairing at baseline.

No blocking mathematical defect, circular assumption, totalized-integral
artifact, custom axiom, or unsafe proof shortcut was found. Formal verification
does not establish that a proposed stochastic integral satisfies the lower
bound or point-separation hypotheses: those remain separate mathematical tasks.

## C4: regularity and quantitative monotonicity

New module: `Foundation/BanachLpDualityFourContinuity.lean`.
It leaves all existing theorem statements and proof bodies unchanged.

The ambient assumptions are only a measurable space Ω, an arbitrary measure μ,
and, for the normal map, a real normed space H and an actual continuous linear
map `δ : H →L[ℝ] Lp ℝ 4 μ`. No probability, finite measure, completeness,
finite-dimensionality, or full Lp-dual representation hypothesis is added.

`squareProduct` and `cubeProduct` are Mathlib's continuous Hölder products
L4 × L4 → L2 and L2 × L4 → L(4/3). Their `_ae` lemmas identify genuine
pointwise multiplication. `dualityFour_eq_cubeProduct` proves equality with
the already verified cube map, rather than replacing its definition.

`contDiff_dualityFour` and `contDiff_normalFour` prove C∞ regularity by
composition of these continuous bilinear maps. `continuous_dualityFour`,
`locallyLipschitz_dualityFour`, `continuous_normalFour`, and
`locallyLipschitz_normalFour` are the corresponding consequences.

`cubic_uniform_monotone` proves the sharp real inequality

    (a³ − b³)(a − b) ≥ (a − b)⁴ / 4.

Its nonnegative remainder is `3/4 * (a-b)^2 * (a+b)^2`.
`normalFour_uniform_monotone` integrates this inequality with genuine
quartic and pairing integrability to prove

    (Au − Av)(u − v) ≥ ‖δ(u − v)‖₄⁴ / 4.

Under exactly `c > 0` and `∀ u, c * ‖u‖ ≤ ‖δu‖`,
`normalFour_uniform_monotone_lower` proves the lower bound
`(c^4 / 4) * ‖u-v‖^4`, and `normalFour_injective` proves injectivity.
Dual norm evaluation and cancellation of the nonzero distance prove
`normalFour_inverse_cubic_bound` and `normalFour_inverse_holder_bound`:

    ‖u-v‖³ ≤ (4/c⁴) ‖Au-Av‖,
    ‖u-v‖ ≤ ((4/c⁴) ‖Au-Av‖)^(1/3).

The zero-distance case is handled separately. These are estimates for the
inverse relation, valid even before proving surjectivity. They do not assume
finite-dimensionality. C5 must separately establish existence for every dual datum.

C4 verification: the complete `lake build` passed (4026 jobs). The project
transitive audit checked 1187 public declarations, including all 17 new C4
declarations. Its axiom union is exactly `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx` or custom axioms. A separate reviewer inspected
all C4 proof bodies and elaborated types with the same result. Existing warnings
in the older adjoint and Poisson modules are unchanged.

## C5: finite-dimensional existence and the actual inverse

New module: `Foundation/BanachLpDualityFourExistence.lean`.
The exact ambient parameters are

```lean
{Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
[NormedAddCommGroup H] [NormedSpace ℝ H]
(δ : H →L[ℝ] Lp ℝ 4 μ)
```

`hasFDerivAt_quarticPotential δ u` proves, with no finite-dimensionality or
lower-bound hypothesis,

```lean
HasFDerivAt (fun v : H => (1 / 4 : ℝ) * ‖δ v‖ ^ 4)
  (normalFour δ u) u
```

The proof writes the quartic energy as the L2 pairing of the genuine square
map with itself. Continuous bilinear differentiation gives four equal terms;
their pairing with each direction is identified a.e. with the already defined
`normalFour`. The L2 pairing is Mathlib's `lpPairing`, built from Hölder
integrability. There is no assumed derivative, exchange of unproved integrals,
or differentiability assumption on the norm at zero.

The remaining C5 declarations assume exactly

```lean
[FiniteDimensional ℝ H]
(c : ℝ) (hc : 0 < c)
(hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖)
```

There is no inner product, Riesz map, probability-measure, nontriviality,
separate completeness, or surjectivity hypothesis. Finite-dimensionality
supplies the proper-space compactness theorem; dimension zero is included.

`exists_quarticPotential_minimizer δ c hc hδ f` proves attainment of the
global minimum of `E(u) = ‖δu‖₄⁴/4 - f u`. The actual sublevel `E(u) ≤ E(0)`
is bounded: the proof first obtains `c⁴‖u‖⁴ ≤ 4‖f‖‖u‖`, then
`‖u‖ ≤ max 1 (4‖f‖/c⁴)`. It uses Mathlib's
`Continuous.exists_forall_le_of_isBounded` to attain the minimum.

`normalFour_surjective δ c hc hδ` applies
`IsLocalMin.hasFDerivAt_eq_zero` to the proved derivative `Au-f` at that
minimizer. Thus every `f : StrongDual ℝ H` has a solution. This direct
variational proof is shorter than constructing a new Brouwer or abstract
monotone-surjectivity framework; no such theorem is assumed.

`normalFour_existsUnique δ c hc hδ f` proves the exact statement

```lean
∃! u : H, normalFour δ u = f
```

using C4 injectivity. `normalFourEquiv δ c hc hδ : H ≃ StrongDual ℝ H`
is the resulting genuine bijection (not a linear equivalence).
`normalFourEquiv_apply` identifies its forward map, and
`normalFour_inverse_solves` proves its inverse solves the original equation.

For `T = (normalFourEquiv δ c hc hδ).symm`, the theorems
`normalFour_inverse_cubic` and `normalFour_inverse_holder` prove

    ‖T f - T g‖³ ≤ (4/c⁴) ‖f-g‖,
    ‖T f - T g‖ ≤ (4/c⁴)^(1/3) ‖f-g‖^(1/3).

These apply to every pair of continuous-dual inputs. The inverse is selected
by classical choice from proved existence and uniqueness. No arbitrary
surjectivity assumption is inserted into its definition.

There are no unresolved C4 or finite-dimensional C5 obligations. General
exponents and infinite-dimensional existence are outside this milestone.
Constructing a stochastic integral with the required norm bound remains a
separate task: these theorems apply to an actual supplied bounded-below map.

C5 verification: the complete `lake build` passed (4027 jobs). The project
transitive axiom audit passed for 1196 public declarations, including all
26 new C4–C5 declarations. The axiom union is exactly `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms occur.
Independent review of all nine C5 public declarations and their elaborated
types passed. A separate check instantiated `normalFour_surjective` at
`H = (Fin 0 → ℝ)`, `δ = 0`, `c = 1`, with arbitrary μ, and compiled.

No existing theorem bodies, original manuscripts, or dependency pins were
changed. The pre-existing untracked documents were preserved and excluded
from the commits. C4 and C5 are committed as separate verified milestones;
no changes are pushed.
