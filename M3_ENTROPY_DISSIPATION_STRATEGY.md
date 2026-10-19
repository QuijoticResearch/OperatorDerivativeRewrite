# M3 entropy dissipation: independent proof architecture review

Repository: `C:\OperatorDerivativeRewrite`.
Reviewed HEAD: `9cf1258426a9cd915eb2f3a6174f7fde7be4c6d1`.
Lean: `v4.34.1`. Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Upstream comparison: `mrdouglasny/markov-semigroups`,
`acf649108ea2222f4a8544a2782f448cb502492a`.

This is a mathematical architecture review, not a completed formal proof.
The proposed declarations below have not been implemented or kernel-checked.
Existing local source and pinned Mathlib source were inspected directly;
the cached upstream source from the earlier pinned audit was also inspected.
No Lean source, manuscript, dependency pin, or earlier statement is changed.

## 1. Recommendation

**Use route B: direct Gaussian interpolation, with a fixed-time rotation
followed by the verified one-dimensional bounded C¹ Stein identity.**

Retain the existing Mehler definition. Prove its positive-time time derivative
under the inner Gaussian integral, then differentiate the entropy under the
outer integral. At a fixed positive time rotate the two Gaussian variables
before integration by parts. This makes `g′` constant in the variable in
which Stein is applied. Only a first derivative of the entropy factor is
then required. Spatial C² smoothing and a pointwise OU-generator identity
are unnecessary for this target.

The decisive existing API is:

```
ProbabilityTheory.IsGaussian.map_rotation_eq_self
```

in `Mathlib/Probability/Distributions/Gaussian/Fernique.lean:252`. It proves
rotation invariance of the product of a centered Gaussian measure with itself.
Together with `GaussianSteinBounded.stein_identity`, this removes the principal
new analytic obligations of the classical generator route. Rotation invariance
must still be specialized to the Mehler coefficients and applied with proper
measurability/integrability; it is not inferred from the one-coordinate
`GaussianMehler.kernel_map` alone.

The current bounded C¹, uniformly positive hypotheses are sufficient. No C²
assumption on g, assumed Fisher decay, assumed dissipation, or approximation
hypothesis needs to be added. The previous recommendation to implement C²
smoothing first remains a valid route A plan, but it is not the shortest
route to this particular identity given the rotation theorem now identified.

**First implementation milestone for Sol Medium:** a small static Gaussian
rotation/Stein module proving the product-measure rotation law and the
`rotated_stein_identity` specified in section 6. It contains no entropy or time
differentiation. Its successful verification resolves the only distinctive
infrastructure risk of route B before beginning the two parametric-integral proofs.

## 2. Exact target, notation, and normalization

Let γ be the existing `GaussianCore.γ = gaussianReal 0 1`. Assume

- `g : ℝ → ℝ`, `ContDiff ℝ 1 g`;
- `0 < ε`, and `ε ≤ g(x) ≤ M` for every x;
- `|deriv g x| ≤ B` for every x.

Separate constants M and B avoid an unnecessary shared-bound restriction.
They satisfy M > 0 and B ≥ 0 as consequences of these hypotheses. Whenever
an existing M2b theorem takes a common bound, use `max M B`; do not change
that theorem. No normalization `∫ g dγ = 1` is needed.

For t > 0 write

```
a_t = exp(-t)
b_t = sqrt(1 - exp(-2*t))
u_t(x) = GaussianMehler.mehler t g x
m = integral g dγ
Φ(r) = r * log r
ψ_t(x) = 1 + log(u_t(x))
```

Then a_t > 0, b_t > 0, a_t² + b_t² = 1, a_t ≤ 1 and b_t ≤ 1.
Use the exact existing centered entropy:

```
E(t) = GaussianEntropyDissipation.entropyTrajectory g t
     = integral Φ(u_t) dγ - m * log m,     t ≥ 0.
```

The second equality is `entropyTrajectory_eq_invariant_mean`, with proved
integrability. The desired derivative is

```
HasDerivAt (GaussianEntropyDissipation.entropyTrajectory g)
  (-GaussianFisher.fisherInformation (GaussianMehler.mehler t g)) t
```

under the hypotheses above and `0 < t`. Its integrand is exactly
`(deriv (GaussianMehler.mehler t g) x)^2 / GaussianMehler.mehler t g x`.
There is no factor 2 and no square on the entropy input. The variance is one.

## 3. Complete mathematical argument for route B

### 3.1 Existing first-order spatial regularity suffices

M2b already proves the actual derivative formula

```
u_t′(x) = a_t * P_t(g′)(x).
```

Since g′ is continuous and bounded, `mehler_continuous` shows that the right
side is continuous in x. Combine it with the existing `HasDerivAt` theorem
using Mathlib `contDiff_one_iff_deriv` to obtain `ContDiff ℝ 1 u_t`.
This is a short packaging lemma, not positive-time C² smoothing.

The existing bounds give, for t ≥ 0,

```
ε ≤ u_t(x) ≤ M,
|u_t′(x)| ≤ a_t B ≤ B.
```

Consequently ψ_t is C¹, its actual derivative is

```
ψ_t′(x) = u_t′(x) / u_t(x),
```

and we have uniform bounds

```
|ψ_t(x)| ≤ L := 1 + |log ε| + |log M|,
|ψ_t′(x)| ≤ B / ε.
```

Use actual `HasDerivAt.log` or the derivative of log composed with u_t.
All denominator nonzero facts follow from the proved positive lower bound.
The log bound follows from monotonicity on `[ε,M]`; it does not require
M ≥ 1 or ε ≤ 1. `fisherInformation_integrable` already yields the necessary
finite Fisher integral, or use the explicit constant bound B²/ε.

### 3.2 Inner time differentiation and its uniform local dominator

Fix t₀ > 0 and work on `J = (t₀/2, 3*t₀/2)`. Set

```
c = b_(t₀/2) > 0,
m₁ = integral |y| dγ(y) < infinity.
```

For s in J, b_s ≥ c and 0 < a_s ≤ 1. Actual differentiation gives

```
a_s′ = -a_s,
b_s′ = a_s² / b_s,
∂s g(a_s x + b_s y)
  = g′(a_s x + b_s y) * (-a_s x + (a_s² / b_s) y).
```

Do not differentiate g′ here. `Real.hasDerivAt_sqrt` applies because
`1 - exp(-2*s) > 0`; prove this before simplifying the denominator.
For each fixed x and every s in J the derivative is bounded by

```
B * (|x| + |y| / c).
```

This is γ-integrable in y. The original integrand is bounded by M and
measurable. The derivative integrand is measurable because g′ is continuous.
Mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le` therefore proves

```
HasDerivAt (fun s => P_s g x) (T(t,x)) t,  t > 0,

T(s,x) = integral g′(a_s x + b_s y)
                    * (-a_s x + (a_s² / b_s) y) dγ(y).
```

Here T is a formula proved to be the derivative, not an independently
supplied derivative. The same estimates prove, for all s in J,

```
|T(s,x)| ≤ B * (abs(x) + m₁/c).
```

Prove the pointwise time derivative for every positive s, not just at t₀:
the outer differentiation theorem requires derivatives throughout a common
neighborhood of t₀. Obtain x-measurability of T(s,x) from the measurable
product integrand and the parameter-integral measurability API. A useful
stronger fact, also easy here, is continuity in x at fixed s: use dominated
convergence on `|x-x₀|<1` with bound
`B*(|x₀|+1+|y|/b_s)`. Joint time-space smoothness is not required.

### 3.3 Outer differentiation of finite entropy

For s > 0 the ordinary chain rule gives

```
∂s Φ(u_s(x)) = T(s,x) * ψ_s(x).
```

On J its absolute value is bounded by

```
B * L * (|x| + m₁/c),
```

which is γ-integrable in x. The input entropy integrand is already integrable
by `entropyTrajectory_integrable`. Measurability of it and of its derivative
follows from the results in sections 3.1–3.2. Apply the same Mathlib
parametric-integral theorem again to get the derivative of the uncentered
integral. Mean invariance on the open positive-time neighborhood makes the
centering term constant, so

```
E′(t) = integral ψ_t(x) * T(t,x) dγ(x).
```

For a Lean `HasDerivAt` transfer, use equality on a neighborhood of t, such as
`entropyTrajectory_eq_invariant_mean` on J. Do not rewrite this as a global
identity for negative times. No interchange of a derivative and an integral
is justified merely by the formal chain rule.

### 3.4 Fixed-time Gaussian rotation: the step avoiding g″

Fix t > 0; abbreviate a=a_t, b=b_t, u=u_t and ψ=ψ_t. Under γ⊗γ put

```
Z = a X + b Y,
V = -b X + a Y.
```

The pair (Z,V) has exactly the product standard Gaussian law. This is a
joint-law statement; Gaussian marginal laws alone do not imply it.
The inverse transformation is

```
X = a Z - b V,
Y = b Z + a V.
```

The velocity in section 3.2 is

```
-a X + (a²/b) Y = (a/b) V.
```

Fubini and the rotation law transform the entropy derivative into

```
E′(t) = (a/b) * E[ψ(X) g′(Z) V]
      = (a/b) * integral g′(z)
          * (integral v * ψ(a*z - b*v) dγ(v)) dγ(z).
```

For each fixed z apply the VERIFIED bounded C¹ Stein identity to

```
v ↦ ψ(a*z - b*v).
```

Its actual derivative is `-b * ψ′(a*z - b*v)`. Its function bound is L,
and its derivative bound is `b*B/ε`. Thus

```
integral v * ψ(a*z - b*v) dγ(v)
   = -b * integral ψ′(a*z - b*v) dγ(v).
```

The factor g′(z) is constant with respect to v. We never differentiate it;
g′ need only be continuous and bounded (even bounded measurable suffices
for this static interpolation lemma). Rotate back and apply Fubini:

```
E′(t) = -a * E[g′(Z) ψ′(X)]
      = -a * integral ψ′(x) * P_t(g′)(x) dγ(x)
      = -integral (u′(x))² / u(x) dγ(x).
```

The last equality uses the already verified `u′ = a P_t(g′)` and
`ψ′ = u′/u`. Cancel b only after proving b>0. This proves exactly the requested
normalization. The argument uses no Fisher decay theorem.

### 3.5 Integrability for every rotation and Fubini step

All functions are measurable. The following explicit bounds supply the
remaining product-measure integrability:

| Integrand | Integrable majorant |
|---|---|
| `ψ(x) g′(a*x+b*y) (-a*x+(a²/b)*y)` | `L*B*(a*abs(x)+(a²/b)*abs(y))` |
| `ψ(x) g′(a*x+b*y) (-b*x+a*y)` | `L*B*(b*abs(x)+a*abs(y))` |
| `g′(z) v ψ(a*z-b*v)` | `B*L*abs(v)` |
| `g′(z) ψ′(a*z-b*v)` | `B²/ε` |
| `ψ′(x) g′(a*x+b*y)` | `B²/ε` |
| `(u′(x))²/u(x)` | `B²/ε` |

The first absolute Gaussian moment and the probability mass one suffice.
The linear-coordinate majorants are integrable under the product measure,
using `integrable_prod_iff` or product integrability helpers. Prove these
facts before using `integral_prod`, `integral_prod_symm`, or
`integral_integral_swap`. `integral_map` has a statement valid for totalized
integrals, so its use alone is not evidence of finite entropy or finite
intermediate expectations. Retain the integrability facts independently.

## 4. Existing Lean declarations and precise reuse

All project names below are under `OperatorDerivativeRewrite.Foundation`.
The line references describe the reviewed HEAD/pinned sources.

| Location | Declarations | Role |
|---|---|---|
| `Foundation/GaussianMehler.lean:33,40,68,76` | `integrable_comp_of_bounded`, `kernel_integrable`, `mehler_norm_le`, `mehler_continuous` | bounded kernel integrability, spatial continuity and bounds |
| same file:158,176 | `integral_mehler`, `mehler_integrable` | constant mean for t≥0 and actual integrability |
| `Foundation/GaussianFisherDecay.lean:51,109` | `hasDerivAt_mehler_C1`, `deriv_mehler_C1` | actual first spatial derivative; use a common bound `max M B` |
| same file:117,32 | `mehler_lower_bound`, `fisherInformation_integrable` | positive denominator and finite Fisher integral |
| `Foundation/GaussianEntropyDissipation.lean:86,133,139,149` | `entropyTrajectory_integrable`, `entropyTrajectory_tendsto_zero_time`, `entropyTrajectory_eq_invariant_mean`, `entropyTrajectory_tendsto_atTop` | finite entropy, zero-time continuity, correct centering, ergodic limit |
| same file:70 | `mehler_time_continuous` | time continuity for bounded continuous g and g′ |
| `Foundation/GaussianSteinBounded.lean:39,80` | `stein_integrable`, `stein_identity` | bounded C¹ one-dimensional IBP for the rotated entropy factor |
| `Foundation/GaussianCore.lean:80,92` | `density_hasDerivAt`, `integrable_density_mul` | already used underneath Stein; no new PDF calculus needed |

Pinned Mathlib APIs:

| File under `Mathlib/` | Declaration | Exact use/restriction |
|---|---|---|
| `Probability/Distributions/Gaussian/Fernique.lean:252` | `ProbabilityTheory.IsGaussian.map_rotation_eq_self` | `μ[id]=0 → (μ.prod μ).map (ContinuousLinearMap.rotation θ)=μ.prod μ`; `IsGaussian`, complete second-countable real normed space with Borel structure; specialize to ℝ and γ |
| `Probability/Distributions/Gaussian/Basic.lean:60` | `ProbabilityTheory.isGaussian_gaussianReal` | supplies the Gaussian instance for γ |
| `Probability/Distributions/Gaussian/Real.lean:537,577` | `integral_id_gaussianReal`, `memLp_id_gaussianReal` | centeredness and first absolute moment |
| `Probability/Distributions/Fernique.lean:102,109` | `ContinuousLinearMap.rotation`, `rotation_apply` | formula is `(cos θ*x + sin θ*y, -sin θ*x + cos θ*y)`, matching this proof's signs |
| `Analysis/SpecialFunctions/Trigonometric/Inverse.lean:293,353` | `Real.cos_arccos`, `Real.sin_arccos` | choose θ=arccos a; show cos θ=a and sin θ=b from a²+b²=1, b≥0 |
| `Analysis/Calculus/ParametricIntegral.lean:288` | `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` | neighborhood measurability, integrability at base point, derivative measurability, uniform local integrable derivative bound, and actual pointwise derivatives; returns derivative integrability AND `HasDerivAt` |
| `Analysis/Calculus/ContDiff/Deriv.lean:98` | `contDiff_one_iff_deriv` | package u_t as C¹ from actual derivative plus continuity |
| `Analysis/SpecialFunctions/Log/NegMulLog.lean:71` | `Real.hasDerivAt_mul_log` | entropy chain rule at positive u_t(x) |
| `Analysis/SpecialFunctions/Log/Deriv.lean:112` | `HasDerivAt.log` | derivative of ψ_t with a proved nonzero argument |
| `Analysis/SpecialFunctions/Sqrt.lean:68` | `Real.hasDerivAt_sqrt` | b′(s), only where the radicand is nonzero |
| `MeasureTheory/Integral/Bochner/Basic.lean:1076` | `MeasureTheory.integral_map` | rewrite integration using the proved joint rotation law |
| `MeasureTheory/Function/L1Space/Integrable.lean:359` | `integrable_map_measure` | transfer integrability through that law if needed |
| `MeasureTheory/Integral/Prod.lean:230,440,463,478` | `integrable_prod_iff`, `integral_prod`, `integral_prod_symm`, `integral_integral_swap` | product integrability and justified Fubini |

Importing `Mathlib.Probability.Distributions.Gaussian.Fernique` and the inverse
trigonometric API uses the pinned Mathlib dependency; it does not introduce a
new external package. No covariance matrix or Hilbert tensor construction is
needed. A static arccos is sufficient: never differentiate arccos(t) in this
implementation.

## 5. Comparison with route A and pinned upstream

### What route A would prove

The classical route is mathematically valid under exactly the same C¹ input
hypotheses; C² regularity is an output about P_t g, not a necessary stronger
assumption about g. At fixed t>0 define

```
H_t(x) = integral y * g(a*x+b*y) dγ(y).
```

Stein in y gives `H_t = b P_t(g′)`, hence `u_t′=(a/b)H_t`.
Differentiate H_t in x under the integral using the majorant `a B |y|`:

```
u_t″(x) = (a²/b) * integral y * g′(a*x+b*y) dγ(y),
|u_t″(x)| ≤ (a²/b) B m₁.
```

A further dominated-convergence argument gives continuity of that derivative.
Then prove `T(t,x)=u_t″(x)-x*u_t′(x)` and apply Gaussian IBP to the bounded C¹
function `ψ_t * u_t′`. Its derivative contains `ψ_t′u_t′+ψ_t u_t″`, with
proved bounds. This yields `∫ψ_t Lu_t=-∫ψ_t′u_t′`.

Using the new local Stein theorem, the final bilinear identity can be much
shorter than porting upstream's separate weighted-PDF proof. Nevertheless,
route A must still build the actual second spatial derivative and its
continuity/bound, identify the time derivative with it, and package the
bilinear IBP. Those results are valuable for a later generator library, but
none is needed for the present entropy target.

### Upstream findings

At the pinned commit, inspect:

- [OUEntropyDecomposition.lean:607](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/General/OUEntropyDecomposition.lean#L607),
  `Gaussian1D.hasDerivAt_entropy_ouSemigroup`.
- [EuclideanStein.lean:165](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/EuclideanStein.lean#L165),
  `Gaussian1D.stein_identity_standard`, and the same file at line 703,
  `gaussian_dirichlet_form_bilinear`.
- [Euclidean.lean:1209](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean#L1209),
  `Gaussian1D.ouSemigroup_entropy_sq_ergodic`.

The entropy derivative proof follows route A. Its substantial local blocks
include `h_stein_x` at 838, the weighted spatial integral differentiation near
903, `h_Ptg_C2` at 991, inner time differentiation around 1147, outer entropy
differentiation around 1300–1545, and the final bilinear IBP around 1555.
Its final theorem assumes C¹ g, ε≤g≤M, and |g′|≤M. It does not simply assume
that P_t g is C²: it proves the missing smoothing in the body. Historical
comments about partial proofs must not be mistaken for the actual proof terms.

**Normalization difference:** upstream `boltzmannEntropy` at line 73 is
`∫ g log g`, without the centered mean subtraction. Its theorem is not literally
the local `entropyTrajectory` statement. Use local invariance to bridge them.
The existing local centered ergodic-limit theorem already supplies the limit
needed here; porting the upstream square-core ergodic theorem again is unnecessary.

Reuse upstream's coefficient bounds and the inner/outer parametric-integral
proof pattern. Preserve Michael R. Douglas's copyright and Apache-2.0 notices
if code is adapted. Do not import its abstract `BakryEmerySpace`, its entire
concrete instance, or conclusions stored in abstract structure fields.
The upstream has not been independently rebuilt or kernel-audited in this review;
every adapted local result will require a fresh transitive axiom audit.

### Relative amount of new Lean work

Both routes share: time-kernel differentiation with local domination; C¹
packaging and log-factor bounds; outer differentiation; centering and final
assembly. Count separately meaningful mathematical obligations, not arbitrary
splitting of Lean files:

| Route-specific work | Route A | Route B |
|---|---|---|
| New law/IBP lemma | affine Stein identity for H_t | rotation-law specialization and static rotated Stein identity |
| New spatial differentiation | weighted H_t derivative | none beyond existing M2b first derivative |
| Higher regularity | continuous u_t″, its bound, C² packaging | none |
| Generator identification | T = u_t″ - x u_t′ | none |
| Final pairing identity | bilinear Gaussian Dirichlet identity | supplied by static rotated Stein |

**B has fewer new analytic lemmas and is the recommended shortest route.**
The exact Lean line count is not known without implementation. A has more
upstream code ready to adapt; B has less analytic work but a new local
rotation/Fubini wrapper. The small first milestone is intended to test this
tradeoff before investing in time differentiation.

Reject A as the immediate implementation route because it proves stronger
spatial facts than this target needs. Do not reject it as invalid, or suggest
that it inherently requires C² input. If the rotation wrapper reveals a concrete
unforeseen incompatibility, A remains a fully specified fallback; record that
obstruction instead of assuming a rotation identity or adding C² g silently.

A naive version of B that applies Stein separately in x and y to
`ψ(x) g′(a*x+b*y)` is also rejected: both applications differentiate g′ and
reintroduce g″. Their formal cancellation does not justify either application
for merely C¹ g. Rotation is what makes this route valid. An angular time
parameter is possible, but adds parameter-conversion and arccos-derivative
bookkeeping without removing either differentiation-under-integral obligation.

## 6. Small independently verifiable implementation milestones

All names here are proposals, not claims about existing declarations.

### B1 — Static rotation and Stein pairing (implement first; then stop)

Suggested new module: `Foundation/GaussianMehlerInterpolation.lean`.
Use the existing γ. For a,b≥0 and a²+b²=1 let
`R(x,y)=(a*x+b*y,-b*x+a*y)`.

1. `gaussian_rotation_map`: prove `(γ.prod γ).map R = γ.prod γ`.
   Apply `IsGaussian.map_rotation_eq_self` with θ=arccos a. Centeredness is
   `integral_id_gaussianReal`; the rotation formula has the correct signs.
   Show `-1≤a≤1`, `sqrt(1-a²)=b`, and simplify the continuous linear map.
   No random-variable independence theorem needs to be reproved.
2. `rotated_stein_integrable`: for bounded measurable k, bounded C¹ ψ with
   bounded actual ψ′, prove both displayed product integrands below integrable.
   Also establish integrability of the rotated expressions within the proof.
3. `rotated_stein_identity`: under exactly those hypotheses prove

```
integral p, ψ(p.1) * k(a*p.1+b*p.2) * (-b*p.1+a*p.2) d(γ.prod γ)
  = -b * integral p, deriv ψ p.1 * k(a*p.1+b*p.2) d(γ.prod γ).
```

Precisely, the hypotheses are `0≤a`, `0≤b`, `a²+b²=1`, `Measurable k`,
`∀z, |k z|≤K`, `ContDiff ℝ 1 ψ`, `∀x, |ψ x|≤A`, and
`∀x, |deriv ψ x|≤C`, for real K,A,C. No derivative or continuity of k is
required. Apply Stein in v to `ψ(a*z-b*v)`, multiply by k(z), integrate in z,
and rewrite both sides with the proved rotation law. The b=0 case is valid
and needs no division; keeping it avoids an unnecessary restriction on this
static lemma. Bounds are `K*A*(b*|x|+a*|y|)` and `K*C` before rotation,
and `K*A*|v|` and `K*C` afterward.

**Acceptance:** no hypotheses containing map-law equality, the desired IBP,
or integral finiteness as substitutes for the bounds; use actual derivatives;
explicit product integrability; full Lake build; exact declaration checks;
`#print axioms` for all new declarations, including transitive Mathlib imports;
no custom axioms or `sorryAx`; attribution for adapted code. Do not start time
or entropy differentiation in B1. This is the concrete first request for
Sol Medium.

### B2 — Actual positive-time derivative of the existing Mehler kernel

Suggested focused module: `Foundation/GaussianMehlerTimeDerivative.lean`.
Prove the coefficient derivatives, `hasDerivAt_mehler_time`, and the uniform
local derivative bound from section 3.2, together with derivative-integrand
integrability and x-measurability. Initial assumptions can be `ContDiff ℝ 1 g`,
`|g|≤M`, `|g′|≤B`; positivity is not needed until entropy. Use existing
`GaussianMehler.mehler`, not a second semigroup implementation.

The central conclusion must be a `HasDerivAt` of `fun s => mehler s g x`,
with the explicit T formula, not a theorem about an unrelated supplied
function. An explicit `J`-uniform bound is part of acceptance because a
single-time bound cannot support the next differentiation.

### B3 — Finite centered entropy derivative and final assembly

After B1–B2, add small C¹/log preparation lemmas and the raw entropy derivative
proved by the outer parametric-integral theorem. A proposed intermediate
`hasDerivAt_entropyTrajectory_raw` has the actual entropy function as its
subject and derivative `∫ ψ_t(x)*T(t,x) dγ(x)`. Apply B1 with
`k=deriv g` and `ψ=ψ_t`, then reuse M2b spatial commutation to identify the
answer as negative Fisher information. Preserve exact centered normalization.

Acceptance is the target statement in section 2 under bounded C¹ input,
positive lower bound, and the original uniform derivative bound; all
integrability and pointwise identities proved; no C² input requirement;
full build and transitive axiom checks. This completes positive-time M3.
Do not begin log-Sobolev or broader semigroup/operator-domain development.

## 7. Hidden analytic obstacles and zero time

1. **Joint law:** `kernel_map` proves the law of Z only. The rotation lemma
   must prove the joint law of (Z,V), with the actual sign convention above.
2. **Freezing time:** in the rotation/Stein step t is fixed. Differentiate the
   entropy first; do not incorrectly treat `ψ_s` as constant while
   differentiating a time-dependent double-integral representation.
3. **Local versus pointwise control:** both derivative-under-integral calls
   require a common neighborhood and a dominator independent of s there.
   The derivative candidate must be measurable at the base time, and its
   pointwise derivative identity must hold throughout that neighborhood.
4. **C¹ packaging:** M2b has `HasDerivAt` and a derivative formula, not a
   ready-made `ContDiff ℝ 1 (P_t g)` declaration. Derive it from continuity
   of P_t(g′). Do not infer it from mere differentiability alone.
5. **Actual derivatives:** applying Stein directly to a formula involving g′
   in the differentiated variable would require g″. The proposed static
   pairing deliberately keeps k(z) constant in that variable.
6. **Integrability:** product-measure Fubini and mapped integrals require
   the explicit bounds in section 3.5. A finite-valued Bochner integral or
   an `integral_map` equality by itself proves no finiteness.
7. **Positivity:** every log-chain rule and division uses ε≤P_tg. Never
   exploit Lean's totalized reciprocal or logarithm at zero to remove this
   analytic hypothesis. The constants do not require ε≤1≤M.
8. **The boundary t=0:** b₀=0 and a_t²/b_t diverges as t↓0. The positive-time
   dominator is not uniform down to zero. The verified
   `entropyTrajectory_tendsto_zero_time` already supplies the required
   continuity; use it separately. No two-sided time derivative at zero is
   claimed, since the formula's negative-time extension is not the OU semigroup.
9. **Optional one-sided endpoint identity:** if needed later, use time
   continuity of P_tg and P_t(g′), M2b commutation and domination B²/ε to prove
   `I(P_tg) → I(g)` from the right. After positive-time dissipation, FTC on
   `[r,T]`, entropy continuity and r↓0 yield the integrated identity; the
   Fisher limit then gives the right derivative. This requires its own FTC
   and convergence justification, not substitution t=0 into a formula with
   1/b_t. It needs no assumed Fisher decay.
10. **At infinity:** centered entropy convergence to zero is already verified
    for bounded continuous inputs. It is not proof of dissipation and is not
    used to justify differentiation. Later integration to infinite time is
    a separate step using the already proved Fisher decay if desired.

No additional analytic hypotheses are required for the stated bounded C¹
core theorem. Removing boundedness or the positive lower bound to obtain a
larger-domain theorem would require new truncation/regularization and limit
arguments; none is asserted by this plan. In particular, applying gε=f²+ε
and later letting ε↓0 belongs to the later log-Sobolev milestones.

## 8. Review outcome

**GO with route B.** Implement B1 first: specialize the existing Mathlib
Gaussian rotation theorem and prove the static bounded-measurable/C¹ rotated
Stein pairing with all product integrability. Then implement the common
inner and outer dominated-differentiation steps and assemble the exact
centered entropy identity. No new general semigroup framework is justified.

This review creates only this strategy document. It does not run a new
proof build or claim that any proposed theorem has been verified. The existing
verified HEAD and source statements are preserved; no automatic commit is made.
