# Actual IBM finite-past derivative-core approximation — checkpoint 1303

IBM remains active. This checkpoint addresses the positive domain construction
after checkpoint 1302's temporal martingale obstruction. It does not complete
intrinsic stochastic calculus or establish a natural-time Clark–Ocone formula.

The actual raw IBM natural filtration and its closed past L2 subspaces are
`IBMNaturalFiltrationObstruction.naturalFiltration` and `.past`. The existing
`IBMFiniteAverageCore.intrinsicCore` is the intersection of actual IBM-observable
L2 with the two existing source/clock closed derivative domains. We define
`IBMPastAverageCore.pastCore T` as its intersection with the actual past at T.
This is a domain restriction, not a new stochastic process or a new derivative.

## Verified results

* `point_mem_past`: actual observations at s ≤ T belong to the past at T,
  using genuine strong adaptation and the established actual-process L2 bridge.
* `nativeAverage_mem_past`: the actual Bochner average A(r) lies in that past
  whenever r ≤ T. The proof commutes its orthogonal projection with the Bochner
  integral and uses the actual interval support (0,r]. Negative r gives an
  empty integration window; no positivity is silently needed for this result.
* `average_mem_core`: for 0 ≤ r ≤ T, A(r) belongs to both derivative domains
  and the actual past. It directly reuses the existing verified average graphs.
* `pastCore_mono`, `closure_le_past`: the domains increase with the horizon,
  and their L2 closures remain inside the corresponding actual past.
* `bounded_chain_past`: bounded C1 composition with bounded derivative preserves
  the common past domain, reusing the existing actual closed chain rule.
* `point_mem_past_core_closure`: every observation at 0 < t ≤ T is in its
  strong L2 closure. The approximants are
  e⁻¹(A(t+e)−A(t)), with −t < e < 0 and e tending to zero from below.
  Thus 0 < t+e < t ≤ T. In particular t=T is covered without future values.
* `IBMPastCylinderClosure.bounded_chain_closure` extends bounded C1 composition
  to this L2 closure by the explicit Lipschitz estimate
  ‖φ(u_n)−φ(f)‖₂ ≤ B‖u_n−f‖₂, with representatives handled almost everywhere.
* `point_cylinder_closure` covers every bounded C1 test with bounded derivative
  of every finite real weighted sum of actual IBM observations at 0<t_i≤T.
  Repeated times, terminal coordinates, negative weights and an empty finite
  index type are allowed. No joint Gaussian observation law is assumed.

All convergence asserted here is strong L2 of scalar observables. Individual
point observations are not asserted to lie in the clock derivative domain.
The argument is not graph-norm convergence of their derivatives. No derivative
of a natural conditional expectation or projection commutation is claimed.

## Reuse, independent checks, and exact remaining obligations

The global proof `IBMFiniteAverageCore.point_mem_core_closure` uses right-sided
increments. It is valid globally, but that proof cannot be reused unchanged at
a fixed terminal horizon. The new proof uses the already verified derivative
of A(t), taking its left-sided slope. The nonlinear proof retains the existing
chain-rule/Lipschitz argument with actual-past domain membership added.

Independent Lean checks instantiate terminal recovery, a mixed two-time sine
cylinder with positive and negative weights, an actual average in both domains,
and the zero-horizon/negative-window edge case. Full root build and complete
transitive Foundation axiom audit, public-type/proof review, source manifests
and manuscript checks are recorded in
`STARDUST_IBM_PAST_CORE_VERIFICATION.json`. Only the established standard three
axioms are allowed; no toolchain, trust or proof-resource changes are made.

**Still open:** prove that the closure is the ENTIRE natural-past L2 space.
Finite smooth Fourier cylinders now have the required approximation theorem;
the remaining connection is the finite weighted-law uniqueness/generated-sigma
density argument for the time-restricted observation family, including the
zero-time endpoint and the exact raw natural-filtration sigma algebra. Global
domain density alone does not imply density after intersection with a past.
Reuse `IBMFiniteWeightedLaws`, `IBMIntrinsicCoreDensity` and generic generated
density lemmas where their exact hypotheses apply. Do not silently substitute
the larger all-time observable sigma algebra for the finite past.

Then investigate closed past-restricted derivatives/adjoints and terminal Doob
conditional projections, and their relationship to the actual source-valued
divergence. Static source reconstruction at checkpoint 1301 is not natural-time
adapted reconstruction. Checkpoint 1302 remains valid: raw IBM is not a true
martingale; no semimartingale or local-martingale impossibility is asserted.

No manuscript was changed or ingested for an unrelated campaign. Preserve the
queue IBM → Bakry/fBM → Cauchy → fractional diffusion → black noise → backlog.
