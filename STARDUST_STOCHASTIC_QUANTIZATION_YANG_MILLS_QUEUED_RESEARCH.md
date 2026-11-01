# Queued research brief — stochastic quantization Yang–Mills

Status: QUEUED at the END of the entire existing authoritative queue, including
all previously saved backlog. Added November 1, 2026 by explicit user request.
Do not activate now. Cauchy remains active; A(2)/RH follows Cauchy immediately.
The user's scheduling request fixes the position of the separately proposed
campaign below. Preserve all preceding priorities, paused obligations and audits.

The following is the complete user-supplied objective, preserved verbatim as
text (line endings normalized only). Its named literature is a future research
starting point, not a claim independently checked during this queue update.

---

# Project Stardust — Stochastic Quantization Route to 4D Continuum Yang–Mills

## Mission

Investigate stochastic quantization as an alternative and complementary route toward constructing four-dimensional continuum Yang–Mills theory and ultimately establishing a positive physical mass gap.

Use the work of Chandra, Chevyrev, Hairer, Shen, and related researchers as a starting point, while exploiting the full cumulative, formally verified Project Stardust library.

**The long-term objective is genuine four-dimensional continuum Yang–Mills, including nontrivial existence and a positive physical mass gap—not simply a finite-dimensional stochastic process, a three-dimensional construction, or a formal analogy.**

Approach this as an independent mathematical research program. Seek substantive new theorems, identify genuine obstructions, and permit unexpected mathematical connections, provided every claim is correctly scoped and verified.

## 1. Primary research foundations

Begin with a theorem-level examination of relevant stochastic Yang–Mills literature, including:

- Chandra, Chevyrev, Hairer and Shen, *Langevin Dynamic for the 2D Yang–Mills Measure*.
- Chevyrev, Shen and collaborators, *Stochastic Quantisation of Yang–Mills–Higgs in 3D*.
- Relevant subsequent work on gauge covariance, renormalization, regularized Wilson loops, singular SPDEs, and lattice-to-continuum approximations.
- Appropriate foundational work on stochastic quantization, regularity structures, paracontrolled distributions, gauge theory, and constructive Yang–Mills.

Retrieve and inspect the actual papers, theorem statements, hypotheses, and proofs. Distinguish established results from conjectures, heuristics, and possible extensions.

Identify precisely what works in dimensions two and three, what fails or becomes singular in dimension four, and which mechanisms might plausibly be extended.

Do not treat lower-dimensional stochastic quantization as evidence that the four-dimensional existence or mass-gap problems are already solved.

## 2. Audit and reuse the entire Stardust library

Before building new mathematical foundations, perform a focused theorem-level crosswalk of reusable Lean developments.

Prioritize:

**Stochastic calculus and Gaussian analysis**

Closed Gaussian derivatives, Malliavin operators, divergence adjoints, stochastic integration, conditional projections, Gaussian chaos, Hilbert-space representations, and stochastic reconstruction.

**SPDE and operator calculus**

Closed generators, semigroups, resolvents, Sobolev and Fourier estimates, regularity results, mild formulations, energy identities, and stochastic evolution methods.

**Existing Yang–Mills campaign**

Reuse the preserved SU(2) Wilson lattice constructions, gauge invariance, physical transfer operators, conditional Gram identities, winding observables, spectral estimates, stationary conditional laws, and all verified positive and negative results.

Read the Yang–Mills stopping and multiblock audits before proposing any new contraction or mass-gap argument.

**Higher-order and signed calculus**

Audit the IBM, pseudoprocess, and multichannel derivative machinery for genuinely applicable operator constructions. Do not transfer signed-functional identities into positive probability spaces without proving the required hypotheses.

Produce an exact crosswalk between reusable declarations and the new stochastic-quantization objectives.

For each proposed reuse, identify its original theorem, hypotheses, domains, scalar field, measure, topology, and the additional proof obligations needed for the new application.

Avoid duplicating infrastructure already available in Stardust.

## 3. Construct a genuine stochastic Yang–Mills bridge

Seek a rigorous bridge from finite lattice gauge theory to stochastic quantization.

Investigate, in a mathematically justified order:

1. Finite-lattice Langevin dynamics with the actual Wilson action, including its invariant Gibbs measure, generator, Dirichlet form, and gauge covariance.
2. A gauge-compatible stochastic evolution and its induced dynamics on gauge-invariant observables or gauge orbits.
3. Exact relationships between the stochastic generator, conditional Wilson operators, lattice transfer operators, and equilibrium correlation functions.
4. Renormalization and ultraviolet estimates required to pass toward continuum gauge fields.
5. Tightness, convergence, nontriviality, and identification of any proposed continuum measure or dynamics.
6. Reflection positivity, reconstruction, connected-correlation decay, and the spectral mechanisms necessary for a physical mass gap.

Do not infer continuum existence from finite-lattice invariant measures.

Do not infer a physical mass gap from ergodicity in stochastic quantization time. Stochastic-quantization time and physical Euclidean separation are different variables; an exact theorem connecting their relevant estimates is required.

Preserve gauge covariance throughout. If gauge fixing is introduced, prove the required compatibility and identify the treatment of gauge redundancy, Gribov-type issues, and reconstruction of gauge-invariant observables.

## 4. Target the four-dimensional obstruction directly

Identify the precise mathematical obstruction preventing known lower-dimensional stochastic-quantization methods from establishing the four-dimensional continuum theory.

Investigate whether Stardust's existing operator and stochastic-analysis machinery offers a genuinely new way to control:

- Critical regularity and renormalization.
- Gauge-covariant stochastic evolution.
- Scale-uniform estimates and compactness.
- Wilson-loop observables and their continuum limits.
- Nontrivial continuum correlation functions.
- Physical-distance connected-correlation decay.
- Spectral reconstruction and a positive physical mass gap.

Distinguish ultraviolet existence and renormalization problems from the infrared spectral/mass-gap problem. Neither automatically solves the other.

Prioritize estimates that survive changes in lattice spacing, volume, coupling, and renormalization scale under explicitly stated hypotheses.

Do not promote finite-volume bounds, gauge-fixed estimates, or conditional operator identities into continuum results without the necessary uniformity and reconstruction theorems.

## 5. Seek new cross-domain mathematics

Actively investigate whether the combination of stochastic calculus, SPDEs, Gaussian operators, and the existing Wilson-lattice results creates mathematical tools unavailable from any one branch alone.

Particularly investigate:

- Conditional stochastic projections and gauge-covariant reconstruction.
- Closed derivative/divergence operators on gauge-invariant observable spaces.
- Higher-order stochastic responses where first-order Wilson innovations fail.
- Dirichlet forms, conditional Gram estimates, and stochastic generator identities.
- Connections between stochastic evolution and physical transfer/spectral operators.
- Multiscale stochastic operator bounds and possible renormalization-compatible domains.

These are research directions, not established implications.

Favor exact mathematical mechanisms over superficial analogies. If an attempted transfer fails, construct the sharpest useful counterexample or obstruction and preserve it.

## 6. Mathematical verification requirements

Every substantive mathematical milestone must satisfy Stardust's existing standards:

- Genuine Lean 4 proof using the pinned Mathlib environment.
- No `sorry`, new mathematical axioms, unsafe shortcuts, or suppressed errors.
- Complete root build and transitive axiom audit.
- Full public theorem-type and proof review.
- Independent tests, including adversarial cases and counterexamples.
- Exact domains, hypotheses, measurability, convergence topology, and quantifier order.
- Research-ledger updates, source-integrity checks, audited Git checkpoints, and guarded verification of both authorized public branches.

Explicitly distinguish verified theorems, conditional theorems, conjectures, numerical evidence, heuristics, and unresolved obligations.

Preserve all original research sources and manuscripts. Follow Stardust's established separation between research and publication responsibilities.

## 7. Research strategy and milestones

Begin with a bounded feasibility and theorem-transfer audit, then select the strongest mathematically justified route.

The first major milestone should be a **genuine stochastic-quantization theorem instantiated on the existing Wilson system**, with exact gauge, measure, and operator hypotheses.

The next milestone should connect that stochastic formulation to a physically meaningful gauge-invariant observable or transfer/correlation estimate.

Only then attempt the relevant scale-uniform or renormalization problem.

The eventual objective is a verified route toward four-dimensional continuum existence and a positive physical mass gap.

Do not confuse the existence of a research program with progress on those final objectives.

If a route fails, preserve the mathematical results and move to the next promising mechanism rather than indefinitely refining an approach whose central estimate is impossible.

## 8. Research deliverables

Maintain a concise technical ledger documenting:

- Exact literature and theorem comparisons.
- Verified Stardust declarations reused.
- New mathematical constructions and theorems.
- Genuine counterexamples and obstructions.
- Which four-dimensional obligations remain open.
- Whether each result advances continuum construction, the physical mass gap, both, or neither.
- Independent novelty assessment against existing research.
- The strongest next mathematical question.

Provide a clear assessment at each significant checkpoint of whether the program is advancing toward four-dimensional continuum Yang–Mills or merely constructing auxiliary mathematics.

## 9. Scheduling and preservation

Treat this as a separately proposed research campaign, not an instruction to silently interrupt Cauchy or the currently authorized A(2)/RH queue.

If activated, preserve the existing queue and return points explicitly. Never overwrite the earlier Yang–Mills stopping audit or represent the earlier campaign as completed.

Reuse its work as a foundation for the new stochastic-quantization approach.

**Guiding principle:**

Shoot for the stars to collect the stardust.

The target is four-dimensional continuum Yang–Mills and its physical mass gap. Every rigorous intermediate theorem is valuable, but the research must continually distinguish foundational progress from actual progress toward that target.