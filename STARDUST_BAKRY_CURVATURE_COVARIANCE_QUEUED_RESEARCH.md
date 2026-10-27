# Project Stardust — Bakry–Émery Objective 2
## Curvature–Covariance Correspondences Across Stochastic Processes

**Status:** ACTIVE — User-authorized transition on October27,2026 at fully locally audited checkpoint1601. Objective1 is deferred/incomplete, with all open obligations preserved. See the authoritative transition in STARDUST_CAMPAIGN_QUEUE.md. The former Objective1-completion prerequisite is superseded as scheduling only; workday private-backup deferral remains in force.

### Research objective

Investigate whether the fractional Brownian covariance representation of the fractional-Laplacian carré du champ, developed in the original Bakry–Émery manuscript, is a special case of a broader relationship between stochastic process covariance structures, Markov generators, and Bakry–Émery curvature.

The goal is to discover and formally verify reusable mathematical principles, not merely accumulate process-specific examples.

### 1. General Lévy-symbol correspondence

For symmetric Lévy generators with characteristic exponent \(\psi\), study the Fourier carré-du-champ kernel

\[
K_\psi(\xi,\eta)
=\frac{\psi(\xi)+\psi(\eta)-\psi(\xi+\eta)}2.
\]

Investigate:

- Necessary and sufficient conditions for positive-definite covariance interpretations, including frequency restrictions and sign conventions.
- Generalizations of the fractional Brownian covariance correspondence.
- Stable, Cauchy, relativistic stable, tempered stable, and subordinated Brownian generators.
- Bernstein-function representations and subordination.
- Connections with negative-definite kernels and Hilbert-space embeddings.
- Whether covariance representations yield new \(\Gamma_2\), curvature-dimension, Poincaré, or spectral-gap results.

Distinguish genuinely new results from established consequences of the Lévy–Khintchine and Schoenberg theories.

### 2. Gaussian and non-Markovian processes

Investigate corresponding operator and covariance structures for:

- Ornstein–Uhlenbeck processes.
- Fractional Brownian motion and Volterra Gaussian processes.
- Iterated Brownian motion and other stochastic time changes.
- Other Gaussian processes naturally supported by Stardust's existing library.

For non-Markovian processes, explicitly distinguish covariance-derived quadratic forms from genuine Bakry–Émery generators.

Consider Markovian lifts only when mathematically justified. Do not infer the existence of a Markov generator from covariance structure alone.

### 3. Higher-order heat pseudoprocesses

Investigate whether higher-order heat operators admit meaningful algebraic carré-du-champ and iterated carré-du-champ constructions.

Determine which identities survive without positivity-preserving Markov semigroups.

Distinguish algebraic \(\Gamma\)-calculus from probabilistic curvature-dimension inequalities. Investigate signed-kernel obstructions rather than imposing unjustified positivity assumptions.

Reuse the verified pseudoprocess machinery where applicable.

### 4. Noncommutative and gauge-theoretic connections

Explore possible extensions to compact Lie groups, beginning with \(SU(2)\).

Investigate:

- Representation-theoretic analogues of Fourier covariance kernels.
- Gauge-covariant derivatives and diffusion generators.
- Dirichlet forms, curvature inequalities, and spectral gaps.
- Whether relevant estimates survive gauge reduction or regularization.

Treat Yang–Mills as a long-term motivation, not an assumed consequence. Do not equate a finite-dimensional diffusion spectral gap with the four-dimensional quantum Yang–Mills mass gap.

### 5. Cross-campaign reuse

Audit the existing Stardust library for reusable Gaussian, Poisson, Lévy, fractional, closed-operator, integration-by-parts, semigroup, and convergence results.

Prefer extending verified foundations over duplicating constructions.

Record which mathematical tools transfer across campaigns and which require fundamentally new assumptions.

### 6. Research methodology

Maintain Stardust's established verification standards:

- Precise Lean theorem statements corresponding to the mathematical claims.
- Full builds, complete axiom audits, and independent checks at verified checkpoints.
- Explicit hypotheses and counterexamples.
- No `sorry` or unapproved axioms.
- Commit and preserve completed checkpoints through the established private backup process.
- Maintain a clear distinction between verified results, conjectures, open obligations, and literature-supported known mathematics.

Actively pursue unexpected mathematically valuable connections, but preserve the campaign's principal objectives.

### 7. Deliverables

Produce:

1. A formally verified general curvature–covariance theorem, if supported by the mathematics, or a precise explanation of why the proposed generalization fails.
2. Verified examples and counterexamples across distinct process families.
3. An assessment of which results provide genuinely new curvature or spectral information.
4. A reusable Lean infrastructure package for future campaigns.
5. A concise mathematical manuscript or research note with exact references to the verified Lean declarations.
6. A literature and novelty audit separating established theory from potentially original results.

### Priority and activation rules

**Activation:** The October27 user-authorized transition at checkpoint1601 supersedes the former Objective1-completion prerequisite. Objective2 is ACTIVE; Objective1 remains deferred/incomplete with all unfinished obligations preserved. See STARDUST_BAKRY_CURVATURE_COVARIANCE_AUDIT.md for current verified scope.

This objective remains within the Bakry–Émery campaign, before the separately queued Cauchy campaign.

IBM1562 remains frozen/incomplete. Do not reopen IBM or alter the remaining Stardust research queue.

If discoveries have implications for Cauchy, iterated pseudoprocesses, or Yang–Mills, document and queue those implications without prematurely redirecting the active research.

**Research philosophy:** Seek general mathematical structure connecting stochastic processes, operators, covariance, curvature, and spectral theory. Prefer transferable theorems over isolated calculations, and rigorous obstructions over unsupported generalizations.