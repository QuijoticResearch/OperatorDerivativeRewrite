# Paper 1 completion plan

Audit date: 2026-10-12. Inspected rewrite HEAD: `582ee395185c1a2a4d42654d9a3b6ac6f67853a9`.

**Recommendation: continue Paper 1 after a mathematical revision gate.** Preserve and prove the central deterministic-representer rigidity result. Repair the representation/domain architecture. Do not spend further proof effort on the current universal Itô or Gubinelli statements: explicit counterexamples prevent proving them as written. Do not start C7 or unrelated extensions.

This is a plan, not new formalization. Proposed module and theorem names below do not denote existing verified declarations. No manuscript, existing Lean source, pin, or pre-existing untracked document was edited; no commit or push was made.

Companion reports:

- [Complete claim inventory](C:/OperatorDerivativeRewrite/PAPER1_THEOREM_INVENTORY.md)
- [Exact Lean crosswalk](C:/OperatorDerivativeRewrite/PAPER1_LEAN_CROSSWALK.md)
- [Blocking obligations and counterexamples](C:/OperatorDerivativeRewrite/PAPER1_BLOCKING_OBLIGATIONS.md)

## 1. What counts as completion

There are two different acceptance levels. They must not be conflated.

**Mathematically defensible paper:** every retained theorem has a correct statement and proof, with precise references for external standard Brownian theory; every application satisfies its hypotheses; false claims have been explicitly revised with an explanation of the change. The paper may accurately state that some stochastic realizations are not yet in Lean.

**Fully Lean-verified central package:** in addition, the actual Brownian realization, weighted transport, stochastic-integral derivative, and rigidity conclusion are theorems about concrete objects in the pinned build, not abstract fields containing those conclusions. The original `EnergySpace` and `UnboundedEnergySpace` interfaces cannot serve as evidence because of their invalid L² operations and supplied closure assumptions.

The user should review the audit before either source revision or new formalization. This task performs neither. The plan identifies paper-critical obligations, so a subsequent implementation task can be narrowly scoped.

## 2. Preserve the central contribution and state the scope changes

The canonical manuscript is [C:\Operator\OperatorDerivative.tex](C:/Operator/OperatorDerivative.tex), title at line 40, with main results A–F at lines 91–150. Its abstract and novelty discussion make theorem E / `thm:obstr` central. `Banach.tex` is the companion, not Paper 1. C:\Operator has no Git history; no TeX version is tracked in the rewrite. Consequently the audit identifies the canonical available source, not a proven earliest historical edition.

Recommended disposition of the six main claims:

| Main claim | Minimal defensible disposition | What this preserves / changes |
|---|---|---|
| A: representation | Prove all-L² representation through the bounded adjoint J* of the predictable isometry; prove `J*F=Πδ*F` on the actual full-adjoint domain. | Preserves the operator-first identification and all-L² representation. Corrects the unbounded domain error. |
| B: cylindrical calculus | Use genuine derivatives and a finite-L⁴ core; prove Leibniz into dom D₂ by L⁴ graph approximation. | Preserves the core-to-closed-operator mechanism. Does not claim the entire D₂ domain or D^{1,4} is an algebra. |
| C: universal Itô | Explicitly revise after reviewing the bracket and projection counterexamples. Separate the valid divergence product rule from a properly scoped stochastic Itô theorem. | The current universal conclusion is not retained under unchanged hypotheses. A Brownian or carefully delimited Gaussian formula is a different statement and must be labeled so. |
| D: volatility transfer | Prove exact-domain unitary transport, then the valid D^{1,4} product theorem. | Preserves the intended extended derivative. Removes unnecessary inverse-moment assumptions and doubled probability variables. |
| E: rigidity | Prove terminal deterministic-gradient rigidity and derive the original cylinder formulation by cutoff. | Preserves the central contribution, with explicit natural Brownian filtration, a.e. conclusions and actual sensitivity. Avoids unnecessary cylinder graph-density assumptions. |
| F: Gubinelli rate | Withdraw the false statement as written and offer an explicitly different controlled-path result only if desired. | No silent claim of equivalence. The optional Taylor-controlled result for φ(B_t) is not the claimed theorem for conditional-expectation martingales. |

A defensible paper cannot leave C and F unchanged merely because the central E is repaired. Conversely, deleting E and publishing only standard Hilbert duality would not fulfill the intended central contribution. The proposed route keeps E.

## 3. Mathematical architecture to adopt

Let X be scalar terminal L² and K an integrand Hilbert space. Let P⊂K be a closed predictable subspace. Let `J:P→X` be the actual centered predictable stochastic-integral isometry. Let `δ:dom δ⊂K→X` be a dense closed extension of J when such an extension is available.

- The full operator derivative is `D=δ*`, with its exact domain.
- The bounded predictable representation operator is `R=J*`, defined on all X.
- `R F=P D F` for F∈dom D.
- `J R` is the orthogonal projection onto range J. PRP identifies that range with centered terminal L².
- Multiplication is an Lp operation with proved exponents and actual operator-domain membership, not a field on all L².
- A stochastic realization consists of a measure, processes, filtration, integration, domains, and identification proofs. Giving an abstract structure those desired properties is not a construction.

The weighted volatility realization uses `K_σ=L²(σ² dt dP)` directly. It does not use `L²(Ω;K_σ)`. Define `U_σu=σu`; strict positivity a.e. gives a unitary onto unweighted K by inverse v/σ. Neither boundedness nor integrability of 1/σ is needed because the inverse norm is weighted.

## 4. First implementation milestone — clean Hilbert representation

**Recommended next Sol Medium task, and only that task initially:** create a focused proposed module `C:\OperatorDerivativeRewrite\Foundation\HilbertRepresentation.lean` proving the representation architecture without either legacy energy interface.

### Exact mathematical target

Let X,K be real complete inner-product spaces, P a closed linear subspace of K, and J:P→ₗᵢ[ℝ]X a linear isometry. Regard J as a continuous linear map and define R=J*.

1. Prove `R(Ju)=u` for every u∈P.
2. Prove `J(RF)` is in range J and `F−J(RF)` is orthogonal to range J. Therefore `JR` is its orthogonal projection. Closedness of range J follows from completeness and isometry, not an extra assumption that restates the projection target.
3. For a partial operator δ:K→ₗ.[ℝ]X with dense domain, assume the genuine extension property `P⊂dom δ` and `δu=Ju` there. For every `F∈dom δ*`, prove `R F=P.orthogonalProjectionOnto(δ*F)`.
4. For a closed constants subspace C⊂X, if `range J=Cᗮ`, deduce `JRF=F−P_C F` and `‖F−P_C F‖²=‖RF‖²`. Specialize to scalar probability L² only after constructing its constants/expectation projection, or leave that small specialization for the next verified commit.

The extension and PRP hypotheses are ordinary input properties of a stochastic realization, not the desired adjoint identity. Their status must be explicit. Do not assume `RF=Pδ*F`, full-domain D, product closure, or the projection conclusion.

### Expected definitions and reusable APIs

Proposed names: `predictableAdjoint`, `predictableAdjoint_isometry_apply`, `representation_residual_orthogonal`, `predictableAdjoint_eq_projected_adjoint`, `representation_of_range_eq_orthogonal`, `representation_norm_identity`. Names may change during implementation; no current declaration is claimed under these names.

Pinned Mathlib reuse:

- `ContinuousLinearMap.adjoint` and `adjoint_inner_left`, in [Analysis/InnerProductSpace/Adjoint.lean](C:/OperatorDerivativeRewrite/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean).
- `LinearIsometry.adjoint_comp_self`, same file line 1068; `LinearIsometryEquiv.adjoint_eq_symm`, line 865.
- `Submodule.orthogonalProjectionOnto` and `Submodule.starProjection`, [Projection/Basic.lean](C:/OperatorDerivativeRewrite/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean):121,133; their membership and orthogonality APIs.
- `LinearPMap.adjoint_isFormalAdjoint`, already used in [Foundation/Adjoint.lean](C:/OperatorDerivativeRewrite/Foundation/Adjoint.lean):30–34.
- `mem_adjoint_domain_iff_representable`, [Foundation/OperatorDomains.lean](C:/OperatorDerivativeRewrite/Foundation/OperatorDomains.lean):23, if a representer proof is convenient.

Proof: compare inner products against every u∈P; isometry gives R∘J=Id, and adjointness identifies the residual. For the full-operator agreement, compare `⟨RF,u⟩=⟨F,Ju⟩=⟨δ*F,u⟩`. Projection uniqueness finishes it. This does not require a new probability, semigroup, rough-path, or stochastic-integral library.

### Acceptance criteria and risks

- Real Hilbert spaces only; no finite-dimensionality or nonzero-dimension assumptions.
- Full partial-operator domain arguments appear in the theorem types.
- No all-L² multiplication and no conclusion stored as a structure field.
- The all-X theorem uses R; the formula using δ* is restricted to dom δ*.
- Inspect fully elaborated types; full Lake build and transitive axiom audit pass; commit only this verified milestone after implementation is separately authorized.
- Main implementation risks are subtype/coercion bookkeeping and closed-range projection instances. These are Lean implementation issues, not unresolved mathematics.

This is the safest first step because it repairs foundational theorem A and prevents later stochastic realizations from conflating the two derivatives. It does not substitute for E.

## 5. Subsequent paper-critical milestones

### P1. Domain-exact unitary transport of unbounded adjoints

**Statement:** for real Hilbert spaces K₁,K₂,X, a unitary U:K₁≃ₗᵢK₂, and dense closed T:dom T⊂K₂→X, define T_U with domain U⁻¹(dom T) and value TU. Prove density and closedness, `dom T_U*=dom T*`, and `T_U*F=U⁻¹(T*F)`. Prove equality of actual partial operators, not only one inclusion or a pairing for known-domain elements.

**Expected file:** a small `Foundation/AdjointUnitaryTransport.lean`. Reuse `LinearPMap`, the actual adjoint domain characterization, and `LinearIsometryEquiv.adjoint_eq_symm`. Build the pullback domain explicitly if the pinned composition API is inconvenient.

**Proof:** transport every test vector in both directions using surjectivity. Norm preservation transports the bounded-functional criterion; the graph is carried by a product unitary, preserving closedness and density.

**Acceptance:** exact domains and values, no boundedness of T, no assumed desired adjoint identity. **Risk:** moderate Lean domain plumbing, straightforward mathematics. This directly supports D and E.

### P2. L⁴ graph closure and genuine Leibniz extension

**Statement:** for the existing closed Gaussian D₂, define the L⁴ graph closure of the genuine polynomial core (or a separately verified smooth core). If F_n→F and D₀F_n→V in L⁴, closedness in L² identifies F∈dom D₂ and D₂F=V. If F,G have such approximations, prove `FG∈dom D₂` and `D₂(FG)=F D₂G+G D₂F`, with every product in L².

**Reuse:** [InfiniteGaussianPolynomialProducts.lean](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianPolynomialProducts.lean):70,81,100; [LpProducts.lean](C:/OperatorDerivativeRewrite/Foundation/LpProducts.lean); `closed_graph_limit` at [OperatorDomains.lean](C:/OperatorDerivativeRewrite/Foundation/OperatorDomains.lean):40; existing closed Gaussian operator.

**Proof:** Hölder estimates on product differences plus boundedness of convergent derivative sequences. State product membership and identity separately. The target space is D₂, not an unjustified D⁴ algebra.

**Acceptance:** no assumed graph density outside the defined closure; no identification with a broader Sobolev domain unless independently proved. Explain precisely what definition of D^{1,4} the paper uses. **Risk:** moderate Lp equivalence-class/coercion work. This repairs the sound part of B and supports D.

Smooth chain calculus and full divergence multiplier rules are further separately testable steps if the revised paper retains the general equivalence theorem. The false global polynomial approximation at T687 cannot be used.

### P3. Concrete Brownian realization and the constant kernel

**Statement:** identify the existing canonical countable Gaussian model with an isonormal process over `L²([0,T])`; define `W_t=W(1_[0,t])`, prove its Brownian law/continuous modification and completed natural filtration, construct the predictable scalar/Hilbert Itô isometries, and identify their restriction with the full Gaussian divergence on the appropriate predictable domain. Establish `ker D^W=constants` on the terminal natural Brownian space.

**Reuse:** actual first chaos, arbitrary-direction polynomial cylinders, representation independence, Gaussian adjoints and graph cores; Mathlib's pinned Brownian, conditional-expectation, martingale and integration APIs should be inventoried at the start of that future task. Do not infer completeness of those stochastic APIs from the presence of Gaussian laws alone.

**Proof architecture:** unitary identification of separable deterministic Hilbert spaces transports the Gaussian derivative. Elementary predictable integrands give Itô integration by isometric completion. Derive compatibility from genuine Gaussian IBP/density. For the kernel, use the proved Gaussian spectral/projection framework or an independently proved Gaussian Poincaré/chaos argument. A constant-kernel theorem on a larger space with initial independent randomness is false.

**Acceptance:** actual measure/filtration/process, predictable-domain inclusion, and adjoint agreement. No “Brownian integration” field containing the needed statements. **Risk:** this is the largest formalization obligation. On-paper use of established Brownian theorems is legitimate with exact citations, but must be labeled unformalized until this milestone passes.

### P4. Weighted volatility transport

**Statement:** for measurable σ>0 dt dP-a.e., prove the unitary `U_σ:L²(σ²dt dP)≃L²(dt dP)` by multiplication. Define δ_M by the actual pullback domain and use P1 to derive `D_M=U_σ⁻¹D^W` with exact domain. For predictable square-integrable σ, identify M=∫σdW and agreement with its weighted predictable integral. Transport P2's Leibniz rule with proved weighted product integrability.

**Proof:** norm equality and measurable inverse v/σ, defined arbitrarily on the null zero set. The norm identity establishes inverse integrability, rather than imposing `1/σ∈L²`. For products, weighted norms cancel σ and reduce to the verified Gaussian Hölder estimates.

**Acceptance:** no duplicated Ω, no bounded inverse assumption, no assumed transfer formula. **Risk:** measure-with-density and equivalence-class transport. This is genuine analytic bookkeeping, with a clear true target.

The paper's blanket natural-X-filtration convention also needs reconciliation here. Either state that this realization uses the completed natural Brownian filtration, or prove equality with the natural M-filtration using strict positivity, quadratic-variation density and recovery of W from M. Do not silently change filtrations in a conditional-expectation identity.

### P5. Differentiate the actual adapted Itô integral

**Statement:** on the completed natural Brownian filtration, for predictable `σ∈L²([0,T];D^{1,2})`, prove M_T∈D^{1,2} and, in `L²(Ω;L²[0,T])`,

`D^W M_T = σ + ∫₀ᵀ D^Wσ_s dW_s`.

The right-hand integral is a genuine Hilbert-valued Itô integral. Prove its predictable version, integrability, centering, and Hilbert Itô isometry from the stated Sobolev process hypotheses. A sectionwise tail formula may be derived afterward; it is not needed for terminal rigidity.

**Proof strategy:** begin with adapted smooth elementary processes, where Gaussian differentiation is genuine. Establish approximation in `L²(dt;D^{1,2})`, preserving adaptation. Then use scalar and Hilbert Itô isometries and closedness of D. Conditional-expectation commutation and predictable versions are supporting theorems, not assumed density conclusions.

**Acceptance:** actual derivatives and stochastic integrals, the same approximants for values/derivatives, no arbitrary derivative data or assumed sensitivity formula, all assertions in the correct a.e. spaces. **Risk:** substantial stochastic/Malliavin approximation; list the exact remaining lemma if incomplete. Do not call this a small algebraic wrapper.

### P6. Terminal deterministic-gradient rigidity and cylinder corollary

**Statement:** with P4–P5 hypotheses, σ>0 a.e., and measurable deterministic k representing `D_M M_T` in K_σ, prove σ equals a deterministic measurable function dt dP-a.e. No inverse moment, boundedness, continuity, or fourth-moment hypothesis on σ is added.

**Proof:** write `D^W M_T=σ+I` using P5. The deterministic-gradient assumption gives `I=(k−1)σ`. Bochner centering and Fubini give `(k(r)−1)Eσ_r=0` for a.e. r; strict positivity and integrability imply k=1. The Hilbert Itô isometry forces `D^Wσ=0`; P3's kernel theorem gives `σ_s=Eσ_s` for a.e. s. This avoids a separate stochastic-Fubini proof for time sections.

**Cylinder corollary:** if the terminal coordinate is included and genuine bounded smooth cylindrical IBP has deterministic terminal representer k∈K_σ, choose `φ_R(x)=Rφ(x/R)` for compact smooth φ equal to id near zero. Then `φ_R(M_T)→M_T` in scalar L² and `φ'_R(M_T)k→k` in K_σ. Closedness identifies `D_M M_T=k`. Apply terminal rigidity. No full cylinder graph-density assumption is used.

**Acceptance:** ordinary determinism expressed by a deterministic measurable representative; no `RepresentersDeterministic` factorization against random test fields; no false `hcancel`; conclusions a.e. unless a version theorem is separately proved. **Risk:** relatively small after P3–P5, but those dependencies are essential. This is the paper-critical endpoint.

## 6. Repairs that need an explicit author decision

These are proposed edits only; original sources remain unchanged.

1. Rewrite the notation once around abstract K and predictable P. Correct every doubled L²(Ω;K_σ) occurrence. Distinguish δ, J, D and J* in the examples and classification table.
2. Split A into the all-L² bounded representation and its full-derivative agreement on dom D. Include the exact terminal sigma-algebra.
3. Replace the invalid “Leibniz ⇔ smooth chain ⇔ divergence product” proof by separate theorems with explicit product domains and graph cores. A closedness argument cannot manufacture an unproved approximation theorem.
4. Preserve E using P6. Add a cutoff proof rather than claiming id∈C_b^∞. Remove unsupported full M-cylinder graph density from its dependencies, while marking that density question open.
5. Correct the Gaussian bracket normalization. Do not identify variance derivative with the covariance diagonal. Replace the claimed general Itô section only after choosing actual stochastic hypotheses and the correct divergence domain; bounded linear-map Fubini alone is insufficient.
6. State explicitly that current F is false. A Taylor-controlled result for φ(B_t) is an optional alternative theorem, not the original conclusion in new notation.
7. Correct all-H fBM assertions where canonical versus extended divergence matters, and correct reference theorem numbers and hypotheses. Do not describe general rough-path/regularity-structure limitations as merely notation.
8. Add actual moment assumptions where using M_T², or choose bounded smooth test functions. State dt-a.e. deterministic volatility. Qualify SDE examples individually.
9. Replace the formalization section with the actual crosswalk: canonical Gaussian and one-site Poisson foundations are verified; Brownian/fBM/time-dependent claims are not. The exact Gaussian LSI adapter does not prove abstract Bakry–Émery curvature theory.

The operator-first viewpoint is a useful organizational and formalization architecture. Standard adjoint existence, Hilbert projection, and known Gaussian calculus are not new mathematics by a change of presentation. Assess novelty of the corrected rigidity theorem against the literature before making a priority claim; this audit establishes neither priority nor a literature-exhaustive novelty verdict.

## 7. What not to put on the critical path

- Full graph density of smooth M-cylinders: no longer needed for the terminal/cylinder rigidity implication.
- A general abstract semigroup/curvature theory: unrelated to the actual Paper 1 rigidity gap.
- Further Banach C7 or Poisson P extensions: preserve existing verified results, but do not expand them for this task.
- Uniform all-H fBM integration or a general rough-path library: much larger than the corrected central claim and currently based on false formulas.
- Automatic replacement of the original full file: its abstract interface and concrete failures need a deliberate integration strategy. The verified rewrite should remain intact.
- Deleting hard statements without recording the scope change, or declaring all conditional legacy proofs to be concrete stochastic theorems.

## 8. Verification and release gates

For each future implementation milestone: inspect elaborated theorem types and all imported hypotheses; compile the focused module; add its real results to the root imports and axiom audit; run the full pinned Lake build; audit transitive axioms; document exact scope and missing obligations; commit only verified work, with no push unless requested. An admission-free proof from a false realization assumption is not an acceptable milestone.

Current baseline, independently rerun during this audit:

| Check | Result |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.34.1` |
| Mathlib pin | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Full rewrite `lake build` | PASS, 4,030 jobs |
| `Foundation/AxiomAudit.lean` | PASS; 1,213 declarations; union `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| `Legacy/GaussianLogSobolevSection.lean` | PASS; does not validate its hypotheses as stochastic realizations |
| Original full `C:\Operator\OperatorDerivative.lean` | FAIL at lines 3156,3272,3300,3609,3630,3696,4456 |
| Original manuscripts / existing Lean / pins | Unchanged by this audit |
| New formalization / commit / push | None |

The narrowest safe next implementation is **Section 4's clean Hilbert representation module**. After review, proceed through exact unitary transport toward genuine Brownian terminal rigidity. Full Paper 1 completion requires the explicit mathematical revisions in Section 6, not just a green build.

## Implementation update — 2026-10-12

The audit-time plan above is preserved. Seven separately verified commits now end at
`30d3140f569cb7afc642e220a247949f052ae02f`:

| Commit | Completed scope |
|---|---|
| `4c4d86c` | Section 4 abstract Hilbert representation and natural adjoint domains |
| `efce58c` | P1 exact unitary transport, including both adjoint-domain directions |
| `3cf1aec` | P3 constant-kernel ingredient on the actual finite/countable Gaussian models |
| `15dc785` | P4 full weighted L2 unitary and actual adjoint transport |
| `b019dc1` | P4 restriction to actual measurable subspaces |
| `71e47aa` | Actual random elementary Gaussian integral, isometry and infinite-product compatibility |
| `30d3140` | Actual finite Gaussian sensitivity and discrete polynomial rigidity |

The finite rigidity theorem is **not completion of P5/P6**. Those still need a Brownian-time realization, predictable integration/completion and justified sensitivity limits. P2's full L4 graph-closure extension was not undertaken. The manuscript's false bracket/Gubinelli formulas remain unresolved scope decisions, not compilation problems.

Next smallest implementation: construct an actual isonormal realization over
`Lp ℝ 2 (volume.restrict (Icc 0 T))` using a proved coordinate embedding into the
existing coefficient Hilbert space. Define the time coordinates from interval
indicators and prove their covariance and independent increments. Do not assume
an unconstructed Hilbert-basis identification; do not call this deterministic
Wiener realization a predictable random stochastic integral. Continuous paths,
partition refinement, predictable completion and adapted graph approximation
remain explicit later obligations.

Full build: 4039 jobs. Transitive audit: 1323 listed declarations, including all
110 new public declarations, standard axioms only. Original sources, existing
Lean proof bodies and dependency pins are preserved. Nothing was pushed.
