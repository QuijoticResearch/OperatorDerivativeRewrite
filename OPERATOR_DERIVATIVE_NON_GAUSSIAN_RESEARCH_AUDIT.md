# Independent research audit: operator derivatives beyond the Gaussian setting

Research review: 11 October 2026. Repository inspected at **1972449856bc31ceadf00e22b0a308cf5e87be92** (commit timestamp 2026-10-11T16:12:10-04:00). Pinned Lean: **4.34.1**; Mathlib: **d13f23b723b8a846827a245b89c10fc7d3f11612**.

This is a mathematical investigation and a source review, not a new Lean verification milestone. Statements proved mathematically below have **not** thereby been formalized. No Lean source, manuscript, dependency pin, or existing audit was changed. No build was required or rerun for this document, and no commit was created. Earlier build/axiom results are historical evidence, not a substitute for this review of statement meanings. External source snapshots were inspected; their projects were not compiled locally. Remote current commit dates could not be reliably resolved, so mutable `main`/`master` links below must not be mistaken for pinned compatibility guarantees.

## 1. Executive assessment

**Recommendation: continue, with a concrete non-Gaussian operator milestone and substantially narrower research claims.**

The durable idea is to distinguish an integration operator, its adjoint, the operator domains, and additional calculus rules. This is useful mathematical organization and useful formal-library architecture. It is not by itself a new stochastic calculus: stochastic derivatives defined as adjoints of stochastic integrals, including derivatives on all of L², predate this manuscript. Di Nunno–Rozanov explicitly treat the nonanticipating adjoint and the anticipating derivative/divergence separately; see §4.1 and §5.2 of [Stochastic Integrals and Adjoint Derivatives](https://abelsymposium.no/symp2005/preprints/dinunno.pdf).

The new verified Gaussian development is valuable as formalization of known mathematics: actual cylindrical derivatives, representation independence, closures, full adjoint identification, graph cores, and genuine Gaussian log-Sobolev integrability. Those achievements do not validate the legacy interfaces or their non-Gaussian instances.

The original manuscript contains both repairable conditional arguments and false assertions. In particular, adjointness alone does not imply representation, arbitrary adjoints are not derivations, a closed derivative domain need not be an algebra, and a predictable representation integrand is not the terminal Malliavin derivative. The stated universal Itô/bracket and Gubinelli identifications have explicit counterexamples. Some legacy Lean structures assume the very analytic facts that their surrounding prose says were constructed; others encode impossible conditions in intended probability models.

There is genuine scope beyond a Gaussian probability law:

- Ordinary differential derivations and adjoints on non-Gaussian weighted measures and local diffusions.
- Difference derivatives and divergences on Poisson spaces, with a different product rule.
- Predictable integral adjoints for square-integrable martingales, subject to a separately established range theorem.
- Weighted transport of Brownian Malliavin operators to stochastic-volatility energy spaces, including volatility with memory.

These are established mathematical territories. No new general theorem stronger than known Malliavin, Stein, Dirichlet-form, or martingale-representation theory was established by this investigation. A quantitative stochastic-volatility representer defect is a promising formulation to investigate, but its novelty has not been established.

**Single recommended first target:** a concrete one-site Poisson difference/divergence pair, with maximal domains and proved finite-support graph cores. Start with its finite-support integration-by-parts identity. This tests the architecture against genuinely non-Gaussian noise, requires no Brownian stochastic-integral library, and remains valuable even if every stronger manuscript conjecture fails.

## 2. What the original files actually establish

Locations below refer to the untouched [original Lean file](C:/Operator/OperatorDerivative.lean) and [original manuscript](C:/Operator/OperatorDerivative.tex), not the later integration copy. A Lean theorem under assumptions establishes the implication; it does not construct an instance satisfying the assumptions.

Classification: **A** = valid mathematical result; **B** = conditional result requiring substantive hypotheses; **C** = conclusion or essential analytic ingredient assumed in an interface; **D** = false, mismatched, or insufficiently justified; **E** = potentially useful corrected research claim requiring further work.

| Item and exact source location | Assessment |
|---|---|
| `operatorDerivative_isClosed`, Lean:68; `operatorDerivative_adjoint_identity`, Lean:76; TeX:244–304 | **A.** Standard adjoint theory, with dense divergence domain. Defining an adjoint does not identify a concrete differential operator. |
| `clark_ocone_unbounded`, Lean:226; `gkw_orthogonality_unbounded`, Lean:289 | **B.** Domain membership and representation/projection data are inputs. The algebraic implications survive; construction of a stochastic integral and proof of its range do not follow. |
| All-L² factorization in TeX:91–98, 327–408 | **D as phrased for an unbounded adjoint.** Restrict to `dom(δ*)`, or use the different, bounded adjoint of the predictable integral on all L². |
| `UnboundedEnergySpace`, Lean:101, total `mul` at136, product-domain field at154–156; bounded `EnergySpace`, Lean:735/748 | **C/D.** These interfaces grant multiplication or closure beyond genuine L² facts. L²×L² maps to L¹, not generally L². |
| `UnboundedCylindricalStructure`, Lean:341; `leibniz_closure`, Lean:366 | **C.** Extension of Leibniz through graph limits is assumed as a field, not obtained from closedness alone. |
| `UnboundedSmoothFunc`, Lean:484; `ito_from_leibniz_alone`, Lean:2207–2216 | **C/B.** The latter still accepts `hChain_derived : E.D φ'Y = E.smul φ''Y (E.D Y)`. Naming it “derived” does not prove it. |
| `operator_ito_decomposition_unbounded`, Lean:520; `ito_formula_with_clark_ocone`, Lean:2046; time-indexed version at2118 | **B/D.** Algebraic divergence/product identities under additional assumptions are not a time-dependent Itô theorem. The projection/multiplication compatibility is a substantial and generally false extra assumption. |
| `UnboundedStochVolAssumption`, Lean:546–556; theorem at560 | **C/B.** Brownian transfer and Brownian Leibniz are assumed. There is a valid concrete weighted construction, explained below, but this declaration does not construct it. |
| `RepresentersDeterministic`, Lean:1496–1499; `representer_rigidity`, Lean:1515 | **D.** The definition factors an expectation for every random test vector, which is stronger than deterministic representers and false even for a nonzero deterministic representer. The theorem merely propagates that factorization. |
| `deterministic_variance_bound`, Lean:1537–1548 | **D as a description.** Its conclusion is another pairing factorization, not the advertised variance bound. |
| `stoch_vol_obstruction`, Lean:1590–1606 | **D as a concrete obstruction proof.** It assumes `hcancel`: a nonconstant factor times another factor being constant forces the second factor to vanish. This is false. |
| `ConcreteStochasticIntegral`, Lean:2775–2777 | **C/D.** Full-domain isometry is not the Skorokhod isometry. Anticipating integrands give counterexamples. |
| `CylindricalFunctional`, Lean:2939–2960 | **D.** `f_eval` and `df_eval` are independent data; there is no actual differentiation condition. A zero value with nonzero alleged derivative is permitted. Orthonormalizing a dependent family also changes its dimension; the “WLOG” comment is not a proof. |
| `SteinLemma`, Lean:3903–3908; `steinFromGaussian`, Lean:4155–4171 | **C/D.** Stein for every such fake cylinder is inconsistent in a nontrivial intended Gaussian model. `per_coord_stein` is supplied by a class field, not derived from actual derivatives. |
| `concrete_mul`, Lean:3274 | **A in its restricted scope.** The L⁴×L⁴→L² construction is mathematically appropriate; it does not supply total L² multiplication. |
| `brownianEnergySpace`, Lean:3475–3477 | **C/D.** The impossible total pointwise multiplication requirement is still an input. It is not a complete Brownian model discharging every interface obligation. |
| `SimpleProcess.toLp`, `simple_process_inner`, Lean:4550–4569 | **A in scope.** A finite tensor/inner-product calculation, not construction of the adapted Itô integral or PRP. |
| `cylindrical_chain_rule`, Lean:4920 | **D as evidence of differentiation.** An unfolding identity for prescribed data does not relate those data to the derivative of the underlying smooth function. |
| `logSobolevTensor`, Lean:2381–2390; Sobolev item at2429–2436 | **D as substantive claims.** Conclusions `True` are not the named analytic inequalities. |
| `complete_stochastic_calculus`, Lean:5132 | **B/D.** Packages conditional algebraic facts; it does not establish the advertised full stochastic calculus. |

The later rewrite has genuinely repaired important Gaussian items. Examples include `polynomialDerivative_on_cylinder` in [InfiniteGaussianDerivative.lean:180](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianDerivative.lean:180), `cylindricalField_integration_by_parts` in [InfiniteGaussianOperators.lean:215](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:215), and `cylindricalDivergence_adjoint_eq_closedDerivative`, `closedPolynomialDivergence_eq_hilbertDivergence`, `hilbertDivergence_polynomial_graph_core_sequence` in [InfiniteGaussianProjectionConvergence.lean:313](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:313). The full one-dimensional inequality is `gaussian_logSobolev_of_hasDerivAt` in [GaussianLogSobolevFull.lean:231](C:/OperatorDerivativeRewrite/Foundation/GaussianLogSobolevFull.lean:231).

At current HEAD, [Legacy/README.md](C:/OperatorDerivativeRewrite/Legacy/README.md) records the verified Gaussian axiom adapter and seven unrelated full-legacy compilation errors. The original claim that the entire legacy framework compiles and supplies concrete stochastic models (TeX:178–180, 1440–1444) must not be retained as a description of what is now verified. Replacing the Gaussian axiom does not prove abstract Bakry–Émery, tensorization, the non-Gaussian interfaces, or the original Itô claims.

## 3. Correct framework: assumptions and consequences

### 3.1 Closed operators and integration by parts

Let S=L²(P) and let K be a real Hilbert space. K may be L²(P;H) for a fixed Hilbert fiber H; a random-weight integrand space should instead be defined directly as an L² space over its weighted measure.

Start with a densely defined, closable linear operator δ₀:K⇀S. Set δ=closure(δ₀), and D=δ₀*=δ*. Then D is closed and densely defined, D*=δ, and

`E[F δu] = <DF,u>_K`, for F∈dom(D), u∈dom(δ).

These conclusions are general Hilbert-space theory. If only `D=δ₀*` is defined, its adjoint is closure(δ₀), not necessarily δ₀. A formal adjoint identity on test cores proves inclusions and closability; full adjoint equality requires a maximal-domain or graph-core argument.

Centeredness `E[δu]=0` for every u∈dom(δ) implies 1∈dom(D) and D1=0. No multiplication, chain rule, filtration, probability distribution, or stochastic representation follows. For example, δ=0 satisfies the basic centered adjoint conditions but represents no nonzero centered variable.

If one builds the energy form `E(F,G)=<DF,DG>`, it is closed when D is closed. To call it a Dirichlet form additionally requires the Markov/contraction property. To use ordinary diffusion chain rules requires locality and appropriate domain calculus. These do not follow from being an arbitrary closed operator. Conversely, non-Gaussian Dirichlet forms already provide many genuine derivations. An observed process being non-Markovian does not exclude Dirichlet forms on its path probability space; the Markov process associated to a form is a different object.

### 3.2 Product and chain rules

An algebraic core A must consist of actual functions/classes with justified products. On it, prove D(FG)=F DG+G DF and actual composition rules. Extend only through estimates strong enough to control the graph:

- L²×L²→L¹ and `<U,V>`∈L¹ for U,V∈L²(P;H).
- L⁴×L⁴→L², and the same Hölder control for scalar-vector products and vector inner products.
- L∞×L²→L².
- A derivative in L² does not make dom(D) an algebra. D¹,⁴×D¹,⁴→D¹,² is a standard sufficient Gaussian condition, not an assertion about every closed operator.

Even on one Gaussian coordinate, f(x)=exp(x²/8) has f,f'∈L²(γ), while f²∉L²(γ). Thus the Gaussian D¹,² domain itself is not multiplicatively closed. “D¹,⁴ = D¹,²∩L⁴” in TeX:738 is also not a general identity; derivative L⁴ control is an additional requirement.

A bounded L²→L²(P;H) operator that obeys ordinary Leibniz on all bounded measurable functions must be zero: for any indicator A, D1_A=2·1_A D1_A, hence D1_A=0; use simple-function density and boundedness. This sharply limits attempts to combine all-L² boundedness and unrestricted terminal-variable Leibniz.

### 3.3 The predictable representation operator is different

Let Kp⊂K be a closed Hilbert subspace, j:Kp→K its inclusion, and assume j(Kp)⊂dom(δ). Suppose the actual restriction I=δj is an isometry Kp→S. Then I* exists on **all** S, and

`II* = orthogonal projection onto ran(I)`,

`I*F = j*DF` for F∈dom(D).

Proof: the isometric range is closed, I*I=id, and testing against v∈Kp gives `<I*F,v>=<DF,jv>`. These are consequences, not representation identities built into definitions.

To obtain `F-EF=II*F` for every F requires the separate range statement `ran(I)=L²₀(P)`. Isometry does not establish that statement. Under a nontrivial initial σ-algebra the natural target is instead `F-E[F|F₀]`; constants alone do not account for initial randomness. A filtration with an independent orthogonal martingale can prevent PRP for the selected integrator.

Conditional expectation provides orthogonal projections in L². It does not identify those projections with a particular stochastic integral or derivative. Construction of predictable processes, their closed subspace, joint measurability, and the a.e. meaning of `E[D_tF|F_t]` remain necessary.

For Brownian motion, the terminal derivative is DW(W_T)=1 and DW(W_T²)=2W_T. The predictable adjoint R=I* instead has R(W_T)=1 and R(W_T²)_t=2W_t. They agree only after the appropriate projection on the derivative domain. Confusing these operators is the source of several original overclaims (notably TeX:1245).

For a bounded integral that is not isometric, II* is generally not an orthogonal projection. A closed-range hypothesis permits a generalized inverse involving I*I, but the simple manuscript factorization then changes.
## 4. Chain rules, Stein kernels, and the precise Gaussian boundary

### 4.1 A valid Gaussian rigidity theorem

**Scalar theorem.** Let D:S⇀L²(P;H) and δ=D* have dense domains. Suppose 1,X∈dom(D), D1=0, u∈dom(δ), δu=X, and X∈L²(P). Suppose for every real t both sin(tX) and cos(tX) belong to dom(D) and satisfy their actual chain rules. Set A=<DX,u>_H, which is integrable by Cauchy–Schwarz. If

`E[A | X] = c` a.s., with c a deterministic real number,

then c=E[X²]≥0 and X has the centered Gaussian law of variance c, including the degenerate c=0 case.

**Proof.** Testing adjointness with 1 and X gives EX=0 and E[X²]=EA=c. Chain and adjointness for the trigonometric tests give, for the characteristic function ψ(t)=E[exp(itX)],

`ψ'(t)=i E[X exp(itX)]=−ct ψ(t)`.

The characteristic-function derivative is justified by X∈L¹; the IBP products by L² and bounded trigonometric derivatives. Solve this ordinary scalar ODE with ψ(0)=1 to obtain ψ(t)=exp(−ct²/2), then use uniqueness of characteristic functions. The complex notation abbreviates two real tests and introduces no complex-derivative assumption.

A deterministic h∈H is allowed by taking u(ω)=h, provided this constant field actually belongs to dom(δ) and δh=X. The pointwise condition `<DX,h>=c` is stronger than needed; conditional constancy is enough. The chain rule alone, a deterministic DX alone, or centered adjointness alone is insufficient.

**Vector theorem.** Let X₁,…,X_d∈dom(D), u_i∈dom(δ), δu_i=X_i; require the genuine multivariate chain rule for sin(t·X), cos(t·X). If

`E[<DX_j,u_i> | X] = C_ij` for all i,j,

with deterministic C, then C_ij=E[X_i X_j], so C is symmetric positive semidefinite, and X is Gaussian with covariance C, allowing linear dependence. The proof is `∂_i ψ(t)=−Σ_j C_ij t_j ψ(t)` followed by its radial ODE. Only the tested family is Gaussian: one can enlarge the probability space by an independent Bernoulli variable.

An even weaker sufficient vector hypothesis is directional: for every a∈R^d, require

`E[<D(a·X), Σ_i a_i u_i> | a·X] = aᵀCa`.

The scalar theorem and Cramér–Wold then suffice. There is no claim here of an absolute “weakest hypothesis” across all possible test classes; these are explicit distribution-determining conditions, weaker than deterministic raw pairings.

This is classical Stein characterization expressed through adjoints. Compare [Nourdin–Peccati–Réveillac, Lemma 3.3](https://arxiv.org/pdf/0804.1889) and [Nourdin–Viens, Corollary 3.3](https://arxiv.org/pdf/0808.2088). The singular-covariance extension in the argument above needs no invertibility. It is not a newly discovered rigidity principle.

### 4.2 What a random pairing actually says

Under the scalar chain/adjoint assumptions, for every admissible smooth φ,

`E[X φ(X)] = E[τ(X) φ'(X)]`, where `τ(X)=E[A|X]`.

This is a Stein kernel identity. It does **not** say that every random pairing produces a non-Gaussian law; a nonconstant raw pairing can have constant conditional expectation and produce a Gaussian law. For independent standard Gaussians G₁,G₂, take X=G₁ and the ordinary two-dimensional Gaussian derivative with u=(1+G₂,−G₁). Then δu=G₁, A=1+G₂ is sometimes negative, but E[A|X]=1.

There is a useful scalar positivity refinement. If the identity holds for all compactly supported smooth tests, X is centered with finite variance, and τ is integrable, then τ≥0 almost surely. Indeed, writing μ=law(X), the finite signed measure ν=τμ satisfies ν'=−xμ in distributions. The finite nonnegative measure k(t)dt, with `k(t)=E[X 1_{X>t}]`, has the same derivative; k≥0 follows from centering, and its integral is E[X²]. Their difference has zero distributional derivative and is a finite multiple of Lebesgue measure, hence is zero. Thus τμ=k(t)dt. Strict positivity and analogous matrix positivity require extra arguments; raw Hilbert pairings need not be positive. Compare the conditional-pairing analysis in [Nourdin–Peccati, Proposition 3.9](https://arxiv.org/pdf/0712.2940).

Consequently, the meaningful Gaussian obstruction is **constant conditional Stein pairing together with genuine differential chain and adjoint identities**. “Deterministic representers” without specifying the metric, divergence, and coordinate law is not an equivalent condition. In a randomly weighted energy space, even a deterministic coordinate formula need not yield a deterministic pointwise energy pairing.

## 5. Explicit test cases

### 5.1 Non-Gaussian differential IBP on the real line

Let μ(dx)=Z⁻¹exp(−x⁴/4)dx and Q(x)=x. On C_c^∞ define D₀f=f'. Its closure in L²(μ) is the weighted weak derivative. Its adjoint is

`δu=−u'+x³u`,

with the maximal distributional domain consisting of u∈L²(μ) for which the displayed expression belongs to L²(μ). Distributional integration by parts against compactly supported tests gives this domain; ordinary smooth cutoff and local mollification give the derivative core. The weight is positive and smooth and equivalent to Lebesgue measure on each compact interval.

Thus actual chain and product rules hold on the smooth core and extend with the usual integrability restrictions. In particular 1∈dom(δ), δ1=Q³, and DQ=1. It is **not** true that δ1=Q. All polynomial integrability and boundary terms follow from the quartic tail.

Taking X=Q³ yields δ1=X and DX=3Q². Its Stein pairing is random: τ(X)=3|X|^(2/3). This supplies a genuine non-Gaussian differential/adjoint model and isolates the missing constant-pairing hypothesis. It is standard weighted Sobolev/Stein theory, not a new calculus. A static probability model supplies IBP; it does not itself supply a time filtration or PRP.

Lean feasibility: local weighted-measure comparison, actual integration by parts, compact cutoffs, then dense cores and adjoints. The project’s adjoint lemmas are reusable; the Gaussian spectral basis is not. For the first non-Gaussian derivation, the compact-interval alternative below has fewer tail obligations.

### 5.2 A non-Gaussian invariant diffusion

Let μ be uniform probability on [−1,1]. On smooth functions set

`Df(x)=sqrt(1−x²) f'(x)`,

`L f(x)=((1−x²)f'(x))'=(1−x²)f''(x)−2x f'(x)`.

The closed gradient is obtained from the closure of this smooth core. Its divergence adjoint has weak expression `δu=−(sqrt(1−x²)u)'`; the domain is the corresponding L² weak-derivative condition with zero boundary flux for sqrt(1−x²)u. Integration by parts gives L=−δD on its smooth generator core, symmetry, and invariance of μ. Ordinary diffusion chain rules hold. This is the Jacobi/Legendre diffusion, classically represented by `dX_t=−2X_t dt+sqrt(2(1−X_t²))dB_t` with its invariant uniform law; constructing that process is an extra step beyond the static operator calculation.

For X(x)=x and u(x)=sqrt(1−x²)/2, δu=X while `<DX,u>=(1−X²)/2`. The random Stein kernel is essential. This is a non-Gaussian invariant law with an ordinary chain rule, although its driving Brownian noise is Gaussian. Those are distinct generalizations. [Ledoux–Nourdin–Peccati, §4.3 and Proposition 5.1](https://arxiv.org/pdf/1403.5855) place beta/Jacobi examples and eigenfunction Stein kernels within known diffusion theory.

For a particularly short formal static example, instead use the unweighted derivative Df=f' on the same interval. Then dom(D)=H¹([−1,1]) and δu=−u' with dom(δ)=H¹₀([−1,1]). The boundary restrictions are indispensable: 1 is not in dom(δ). With τ(x)=(1−x²)/2, δτ=x and

`∫ x φ(x) dμ = ∫ τ(x) φ'(x) dμ`.

This valid identity explains why DX=1 does not force Gaussianity on an interval. A process representation theorem, if desired, would still need its own filtration and integral.

### 5.3 Brownian digital payoff: nonsmooth payoff, not non-Gaussian noise

On canonical Brownian space, fix T>0 and finite K. Let F=1_{W_T>K}, p=P(W_T>K). For 0≤t<T,

`M_t=E[F|F_t]=Φ((W_t−K)/sqrt(T−t))`,

`H_t=exp(−(W_t−K)²/(2(T−t)))/sqrt(2π(T−t))`.

The heat equation and Itô’s formula on [0,T−ε] give dM_t=H_t dW_t. Bounded martingale convergence and Itô isometry yield

`F=p+∫₀ᵀ H_t dW_t`, and `E∫₀ᵀ H_t²dt=p(1−p)`.

The endpoint value of H_T is irrelevant. On every t<T the quadratic-covariation derivative `d<M,W>_t/dt` equals H_t. This is an actual predictable integrand on an L² domain, not a claimed derivative of F in D¹,².

Indeed F∉D¹,². Were it in that space, apply a smooth bounded-derivative function agreeing with x² near {0,1}: F²=F would imply DF=2FDF and hence DF=0. The canonical Wiener zero-gradient theorem would force F constant, contradicting 0<p<1. The distinction is already explicit in [Allouba–Fontes (2011), Theorem 1.1 and §3.1–3.2](https://arxiv.org/pdf/1011.1475), including this indicator and digital-option application. This is particularly direct prior art, coauthored by the manuscript’s author, not a new example enabled for the first time by this framework.

The relevant operator is R=I* on all scalar L² with I the predictable Itô isometry. As a bounded operator R*=I. It does not obey the ordinary terminal-variable chain rule. Formalizing the example would be useful but requires an actual Brownian integral, Itô formula, and martingale convergence infrastructure beyond the present Gaussian product-space operator foundation.

### 5.4 One-site Poisson: genuinely non-Gaussian noise

Fix λ>0 and μ_n=exp(−λ)λⁿ/n!. Set S=L²(μ), K=L²(λμ). Identify representatives pointwise, since every atom has positive mass. Define

`Df(n)=f(n+1)−f(n)`,

`δu(n)=n u(n−1)−λu(n)`, with the first term zero at n=0.

The exact maximal domains are

`dom(D)={f∈S : Σ n μ_n |f(n)|² < ∞}`,

`dom(δ)={u∈K : Σ (n+1) μ_n |u(n)|² < ∞}`.

These are closed densely defined mutual adjoints. Finite-support sequences form graph cores for both. A complete short proof and formalization plan appear in §9–10. In particular

`λ E[(Df)(N) u(N)] = E[f(N) δu(N)]`.

The product rule is

`D(fg)=f Dg+g Df+(Df)(Dg)`.

On finite-support functions every term is genuinely integrable; extension requires additional domain/product estimates. With X=N−λ, δ1=X and DX=1, but `D(X²)=2X+1`, not 2X. In the weighted energy metric the pairing with the unit field is the deterministic λ. Thus even an adjoint representation and constant derivative pairing do not force Gaussianity when the **ordinary differential chain rule is missing**.

The exact composition rule is the finite difference `Dφ(f)=φ(f+Df)−φ(f)`. This is the classical Poisson calculus, not a pathological failure. See [Peccati–Solé–Taqqu–Utzet, Lemma 2.7, Remark 2.8(4), and Lemma 2.9](https://arxiv.org/pdf/0807.5035). A single Poisson count has no time filtration. Poisson-process predictable representation and Poisson-random-measure divergence require a later construction, not a claim attached to this static example.

### 5.5 Memory and stochastic volatility: a credible surviving extension

Work on canonical Brownian space with its augmented natural filtration, and let σ be a jointly measurable predictable process, positive and finite a.e., with E∫₀ᵀσ²dt<∞. Define directly

`Kσ=L²(Ω×[0,T], σ² dP dt)`, `Uσu=σu`.

Uσ:Kσ→K_W is unitary; its inverse is v↦v/σ. There is no need for bounded σ, bounded inverse, or inverse moments. Put

`δσ=δW Uσ`, `dom(δσ)=Uσ⁻¹(dom(δW))`.

Then `Dσ=δσ*=Uσ⁻¹ DW`, with **exactly** dom(Dσ)=D¹,², and `(DσF)_t=D_t^W F/σ_t`. On predictable vectors δσ agrees with the Itô integral against M_t=∫₀ᵗσ_s dW_s. Under the Brownian natural filtration the predictable range statement follows by transferring the actual Brownian representation theorem. This is an operator equivalence, not stronger differentiability of terminal claims.

No Malliavin differentiability of σ is needed for this unitary operator transport. For cylinder coordinates M_t and their derivatives, require the additional genuine condition σ∈D¹,²(L²[0,T]). Then

`D_r^W M_t=σ_r 1_{r≤t}+∫ᵣᵗ D_r^Wσ_s dW_s`,

`κ_t(r)=D_r^W M_t/σ_r`.

Bounded smooth functions of finitely many M_t have actual weighted gradients by the Brownian chain rule. Product extension holds on D¹,⁴. Density of these particular M-coordinate cylinders in the **derivative graph norm** is a separate theorem, not established by generation of the terminal σ-algebra; TeX:1053–1057 leaves this unresolved.

For an explicit memory model, let `Y_t=∫₀ᵗ W_s ds=∫₀ᵗ(t−r)dW_r` and `σ_t=exp(ηY_t−η²t³/6)`, η>0, on a finite horizon. Gaussian exponential moments give every required finite moment, and `D_rσ_s=η(s−r)σ_s 1_{r≤s}`, so the preceding derivative hypothesis holds. Y is non-Markovian: its Gaussian covariance C(s,t)=s²(3t−s)/6 for s≤t violates C(s,u)C(t,t)=C(s,t)C(t,u), for example at (1,2,3), or a rescaling inside any positive horizon. The timewise invertible transformation to σ preserves this non-Markovianity.

The resulting centered martingale M has a non-Gaussian terminal law. Itô’s cubic formula and Brownian duality, justified by the finite moments, give

`E[M_T³]=6η∫₀ᵀ∫₀ˢ(s−r)E[σ_r σ_s²] dr ds > 0`.

This supplies non-Markovian volatility and a non-Gaussian output on Gaussian driving space. It is not a proof that the scalar process M alone is non-Markovian, nor an example of non-Gaussian driving noise. Volterra Malliavin sensitivities and representation methods already occur in work on stochastic Volterra equations; compare [Di Nunno–Giordano, arXiv:2011.07341](https://arxiv.org/abs/2011.07341).

The manuscript’s fractional Brownian example is a different extension: non-Markovian **Gaussian** noise. Gaussian operator calculus can support it after a genuine covariance/kernel transport. It does not validate the stated rough-path identification, which fails as explained next.
## 6. Failures that cannot be repaired by notation

### 6.1 Deterministic representers and false cancellation

The condition in `RepresentersDeterministic` at Lean:1496 says, in a genuine model,

`E[F <κ,u>] = EF E[<κ,u>]` for every random F,u.

For a deterministic nonzero κ, take a bounded centered nonzero F and u=Fκ. The left side is E[F²]||κ||²>0 and the right side is zero. Thus this is not the definition of a deterministic representer. Its conditional theorem proves a consequence of the wrong hypothesis.

The `hcancel` assumption at Lean:1601 is disproved by any bounded positive nonconstant F bounded away from zero and G=1/F; for example F=2+sin(W_T). Both factors belong to every finite Lp, FG=1, and G≠0. This is not an integrability or Lean API difficulty. A genuine stochastic-volatility obstruction must use adaptedness, the derivative-of-integral identity, and Brownian zero-gradient rigidity, as in Candidate 3 below.

### 6.2 Fake cylindrical data

In `CylindricalFunctional` at Lean:2939, choose one unit direction h, f_eval=0, F=0, df_eval=1 and dF=1. Every displayed evaluation and L² condition is satisfied, but the alleged derivative is nonzero. Applying `SteinLemma.stein` with this cylinder and h produces 0=1. Gaussianity of W does not repair independent derivative data. The rewrite’s actual polynomial differentiation and representation-independence proofs are the necessary repair; the legacy instance fields do not prove these facts.

### 6.3 Skorokhod isometry and projection multiplication

TeX:826 uses a positive Hilbert–Schmidt norm correction where the finite-dimensional Gaussian identity actually has the trace pairing

`E[(δu)²]=E||u||² + E Σ_i,j (∂_i u_j)(∂_j u_i)`.

For u=(G₂,−G₁), δu=0, E||u||²=2 and E||Du||²_HS=2; the actual trace term is −2. Consequently the proposed sum of positive norms is false. Even in one coordinate, u(G)=G gives E[(δu)²]=E[(G²−1)²]=2 while E[u²]=1: full divergence is not the predictable Itô isometry.

Conditional expectation also does not commute with multiplication by an anticipative terminal variable. For F=cos(W_t), r<t,

`E[D_r F|F_r]=−exp(−(t−r)/2) sin(W_r)`,

not −sin(W_r). The projection step in the manuscript’s Itô derivation (TeX:850 onward) cannot be obtained by Fubini or a product rule alone. A genuine Itô formula needs temporal semimartingale/quadratic-variation hypotheses or a different explicitly proved pathwise calculus.

### 6.4 The bracket normalization already fails for Brownian motion

TeX:770 defines the claimed bracket through `∫₀ᵗ ||Π D Y_s||²_H ds`. For Y_s=W_s on H=L²[0,T], DW_s=1_[0,s] and the predictable projection fixes it. The proposed value is therefore t²/2, whereas Brownian quadratic variation is t. A full terminal-variable Hilbert derivative is not an instantaneous time integrand.

Similarly, an isonormal fractional Brownian realization B_t=W(k_t) must have `||k_t||²=E[B_t²]=t^(2H)`. It cannot simultaneously have `||k_t||²=2H t^(2H−1)` by “normalization” as proposed at TeX:636–650 and1259. The latter is a derivative of variance, not the covariance-space norm. Changing it changes the represented Gaussian process. A one-time expectation correction involving d(t^(2H)) in a valid fBM formula must be derived with the correct covariance, not imposed on the RKHS norm.

### 6.5 A first-chaos counterexample to the claimed Gubinelli identification

Take canonical fBM with H>1/2, F=B_T^H, and Y_t=E[B_T^H|F_t^H]. This F has arbitrarily high Gaussian Sobolev regularity. According to the manuscript’s projection definition (TeX:524–583), DF=k_T and `(Π DF)_s=P_s k_T`, both deterministic. Its proposed leading term

`a_(s,t)=<P_s k_T, k_t−k_s>_H`

is therefore deterministic. But the canonical Volterra representation and equality of the Brownian/fBM natural filtrations give

`Var(Y_t−Y_s)=∫_s^t K_H(T,r)² dr`.

For a fixed interior 0<s<T this is asymptotic to the positive number K_H(T,s)² times t−s. Thus any remainder satisfying the displayed expansion must obey

`E[R_(s,t)²] = Var(Y_t−Y_s)+a_(s,t)² ≥ c_s(t−s)`

for t sufficiently near s. This contradicts the claimed O(|t−s|^min(4H,2H+1)), whose exponent is greater than 2 here. The Volterra/filtration construction is classical; see [Decreusefond–Üstünel (1999)](https://doi.org/10.1023/A:1008634027843). The contradiction is a direct calculation for the literal manuscript formula, not a claim that no relation between rough paths and Gaussian calculus can ever hold. In particular, adding D²,² regularity would not repair it. A Skorokhod integral cannot simply be identified with the deterministic RKHS inner pairing used at TeX:581.

### 6.6 Real open obligations rather than established consequences

The following remain plausible only as carefully restated, separate projects:

- Graph density of cylinders built from a specified non-Gaussian observed process M, rather than all underlying Wiener cylinders.
- Representation independence and local chain rules for a new concrete non-Gaussian differential model.
- A properly typed comparison between an actual pathwise controlled derivative and an L² predictable integrand, with hypotheses on the **process being controlled** and its path regularity.
- Non-Brownian filtration or stable-noise representation with the correct integrability scale. Infinite-variance stable noise is outside this Hilbert L² setup; a Banach extension needs its own duality and domain theory.

None is supplied by naming a cylindrical structure, assuming its graph density, or invoking closure alone. The cited follow-up manuscripts on Banach/stable factorization were not independently audited here; their existence does not discharge these obligations.

## 7. Literature and Lean ecosystem comparison

### 7.1 Mathematical priority and novelty classifications

| Claim | Classification and primary evidence |
|---|---|
| A derivative as the adjoint of a centered integral; separate anticipating and nonanticipating domains | **Classical mathematics.** Di Nunno–Rozanov, [§4.1, pp.29–30; §5.2, Theorem16, pp.39–40](https://abelsymposium.no/symp2005/preprints/dinunno.pdf), explicitly give these adjoints. Reversing the order of definitions is not new. |
| Best L² predictable integrand without differentiability of the terminal payoff | **Classical mathematics.** Di Nunno, [Stochastic integral representations, stochastic derivatives and minimal variance hedging](https://doi.org/10.1080/10451120212869), Stochastics and Stochastics Reports 73 (2002), 181–198. Publisher full text was not available in this review; the independently accessible Di Nunno–Rozanov treatment is the stronger inspected evidence. |
| Weak/functional derivative as the adjoint and inverse of the Itô integral on its range | **Classical mathematics.** Cont–Fournié, [Theorem5.8 and Theorem5.9, §5](https://arxiv.org/pdf/1002.2446). Their range, filtration, and regularity construction matter; an abstract adjoint does not dispense with them. |
| QCD representation of a Brownian indicator outside D¹,² | **Classical mathematics with an exact prior example.** [Allouba–Fontes (2011)](https://arxiv.org/abs/1011.1475), arXiv v2 2011-05-05; journal 29(6),1111–1135. |
| Constant conditional Stein pairing implies Gaussianity | **Classical Stein/Malliavin–Stein mathematics.** [Nourdin–Viens, Corollary3.3](https://arxiv.org/pdf/0808.2088); [Nourdin–Peccati–Réveillac, Lemma3.3](https://arxiv.org/pdf/0804.1889). The operator statement above is a formulation of this characterization. |
| Ordinary chain rules with non-Gaussian invariant laws | **Classical diffusion/Dirichlet-form mathematics.** [Ledoux–Nourdin–Peccati (2014), §4.3 and §5](https://arxiv.org/pdf/1403.5855) give a direct relevant comparison. Non-Markovian observations do not invalidate this theory. |
| Poisson add-one derivative, corrected product rule, divergence adjoint | **Classical mathematics.** [Peccati–Solé–Taqqu–Utzet (2008), §2](https://arxiv.org/pdf/0807.5035). The proposed scalar Lean realization would be a formalization contribution, not new Poisson calculus. |
| Weighted volatility transport Dσ=σ⁻¹DW | **New notation/presentation of a standard operator transport and Brownian chain calculation.** No stronger payoff domain is obtained. |
| Quantitative weighted representer defect in Candidate3 | **Potentially useful formulation; mathematical novelty unestablished.** It follows from standard Brownian derivative, projection, Itô-isometry and Poincaré facts. A dedicated priority search would be needed before calling it new. |
| Universal Itô/bracket and Gubinelli conclusions in this manuscript | **False or unsupported as stated.** Explicit counterexamples appear in §6. They are not prospective novelty. |

A useful contribution is still possible without novel probability theory: reliable adjoint-domain identification for a concrete non-Gaussian model, a reusable Lean library for it, and exact comparison theorems between distinct derivatives. No evidence supports a claim that current operator notation supersedes the mathematical reach of established Malliavin calculus, which already includes non-Gaussian measures and Poisson/Lévy settings.

### 7.2 Existing formalization that should be reused

Pinned local Mathlib is the compatibility authority. Public repositories are comparison evidence, not proposed new dependencies.

| Source | Actual inspected declarations and relevance |
|---|---|
| [Mathlib/Analysis/InnerProductSpace/LinearPMap.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/InnerProductSpace/LinearPMap.lean) | `mem_adjoint_domain_iff`:159; `mem_adjoint_domain_of_exists`:164; `adjoint_apply_eq`:184; `adjoint_isFormalAdjoint`:190; `IsFormalAdjoint.le_adjoint`:195; `adjoint_isClosed`:333. These already formalize basic unbounded-adjoint facts. |
| [Mathlib/Analysis/InnerProductSpace/Adjoint.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/InnerProductSpace/Adjoint.lean) | `LinearIsometry.adjoint_comp_self`:1068 supplies the main Hilbert identity for an isometric representation operator. It does not instantiate a stochastic integral or its surjectivity. |
| [Mathlib/Probability/Distributions/Poisson/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Probability/Distributions/Poisson/Basic.lean) | `ProbabilityTheory.poissonMeasure`:41; `poissonMeasure_real_singleton`:54; positivity:58; `integrable_poissonMeasure_iff`:76; `hasSum_integral_poissonMeasure`:88; `integral_poissonMeasure'`:104. These supply the concrete measure and honest integrability-to-series bridge. No shift/Stein identity was located in this file. |
| [gaussian-hilbert/GaussianHilbert/PolynomialDensity.lean](https://github.com/mrdouglasny/gaussian-hilbert/blob/main/GaussianHilbert/PolynomialDensity.lean) | `GaussianHilbert.polynomial_dense_L2_of_subGaussian` uses an exponential quadratic moment and proves squared-error polynomial density. This has non-Gaussian uses, but does not supply a derivative or graph density. A comment about Gamma laws is not enough to satisfy that strong tail hypothesis. |
| [lean-malliavin/Malliavin/MalliavinDerivative.lean](https://github.com/savarin/lean-malliavin/blob/main/Malliavin/MalliavinDerivative.lean) | `Malliavin.integral_inner_mderiv`, `integral_inner_mderiv_mul`, `inner_mderivLp_smulLp` are actual Gaussian Cameron–Martin/Fréchet derivative infrastructure. Their scope is not an arbitrary non-Gaussian measure. |
| [lean-malliavin/Malliavin/BrownianClarkOconeCapstone.lean](https://github.com/savarin/lean-malliavin/blob/main/Malliavin/BrownianClarkOconeCapstone.lean) and [ClarkOconeSolution.lean](https://github.com/savarin/lean-malliavin/blob/main/ClarkOconeSolution.lean) | `naturalMartingaleRepresentation_of_generated`, `bestNaturalItoIntegrand_eq_predictableProjection_of_generated`, `naturalClarkOcone_of_generated`, `naturalClarkOcone_condExp_of_generated`; also `PalomarClarkOcone.generated_clark_ocone`. The inspected types impose a Gaussian Banach measure, linear Brownian coordinates, generation, and natural filtration. This is relevant existing source, not proof of a generic non-Gaussian instance or confirmation that it builds against our pin. |
| [markov-semigroups/MarkovSemigroups/Abstract/DirichletForm.lean](https://github.com/mrdouglasny/markov-semigroups/blob/main/MarkovSemigroups/Abstract/DirichletForm.lean) | `DirichletSpace` in the inspected snapshot packages an energy, a core, symmetry, positivity and bilinearity. It does not by that declaration construct a closed gradient or identify its adjoint domain. The local project’s historical attribution to commit `acf649108ea2222f4a8544a2782f448cb502492a` must be distinguished from this mutable source snapshot. |
| [brownian-motion/BrownianMotion/StochasticIntegral/StochasticIntegral.lean](https://github.com/RemyDegenne/brownian-motion/blob/master/BrownianMotion/StochasticIntegral/StochasticIntegral.lean) | `ProbabilityTheory.IsRiemannStieltjesExtension` and `IsStochasticIntegral` are predicates with substantive elementary-agreement and convergence requirements. This inspected file alone is not construction of the L² integral or PRP. |

Other useful pinned declarations for the uniform candidate are `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` in `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean`:111; `polynomialFunctions_closure_eq_top` in `Mathlib/Topology/ContinuousMap/Weierstrass.lean`:53; and `ContinuousMap.toLp_denseRange` in `Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`:363. Use `ProbabilityTheory.cond volume (Icc (-1) 1)` for interval-uniform probability; the counting-measure `uniformOn` is not that construction.

The search did not verify an existing public Lean package with the exact scalar Poisson maximal-adjoint domains and graph cores proposed here. This is a bounded search finding, **not proof of absence**. Nor does it establish that every individual prerequisite is unformalized. Before upstream submission, repeat theorem-name/content searches against then-current Mathlib and the cited repositories.

### 7.3 Which local foundation genuinely transfers

Reusable measure-independent results include:

- [Adjoint.lean:20](C:/OperatorDerivativeRewrite/Foundation/Adjoint.lean:20): `operatorDerivative`, `operatorDerivative_isClosed`, `operatorDerivative_adjoint_identity`.
- [OperatorDomains.lean](C:/OperatorDerivativeRewrite/Foundation/OperatorDomains.lean): `mem_adjoint_domain_iff_representable`, `bounded_adjoint_domain`, `closed_graph_limit`.
- [AdjointClosure.lean:12](C:/OperatorDerivativeRewrite/Foundation/AdjointClosure.lean:12): `operatorClosure_le_closed`, `operatorClosure_dense_domain`, `formalAdjoint_closure_left`, `operatorClosure_adjoint_eq`.
- [AdjointBidual.lean:15](C:/OperatorDerivativeRewrite/Foundation/AdjointBidual.lean:15): `closedOperator_adjoint_adjoint_eq`, `closableOperator_adjoint_adjoint_eq_closure`.
- [MultiplierCore.lean:92](C:/OperatorDerivativeRewrite/Foundation/MultiplierCore.lean:92): `IsDivergenceMultiplier` and its `.preserves_adjoint_domain`, `.mem_adjoint_domain`, plus `divergenceCommutator_unique`. These require actual domain preservation and a bounded commutator; they do not manufacture Leibniz.
- `Foundation/LpProducts.lean` supplies actual Hölder/product integrability. It does not assert graph-domain membership.

Gaussian Hermite orthogonality, Gaussian coordinate laws, Gaussian Stein identities and Gaussian log-Sobolev estimates do not transfer simply by replacing a measure parameter. Poisson graph cores below admit a direct weighted-sequence proof, so no Charlier basis or imported semigroup project is needed for the first target.
## 8. Three precise candidate research results

These are proposed targets, not declarations already added to the repository.

### Candidate 1 — Full one-site Poisson adjoint and graph-core theorem

**Statement.** For every λ>0, the D and δ of §5.4 on S=L²(μλ), K=L²(λμλ), with the displayed maximal weighted-square-summability domains, are densely defined closed mutual adjoints. Restrictions D₀ and δ₀ to finitely supported functions satisfy

`closure(D₀)=D=δ₀*`, `closure(δ₀)=δ=D₀*`.

Finite coordinate truncations converge in both graph norms. The genuine difference product rule holds on the finite-support algebra, and δ1=N−λ, D(N−λ)=1 while D((N−λ)²)=2(N−λ)+1.

**Minimal hypotheses.** λ>0 and the concrete Poisson measure. No assumed PRP, graph density, chain rule, or unspecified “Poisson structure”. Zero rate is a distinct degenerate quotient case, excluded explicitly from this target.

**Strategy.** Use the actual Poisson weight recurrence, weighted shift norm formulas, finite-support density, coordinatewise graph limits, and adjoint testing against the coordinate indicators. The graph estimates are explicit below.

**Related work / novelty.** This is elementary scalar Poisson Malliavin calculus. Mathematical novelty: none claimed. A reusable Lean realization with maximal domains and graph-core identification appears a plausible new formalization contribution, subject to a final ecosystem search.

**Failure tests.** Ordinary Leibniz must fail by the extra ΔfΔg term; λ=0 cannot support arbitrary coordinate evaluation; domains must be maximal, not merely polynomial. An ambient L²-density proof is not enough. Infinite-dimensional vector divergence can have component cancellations; no such stronger domain restriction is proposed here.

**Difficulty / Lean requirements.** Low-to-moderate mathematical difficulty; moderate formalization work in Lp quotients, positive atoms, infinite sums, and `LinearPMap`. Reuse the current adjoint/closure/bidual modules and Mathlib’s Poisson measure; no new library dependency or spectral theory is necessary.

**Meaningful success.** A concrete non-Gaussian probability model satisfying actual operator adjointness, correct domains, a proved core, and its own honest calculus rule. This would expose exactly which earlier interfaces are measure-independent and which were covertly Gaussian/local.

### Candidate 2 — Uniform-interval derivation, full boundary adjoint, and Stein kernel

**Statement.** On μ=uniform[−1,1], define D₀p=p' on polynomial classes. On the dense core τ·polynomials, τ(x)=(1−x²)/2, define

`δ₀(τp)=xp−τp'`.

Both are well-defined, densely defined, and closable. Prove

`closure(D₀)f=f'`, with domain H¹([−1,1]),

`D₀*u=−u'`, with domain H¹₀([−1,1]),

and `closure(δ₀)=D₀*`, `δ₀*=closure(D₀)`. Ordinary product and bounded-derivative chain rules hold with their actual Sobolev membership hypotheses. For every C¹ φ on the interval,

`E[X φ(X)]=E[τ(X) φ'(X)]`.

**Minimal hypotheses.** The explicit uniform measure and weak derivative/trace domains. No Gaussian assumption, tail condition, or presumed derivative-data interface. Endpoint traces cannot be omitted.

**Strategy.** First prove the displayed finite-interval IBP from τ(±1)=0 and actual derivatives. Weierstrass plus continuous-to-L² density gives polynomial density. τ-polynomials are L²-dense: g orthogonal to all τp implies τg orthogonal to all polynomials, hence τg=0, so g=0 a.e. For full graph-core equality, prove H¹ approximation, not merely this density: approximate the derivative in L² and integrate to approximate H¹ functions; for H¹₀, cut off and smooth interior functions, then, for g∈C_c^∞(−1,1), approximate g/τ by polynomials in C¹. The quotient extends smoothly by zero near the endpoints, so multiplying these approximants by τ gives the required graph approximation. This is additional work, not a consequence of the first IBP lemma.

**Related work / novelty.** Standard Sobolev adjoints, boundary-value theory, and scalar Stein kernels. New mathematical theorem: no. It would be a clean formal countermodel to “chain rule implies Gaussianity” and a useful bounded-interval operator library.

**Failure tests.** The constant field 1 is not in the divergence domain. Incorrectly admitting 1 to dom(δ) with δ1=0 would force E[f′(X)]=0 for every f∈H¹; taking f(x)=x gives 1=0. The closure of a compactly supported derivative core imposes different boundary conditions from the closure of polynomials.

**Difficulty / Lean requirements.** First IBP very small; complete domain identification moderate, with trace and H¹ approximation work. Reuse interval integration by parts, the project’s local FTC/primitive techniques where their measure-independent statements apply, Mathlib’s polynomial density, and the generic adjoint foundation. Gaussian-specific approximation theorems cannot simply be applied under μ.

**Meaningful success.** An actual non-Gaussian derivation with full boundary-sensitive adjoints, retaining ordinary chain rules. This is the best alternative if retaining the ordinary chain rule is a higher priority than modeling non-Gaussian noise.

### Candidate 3 — Quantitative stochastic-volatility representer rigidity

**Statement.** On canonical Brownian space, assume σ is positive a.e., predictable, jointly measurable, and belongs to D¹,²(L²[0,T]). Let M=∫σdW, let Kσ,Uσ,Dσ be as in §5.5, and set κ_T(r)=D_rM_T/σ_r. Let Πσ be the orthogonal projection onto the predictable subspace in **Kσ**. Then

`Πσ κ_T=1`,

`||κ_T−1||²_Kσ = E∫₀ᵀ ||D^W σ_s||²_L²[0,T] ds`,

`∫₀ᵀ Var(σ_s) ds ≤ ||κ_T−1||²_Kσ`.

Consequently κ_T is predictable if and only if σ is deterministic as an L²([0,T]×Ω) equivalence class. A deterministic κ_T is therefore possible only for deterministic volatility; conversely deterministic σ gives κ_t=1_[0,t] for every t. The quantitative assertion is stronger and more informative than the corrected deterministic-representer corollary.

**Proof.** Multiplication by σ maps the predictable weighted subspace unitarily to the ordinary predictable Brownian subspace, so `Πσ=Uσ⁻¹ΠW Uσ`. The genuine derivative-of-Itô-integral formula yields

`σ_r(κ_T(r)−1)=∫ᵣᵀ D_rσ_s dW_s`.

For almost every r its conditional expectation given F_r is zero. Thus the weighted projection is 1. Itô isometry, Tonelli, and adaptedness (D_rσ_s=0 for r>s) yield the norm identity. The canonical Wiener Poincaré inequality gives the variance bound and the zero-gradient characterization. Conversely deterministic σ has zero Brownian derivative. All statements use L² equivalence classes and a.e. times.

Do **not** write `E[κ_T(r)|F_r]` without additional unweighted integrability: division by σ can destroy it. Conditioning `D_rM_T=σ_rκ_T(r)` and using the weighted Hilbert projection is the correct argument. No inverse-moment bound is needed.

**Related work / novelty.** Weighted operator conjugacy, differentiation of an adapted Itô integral, Gaussian Poincaré and martingale projection are standard. This exact defect formulation is a plausible useful research presentation; no claim of first discovery is justified by the search. It repairs the mathematical intent of TeX:1116 onward without the false legacy `hcancel` hypothesis. It does not prove graph density of M-coordinate cylinders or a general non-Brownian chain rule.

**Failure tests.** On an enlarged space with an independent nonconstant positive initial variable A∈L², σ_t=A has Brownian derivative zero but is not deterministic. The inference uses the zero-gradient-implies-deterministic property, which canonical Brownian space ensures; it need not hold after enlargement by independent randomness. If σ vanishes on a positive-measure set, the stated unitary inverse fails. If σ lacks the Malliavin condition, κ_T is not justified by the formula. One terminal horizon T must be covered; representers for a few earlier observation times cannot determine volatility after the last observation.

**Difficulty / Lean requirements.** Short ordinary proof after substantial prerequisites; high formalization cost at present. Requires the concrete Brownian process/filtration, Itô integral and isometry, derivative-through-Itô theorem, weighted predictable projections, and Wiener Poincaré for time-valued variables. The existing Gaussian Hilbert derivative is a useful analytic base but does not supply these process results merely by relabeling coordinates.

**Meaningful success.** A precise quantitative obstruction with minimal positivity/integrability assumptions, plus a distinction between Gaussian underlying noise and non-Gaussian martingale output. This is the candidate closest to a sharpened manuscript research theorem.

### Ranking and choice

Ranks compare these three targets, with 1 highest. “Novelty potential” does not assert novelty.

| Criterion | Candidate1: Poisson | Candidate2: uniform | Candidate3: volatility |
|---|---:|---:|---:|
| Mathematical significance for the manuscript’s research agenda | 2 | 3 | 1 |
| Potential for a useful new mathematical formulation | 2 (classical) | 3 (classical) | 1 (unestablished) |
| Extension beyond Gaussian driving-law calculus | 1 (genuine Poisson base) | 2 (non-Gaussian base and diffusion invariant law) | 3 (transport of Gaussian driving calculus) |
| Feasibility of a complete Lean operator milestone now | 1 | 2 | 3 |
| Reusability as a concrete library contribution | 1 | 2 | 3 |

**Choose Candidate1.** It offers the best balance of a real change of probability law, exact closed-operator substance, existing Mathlib support, and manageable proof obligations. Candidate3 is a later research direction, not a reason to postpone a small complete theorem. Do not restart general interfaces, Brownian stochastic integration, or abstract semigroups for this first task.

## 9. Complete ordinary proof architecture for the chosen theorem

Write w_n=μλ({n}). The recurrence `(n+1)w_(n+1)=λw_n` is the only probability-specific input beyond positivity and summability of the Poisson weights.

Let `Af(n)=f(n+1)` and `Bu(n)=n u(n−1)`. Direct nonnegative-series reindexing gives

`||Af||²_K = Σ_n n w_n |f(n)|²`,

`||Bu||²_S = λ Σ_n (n+1) w_n |u(n)|²`.

Since S and K have equivalent norms for fixed λ>0, the unshifted f and λu already belong to the respective target spaces. Therefore Df=Af−f belongs to K exactly when Af does, and δu=Bu−λu belongs to S exactly when Bu does. This proves the stated maximal domains; no cancellation has been discarded.

The triangle inequalities applied to A=D+id and B=δ+λid give graph-norm equivalences

`||f||²_S+||Df||²_K ≍_λ Σ_n(n+1)w_n|f(n)|²`,

`||u||²_K+||δu||²_S ≍_λ Σ_n(n+1)w_n|u(n)|²`.

The notation means two proved bounds with positive constants depending only on λ; exact optimal constants are unnecessary. For example use `|a+b|²≤2|a|²+2|b|²`. Finite truncations to {0,…,m} converge in the weighted series norm by summable tails, hence in both graph norms. The shift’s support boundary is included in these estimates, not ignored. In particular the derivative boundary error contributes `(m+1)w_(m+1)|f(m+1)|²`, which tends to zero by weighted summability.

Every coordinate evaluation is continuous in S and K because w_n>0. If f_k→f and Df_k→g in their respective Hilbert spaces, coordinatewise limits give g(n)=f(n+1)−f(n). As g∈K, the domain equivalence puts f in dom(D). This proves closedness. The same argument proves closedness of δ. Finite-support sequences are dense in each ambient L² space, independently of the graph argument.

On finite supports, reindexing yields

`<Df,u>_K = Σ_n w_n f(n)[n u(n−1)−λu(n)] = <f,δu>_S`.

Graph approximation extends this identity to the full domains. Thus δ⊆D*. Conversely, if u∈dom(D*) with value v, test the adjoint identity against the coordinate indicator e_n. It forces `v(n)=n u(n−1)−λu(n)` at every n. Since v∈S, the maximal-domain equivalence gives u∈dom(δ). Hence δ=D*, and dense closed D gives δ*=D. Equivalently the same indicator argument can identify D₀* directly; graph cores then give all four closure/adjoint equalities.

The product formula is ordinary algebra for differences, with finite support guaranteeing all terms are in the right L² spaces. Poisson moment estimates then place 1,N−λ,(N−λ)² in the maximal domains and verify the ordinary-chain counterexample. These are actual functions of N, not independently assigned derivative data.

This argument deliberately remains scalar. In a future multi-coordinate divergence, sums of shifted vector components can cancel. One must characterize the square summability of their **combined** coefficients, not transplant the scalar component domain as a necessary vector condition.
## 10. Incremental Lean roadmap and exact first implementation task

All declaration names in this section are **proposed**, not claims that they currently exist. Each milestone should be separately built, checked with `#print axioms`, and independently reviewed before the next one. Do not introduce an abstract interface whose fields are the pending conclusions.

### P0 — Finite-support Poisson shift and integration by parts

Proposed module: `Foundation/PoissonDifferenceCore.lean`.

Objects:

- `λ : ℝ≥0`, with explicit `0 < λ` where nondegeneracy is needed.
- `μ := ProbabilityTheory.poissonMeasure λ` on the existing discrete measurable space ℕ.
- `poissonWeight λ n := μ.real {n}`.
- Actual finite sequences `f u : ℕ →₀ ℝ`.
- `forwardDifference f n := f (n+1) - f n`.
- `backwardWeighted u 0 := 0`, `backwardWeighted u (n+1) := (n+1 : ℝ) * u n`.
- `poissonDivergenceExpr λ u n := backwardWeighted u n - (λ : ℝ)*u n`.

Required statements:

1. `poisson_weight_succ`: for every n, `(n+1 : ℝ)*poissonWeight λ (n+1) = (λ : ℝ)*poissonWeight λ n`.
2. Explicit finite-support preservation and integrability lemmas for f, u, forwardDifference f, backwardWeighted u, divergenceExpr u, and the two IBP product integrands. Prove their L² membership where used; do not infer it from a totalized real integral identity.
3. `poisson_shift_finsupp`: `∫ n, (n:ℝ)*f n ∂μ = (λ:ℝ)*∫ n, f (n+1) ∂μ`.
4. `poisson_difference_ibp_finsupp`: `(λ:ℝ)*∫ n, forwardDifference f n * u n ∂μ = ∫ n, f n * poissonDivergenceExpr λ u n ∂μ`.
5. If small, `poisson_difference_mul_finsupp`: pointwise actual difference product rule, including the additional product of differences. Its omission from P0 must be documented rather than replaced by ordinary Leibniz.

Use `poissonMeasure_real_singleton`, `Nat.factorial_succ`, `pow_succ`, the genuine integrability-to-series theorem `integral_poissonMeasure'`, and finite-sum reindexing. The no-integrability version `integral_poissonMeasure` at line122 is mathematically totalized outside the integrable case; do not use its existence as evidence that an integral is finite.

**Acceptance:** exact factor λ and the n=0 term checked, actual integrability before integral algebra, no assumed shift/Stein identity, no prescribed derivative data, no density or graph claim yet. Add the module to project imports and the axiom audit, document the narrow milestone, run the full Lake build and transitive axiom checks, and commit only that verified implementation when later authorized. This research task itself does not implement or commit P0.

### P1 — Concrete Hilbert spaces and dense operator cores

Use native Mathlib spaces

`ScalarL2 λ := Lp ℝ 2 (poissonMeasure λ)`,

`IntegrandL2 λ := Lp ℝ 2 ((λ : ℝ≥0∞) • poissonMeasure λ)`.

Their inner products are E[fg] and λE[uv]. Prove the scalar-measure norm/inner-product relationship using Mathlib’s Lp scaling APIs, including `eLpNorm_smul_measure_of_ne_zero` in `MeasureTheory/Function/LpSeminorm/Basic.lean`:740. Avoid installing a custom incompatible real inner-product instance on the same type.

Construct finite-support embeddings and prove injectivity from positive atoms. Use these to define `poissonDerivativeCore` and `poissonDivergenceCore` as `LinearPMap`s on their actual image submodules. Prove `poisson_core_dense` separately in each Hilbert space, and `poisson_core_formalAdjoint` from P0.

**Acceptance:** well-definedness on L² classes, genuine domain density, correct scalar-weight pairing, and both closability inclusions. No full adjoint equality claimed from formal adjointness alone. Reuse `IsFormalAdjoint.le_adjoint` and the local closability/closure infrastructure.

### P2 — Maximal domains from weighted shift estimates

Define the maximal operators by pointwise forward/backward expressions with actual L² membership. Because each atom has positive measure, evaluation is independent of representatives; establish this before using coordinates of quotient classes. Prove `poisson_forward_shift_norm_sq` and `poisson_backward_shift_norm_sq`, first as nonnegative series identities and then as finite real identities under membership assumptions.

Prove `poissonDerivative_mem_domain_iff` and `poissonDivergence_mem_domain_iff` with exactly the domains in Candidate1. Prove `poissonDerivative_isClosed` and `poissonDivergence_isClosed` via continuous coordinate evaluations or graph limits. Do not require bounded functions, finite support, or extra weighted moments for the maximal operators.

**Acceptance:** both directions of each domain equivalence; no “integrable by assumption” substitution for the required weighted estimate; no λ=0 division; explicit finite quantities before manipulating real sums/integrals.

### P3 — Finite truncations are graph cores

Define `truncate m f := 1_{n≤m} f(n)` as an actual finite-support sequence. Prove a scalar L² tail theorem and the weighted tail theorem. Use the inequalities in §9 to prove simultaneous convergence of `truncate m f` and its actual derivative, and of `truncate m u` and its actual divergence.

Proposed declarations: `poissonDerivative_truncate_graph_tendsto`, `poissonDivergence_truncate_graph_tendsto`, `poissonDerivativeCore_closure_eq`, `poissonDivergenceCore_closure_eq`.

**Acceptance:** one common truncation sequence for both components of each graph; the successor boundary is accounted for; no graph-density assumption and no polynomial-density substitution. A successful ambient L²-density proof alone does not finish this milestone.

### P4 — Exact mutual adjoints

Use P0/P3 for the formal-adjoint identity on full domains. For the reverse inclusion, test a general adjoint pair against each coordinate indicator and derive the actual backward/forward coefficient formula. Apply P2 to obtain domain membership.

Proposed declarations: `poissonDerivative_adjoint_eq_divergence`, `poissonDivergence_adjoint_eq_derivative`, and the corresponding core-adjoint equalities.

Reuse `closedOperator_adjoint_adjoint_eq` only after supplying its actual density assumptions. They follow from the concrete cores, not from a new unproved instance. Alternatively prove both reverse inclusions by coordinate tests.

**Acceptance:** equalities of `LinearPMap`s, including domains and values; exact normalization against K=L²(λμ); ordinary standard foundational axioms only. This finishes the principal independently meaningful target.

### P5 — Honest calculus and its rigidity boundary

Extend the finite-support product identity only under explicitly proved membership conditions. Prove the needed low-order Poisson moments and the maximal-domain statements for 1, N−λ and its square. Establish δ1=N−λ, D(N−λ)=1, and the nonzero ordinary-chain defect.

This gives a concrete formal answer to the rigidity question: the constant-pairing Gaussian theorem needs its ordinary chain hypothesis. It does not yet formalize a Poisson process, a random-measure divergence, Clark–Ocone, multivariate cancellation-sensitive domains, Charlier spectral theory, or a log-Sobolev inequality.

**Independent audit checkpoint:** compare the final statements against the original total-multiplication and generic-chain interfaces. The new module must stand on its own without satisfying false fields by changing mathematical meanings.

## 11. Final research recommendation

**What survives:** dense/closed adjoint theory; correctly restricted IBP and product calculations; predictable projection formulas after constructing an isometric integral and proving its range; concrete Gaussian results already repaired in the rewrite; and weighted stochastic-volatility transport with exact domains.

**What fails:** automatic calculus and representation from adjointness; unrestricted L² multiplication and graph-domain algebra; the legacy deterministic-representer definition and cancellation argument; a full Skorokhod isometry; and the original bracket/Gubinelli/Itô conclusions as stated.

**What is genuinely interesting:** exact domain comparisons between the predictable integral adjoint and the full divergence adjoint, non-Gaussian instances with actual graph cores, the precise Stein boundary of Gaussianity, and the quantitative weighted representer defect. The latter is promising but not established as novel mathematics.

**How far this can extend:** beyond Gaussian laws to weighted differential models and jump/difference calculus, and to processes with memory through verified process-specific constructions. Ordinary chain rules, stochastic representations, and pathwise controlled expansions require different additional hypotheses. There is no justified universal calculus covering all of them from one adjoint definition.

**Exact first Sol Medium task:** implement **P0 only**, `Foundation/PoissonDifferenceCore.lean`, proving the actual finite-support Poisson recurrence, integrability, shift identity and bilinear adjoint identity with rate λ. Preserve all current sources and pins; do not begin stochastic processes, new semigroups, or general-interface revisions. Build and audit the resulting small module before attempting maximal-domain or graph-core equalities.