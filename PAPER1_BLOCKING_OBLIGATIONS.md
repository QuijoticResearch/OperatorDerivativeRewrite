# Paper 1: blocking mathematical obligations

Audit date: 2026-10-12. Rewrite HEAD: `582ee395185c1a2a4d42654d9a3b6ac6f67853a9`.

**Verdict: REVISE. The current manuscript is not defensible as written.** Its central stochastic-volatility rigidity argument has a credible repair. Several other main claims have counterexamples, and the original Lean declarations do not certify those manuscript claims. The verified rewrite provides substantial Gaussian operator theory, but not the claimed complete stochastic-calculus pipeline.

This report is a mathematical audit, not a formalization of its counterexamples or proposed repairs. No manuscript, Lean source, dependency pin, or pre-existing untracked document was changed. See [inventory](C:/OperatorDerivativeRewrite/PAPER1_THEOREM_INVENTORY.md), [Lean crosswalk](C:/OperatorDerivativeRewrite/PAPER1_LEAN_CROSSWALK.md), and [completion plan](C:/OperatorDerivativeRewrite/PAPER1_COMPLETION_PLAN.md).

## Source and evidence conventions

- `T` means [C:\Operator\OperatorDerivative.tex](C:/Operator/OperatorDerivative.tex), the canonical available Paper 1 manuscript, 1,547 lines.
- `L` means [C:\Operator\OperatorDerivative.lean](C:/Operator/OperatorDerivative.lean), the original 5,184-line development. A declaration in this file is not automatically part of the compiling rewrite.
- `F` means `C:\OperatorDerivativeRewrite\Foundation\`.
- Source ranges below refer to the inspected snapshots, not proposed edits.
- A successful proof of an implication does not establish that its hypotheses describe the intended stochastic model. Standard axioms in `#print axioms` do not detect a false premise, an empty class of realizations, or a conclusion weakened to `True`.

The rewrite builds successfully: 4,030 jobs. The transitive audit of 1,213 listed declarations reports only `propext`, `Classical.choice`, and `Quot.sound`. The independently compiled legacy prefix `Legacy/GaussianLogSobolevSection.lean` passes. The original full file fails at lines 3156, 3272, 3300, 3609, 3630, 3696, and 4456. The root imports Foundation modules, not either full legacy file. These checks are evidence about the checked Lean statements, not validation of the paper.

## Priority register

“Blocking” means a retained publication claim cannot stand until corrected or proved. “Optional” is relative to the central rigidity contribution; a false assertion cannot simply remain in an optional section.

| ID | Priority | Affected claims | Required resolution |
|---|---|---|---|
| B01 | Blocking, first | Energy space, adjoint, predictable/full operators; A, D, E | Fix the Hilbert spaces and distinguish the bounded predictable adjoint from the unbounded full derivative. |
| B02 | Blocking | Both legacy interfaces; Leibniz and product domains | Eliminate universal L² multiplication and whole-domain algebra assumptions from the mathematical architecture. |
| B03 | Blocking | A, Clark–Ocone, GKW, variance | State the derivative formula on its actual domain and construct the all-L² representation operator separately. |
| B04 | Blocking | B, equivalences, cylindrical reduction | Supply genuine derivatives, appropriate graph approximation, and precise product/divergence domains. |
| B05 | Blocking, central contribution | E, rigidity, obstruction, classification | Replace the incorrect legacy predicates and cancellation hypothesis with actual Brownian sensitivity and constant-kernel arguments. |
| B06 | Blocking if Gaussian/Volterra claims retained | fBM factorization, RKHS projection, normalization | Correct the projection type, transported formula, and covariance normalization. |
| B07 | Blocking if C retained | Intrinsic bracket, scalar/multivariate Itô, local isometry | Revise false formulas and provide actual time-dependent analytic estimates; this is more than Fubini. |
| B08 | Blocking if F retained | Gubinelli theorem and rough-path comparison | Replace a false theorem explicitly; additional Malliavin smoothness does not repair it. |
| B09 | Blocking | Lean-status and novelty assertions | Replace claims of full formalization with an exact declaration-level account. |
| B10 | Blocking at each use | Stochastic-volatility hypotheses, examples and versions | State correct moment, measurability, filtration, and almost-everywhere qualifications. |
| N01 | Nonblocking for central E | Adjoint density exposition, references | Replace circular exposition with the standard graph-orthogonality proof or a precise citation. |
| N02 | Nonblocking for central E | Poisson representation example | Repair its all-L² proof using bounded tests and finite-intensity integrability; the conclusion is not refuted. |
| O01 | Optional extension | Graph density of smooth M-cylinders | Not needed for the terminal-coordinate rigidity proof below. Do not claim it from sigma-algebra generation. |
| O02 | Optional extension | General Volterra/fBM Itô and rough paths | Separate development after the main paper's scope is resolved. |
| O03 | Optional extension | Exotic-filtration “wild defect” conjecture | Reformulate: the current wording already admits a Brownian example. |
| O04 | Outside this task | C7, Banach and further Poisson extensions | Do not pursue to fill Paper 1 gaps. |

## B01 — the operator and its Hilbert space must be fixed

At T208–214 the input is `L²(Ω;H_X)`, with H_X a deterministic Hilbert space. At T220–225 and T964–974, H_X is itself a Hilbert space of random predictable or weighted processes, already integrating over Ω. Expressions such as `L²(Ω;H_M^ext)` at T996,1000,1009,1018,1022–24,1123–35 introduce a second probability variable. They are not the weighted norm actually used in the proofs.

Use a single abstract integrand Hilbert space K. In a Gaussian realization, K may be `L²(Ω;H₀)` for deterministic H₀. In the volatility realization it is `K_σ=L²(σ² dt dP)`. Specify a closed predictable subspace P of K and an isometry `J:P→L²(Ω)` independently of the full closed divergence `δ:dom δ⊂K→L²(Ω)`.

Then there are two distinct adjoints:

- `J*` is bounded and defined on every L² random variable. It produces the predictable representation integrand.
- `D=δ*` is generally unbounded and has its natural proper domain. It is the full Malliavin-type derivative when the realization proves that identification.

On `dom D`, one can prove `J*F=P D F` when δ extends J. This does not identify the two operators on all L² or transfer Leibniz from D to J*.

Concrete Brownian check: `D^full W_T²=2W_T 1_[0,T]`, but `(J*W_T²)_t=2W_t`. The examples at T1245–1255 cannot use these interchangeably. Conversely, extended divergence is not an isometry even for σ=1: for `u_t=W_T`, `δu=W_T²−T`, so `E(δu)²=2T²` while `E∫u²dt=T²`. The classification at T1190–1206 mixes properties of different operator pairs.

The predictable σ-algebra and time parameter must also exist before defining “predictable H-valued elements.” An arbitrary deterministic RKHS vector has no time-coordinate evaluation merely by being in a Hilbert space.

## B02 — multiplication and domain closure

L101–175 (`UnboundedEnergySpace`) and L735 onward (`EnergySpace`) supply total operations `L²×L²→L²`, scalar multiplication into vector L², and a vector pointwise inner product into scalar L². These are not genuine operations on unrestricted L² classes. L149 additionally assumes the entire adjoint domain is an algebra. L3272 fails in the attempted concrete product realization.

Counterexample: on `(0,1)` with probability Lebesgue measure, `f=g=x^(−1/3)` are in L², but `fg=x^(−2/3)` is not in L². Vector-valued inner products obey the same obstruction by using a fixed unit vector.

Even the actual Gaussian derivative domain is not an algebra. For standard γ, `f(x)=exp(x²/6)` and `f'(x)=(x/3)exp(x²/6)` lie in L²(γ), but f is not in L⁴(γ); hence f² is not in L². This also refutes the advertised `D^{1,2}⊂L⁴` implication behind L2429.

Correct operations are L²×L²→L¹, L⁴×L⁴→L², and L∞×L²→L², with corresponding scalar/vector Hölder estimates. Actual product-domain membership is a separate theorem. The rewrite proves these estimates in `F/LpProducts.lean`, polynomial closure in `F/InfiniteGaussianPolynomialProducts.lean`, and domain preservation for **proved admissible commutators** in `F/MultiplierCore.lean`; it does not assume every multiplier preserves an arbitrary closed operator's domain.

There is a second obstruction to the bounded legacy architecture. If a bounded map `D:L²→L²(H₀)` obeys genuine Leibniz on all bounded functions, then
`D1_A=2·1_A D1_A`, so `D1_A=0`. Linearity and simple-function density imply D=0. A nontrivial Malliavin derivation cannot be both bounded on all L² and Leibniz on all bounded functions.

## B03 — representation formulas and exact domains

T91–97,327–339,379–385,409–418 quantify over all L² while applying the potentially unbounded δ*. PRP and predictable isometry do not make the full derivative everywhere defined. For example, in one Gaussian coordinate with normalized Hermites H_n, the L² series `F=Σ_{n≥1} H_n/n` has finite scalar norm but derivative energy `Σ n/n²=∞`. It lies outside the Gaussian derivative domain.

The original `UnboundedEnergySpace.clark_ocone_unbounded` at L226 correctly carries `F∈dom D` and a projected divergence-domain condition. The paper omits these. `variance_identity_unbounded` at L314 takes the Clark–Ocone identity as an explicit hypothesis; it does not establish it independently.

Minimal corrected theorem: for a closed P⊂K and centered linear isometry J into scalar L², `JJ*` is the orthogonal projection onto the closed range of J. Thus it gives GKW on all L². If `range J` is the centered terminal L² subspace, `JJ*F=F−EF` and `Var(F)=‖J*F‖²` there. For a densely defined δ extending J, `J*F=Pδ*F` for F in `dom δ*`. No multiplication hypotheses are needed.

Specify whether scalar L² means the terminal filtration's L² or a larger probability-space L². PRP is about the former. This repair preserves the intended adjoint identification and an all-L² representation; it does not declare the unbounded derivative total.

## B04 — cylindrical reduction, graph approximation, and product rules

The proof at T719–727 contains a valid strategy: if F_n,G_n converge with their genuine derivatives in L⁴, Hölder gives convergence of products and product derivatives in L²; closedness then gives `FG∈dom D₂` and its Leibniz identity. The target is dom D₂, not necessarily D^{1,4}.

However:

1. T703 only assumes representers κ_i in L². It does not ensure that every declared cylinder has L⁴ derivative. Define the L⁴ graph closure using the finite-L⁴ part of the core, or establish the necessary moment property in each realization. The genuine Gaussian polynomial core has all finite moments.
2. L348 `cyl_dense` contains a sequence but **no convergence condition**. L367 `leibniz_closure` supplies the missing extension as a field. Applying it in L407 is not a proof of graph approximation.
3. At T687, global C¹ approximation of a nonzero compactly supported function by polynomials on all of Rⁿ is impossible. A polynomial with bounded global error from a bounded function is constant. Multiplying a polynomial by a smooth cutoff makes it nonpolynomial; its chain rule is precisely an unproved step. At T693, `xy` is outside `C_b^∞`. Both directions need a domain-sensitive truncation proof, not the stated one-line reductions.
4. At T695–697 and T793–807, membership `Fu∈dom δ` is used before being established. Testing on an ambient-dense bounded subclass does not extend an identity involving DG; graph density is required. With only closable δ, the dual argument gives membership in `dom δ**=dom closure δ`, not necessarily the original domain.
5. T739 asserts `D^{1,4}=D^{1,2}∩L⁴`, which is false. With a compact smooth cutoff χ equal to one near zero, `f=χ|x|^(2/3)` is bounded and in Gaussian D^{1,2}, but its weak derivative behaves like `|x|^(−1/3)` and is not in L⁴. Standard Gaussian Sobolev spaces do not have the asserted equality.
6. L2939 `CylindricalFunctional` allows independent `f_eval` and `df_eval`. Composition at L4892 prescribes the purported derivative, so L4920's unfolding identity does not establish actual differentiation. A universal Stein assumption on this class is inconsistent in a nonzero H: take a one-coordinate zero function with derivative data one along a unit vector; the supposed Stein equality becomes 0=1.

Repairs: reuse the actual polynomial gradient and representation independence from the rewrite; prove the L⁴ graph-limit product theorem; prove smooth functional calculus and full divergence multiplier domains separately if retained. Keep IBP hypotheses as genuine, independently verified identities on the chosen core, never as a replacement for the desired conclusions.

## B05 — preserve and genuinely prove central rigidity

The abstract and novelty discussion (T48–65,158–188), main E (T140–142), and `thm:obstr` (T1116–1166) make deterministic-representer rigidity central. It should not be replaced silently by the easier representation theorem.

The legacy names do not prove it:

- `EnergySpace.RepresentersDeterministic` (L1496) requires `E[F〈κ,u〉]=EF·E〈κ,u〉` for every random u. This is not ordinary determinism of κ. Even deterministic unit κ with u=Fκ fails for a nonconstant centered F.
- `representer_rigidity` (L1515) propagates that expectation factorization; `deterministic_variance_bound` (L1537) is also a factorization, not the claimed variance bound.
- `stoch_vol_obstruction` (L1590–1632) assumes `hcancel`: a nonconstant F and constant FG force G=0. On two equally likely points, F=(1,2), G=(1,1/2) refute it with bounded functions. Kernel checking of this implication cannot establish the stochastic theorem.
- `UnboundedStochVolAssumption` (L546) supplies the Brownian derivative, global Leibniz, and transfer formula. L560 proves algebra from these inputs, not their Brownian realization.

### A precise repair that preserves the contribution

Work on the completed natural Brownian filtration on [0,T], T>0. Let σ be predictable, strictly positive dt dP-a.e., and in `L²([0,T];D^{1,2})`. In particular require

`E∫σ_s² ds + E∫∫|D_r^W σ_s|² dr ds < ∞`.

Let `M_T=∫σ_s dW_s`, `K_σ=L²(σ² dt dP)`, and `U_σu=σu`. Prove that U_σ is unitary onto `K=L²(dt dP)`; define the closed extended divergence by exact pullback of dom δ^W. Then prove

`dom D_M=dom D^W`, and `D_M F=U_σ^{-1}D^W F`.

**Proposed terminal rigidity theorem:** if `D_M M_T` has a deterministic time representative k, then σ_s is deterministic for dt-a.e. s. This is a mathematical repair proposal, not an existing Lean theorem.

Proof obligations and argument:

1. Prove the genuine stochastic-integral sensitivity theorem, with jointly measurable/predictable versions:
   `D_r^W M_T = σ_r + I_r`, where `I_r=∫_r^T D_r^Wσ_s dW_s`, for dr dP-a.e. (r,ω).
2. The deterministic representer assumption gives `I_r=(k(r)−1)σ_r`. For a.e. r both σ_r and I_r are in L². The Itô integral is centered, so `0=(k(r)−1)Eσ_r`. Since `0<Eσ_r<∞`, k(r)=1. No inverse-moment assumption on σ is needed.
3. Itô isometry gives `E∫_r^T|D_rσ_s|²ds=0`. Tonelli yields zero derivative on r≤s. Adaptedness gives zero on r>s. The natural Brownian Gaussian constant-kernel theorem makes σ_s deterministic for a.e. s.

The sensitivity theorem, versions, and constant kernel must be derived in the actual model. They must not become assumptions that merely rename the desired rigidity conclusion.

To recover the cylinder formulation, include the terminal coordinate M_T. Since x itself is not in C_b^∞, use smooth bounded cutoffs φ_R with uniformly bounded first derivatives, φ_R→id and φ'_R→1. Proved cylindrical formulas, dominated convergence in the weighted integrand space, and closedness identify `D_M M_T=κ_T`. No density of all smooth M-cylinders in the full graph domain is necessary for this argument.

The natural-filtration/constant-kernel qualification is essential: if an independent initial Z>0 is allowed and Malliavin differentiation acts only on the Brownian factor, σ_t=Z is random but `D^Wσ=0` and `D_M M_t=1_[0,t]`. A definition using only the closure of deterministic Brownian cylinders excludes Z instead. The paper must specify which probability space and domain it uses.

## B06 — Gaussian/Volterra realization and normalization

T528–530 defines `(Πu)_t=P_t E[u|F_t]`. An H-valued u becomes a **time-indexed family** of H-valued fields; this is not an endomorphism of `L²(Ω;H)` on which δ_H acts. T620 silently switches to an orthogonal projection. These definitions cannot be interchanged.

The actual Decreusefond–Üstünel formula uses transport through the Volterra map and conditional expectation in Brownian integrand coordinates. The manuscript's formula and cited theorem numbers need checking against that result. See [Decreusefond–Üstünel, Theorem 4.6, PDF p.21; Theorem 5.1, p.28](https://moodle.r2.enst.fr/moodle/pluginfile.php/3841/mod_resource/content/4/fbm.pdf). The latter Itô theorem has H>1/2 and specific Malliavin hypotheses; it does not establish the manuscript's uniform claim.

T636–646 imposes `‖k_t‖²=2Ht^(2H−1)` while preserving the isonormal map, covariance, and `DX_t=k_t`. These force `‖k_t‖²=E(X_t²)=t^(2H)`. The variance and its derivative are different objects. Reweighting representers cannot preserve all three identities.

The kernel assumptions at T486–488 need per-time square integrability and measurability, not just an integrated condition giving sections for a.e. time. T597–604's “sufficient regularity” is not a checkable hypothesis. None of the rewrite's genuine canonical Gaussian product construction supplies an arbitrary Volterra kernel, Brownian filtration, or this time projection automatically.

## B07 — the claimed universal Itô theorem is not proved

### Bracket counterexample

T770–774 defines `[Y]^op_t=∫₀ᵗ‖ΠDY_s‖_H²ds`. For Brownian motion in the full Gaussian realization, `DW_s=1_[0,s]`, so the expression is `∫₀ᵗs ds=t²/2`, not t. Similarly its canonical fBM value is `t^(2H+1)/(2H+1)`, not `t^(2H)`. Evaluating a time density and taking the norm of the whole derivative vector are different operations.

### Incorrect Skorokhod trace

At T834 the correction is treated as a positive Hilbert–Schmidt norm square. For independent standard Gaussians X₁,X₂ and u=(X₂,−X₁), δu=0, whereas `E‖u‖²=2` and `E‖Du‖HS²=2`. The claimed equality gives 0=4. The genuine correction is a transpose pairing, equivalently `E tr((Du)²)`, which is −2 in this example. See [Privault, equation (1.2), PDF p.3](https://personal.ntu.edu.sg/nprivault/papers/moments.pdf).

T826–841 also uses time-local L² estimates for nonlocal fBM integrand norms; Hölder regularity of u does not control its Malliavin derivative. The exponent argument must be checked separately for H<1/2.

### Invalid projection step, not missing Fubini alone

T869 moves a terminal multiplier through predictable projection and substitutes the current-time derivative. For Y=W and φ=sin, the actual Clark–Ocone coefficient is

`E[cos W_t | F_s]=exp(−(t−s)/2) cos W_s`, s<t,

not `cos W_s`. The latter substitution would give `sin W_t=∫₀ᵗ cos W_s dW_s`, missing its nonzero drift. L2046 `ito_formula_with_clark_ocone` explicitly **assumes** the invalid general commutation as `hPS`.

T874–890 needs weighted Taylor remainder estimates, actual divergence domains, control of first-order covariance, time differentiation, and the identification of a random correction. Equality of means cannot be promoted to a random identity by Fubini. The initial value in the mean equation must be `Eφ(Y₀)`, unless Y₀ is deterministic. L1944's continuous-linear-map integral interchange does not justify interchange through an unbounded divergence without graph integrability.

L2021 `ito_formula_bounded` is a static divergence product identity. L2118 applies that algebra at each t without using the process decomposition. L2141 integrates it under supplied integrability assumptions. None proves `φ(Y_t)−φ(Y₀)` or derives the factor 1/2. L2207 `ito_from_leibniz_alone` still assumes `hChain_derived`.

Finally, the ordinary canonical Hilbert divergence of the fBM self-integrand does not exist for H≤1/4; extended divergence is a different operator. Thus T935–937's all-H square example needs a domain/operator change. See [Cheridito–Nualart, Ann. IHP 41 (2005), pp.1050–1051](https://www.numdam.org/item/AIHPB_2005__41_6_1049_0.pdf).

Minimal honest repair: separate the valid static divergence commutator from actual stochastic change of variables. A Brownian Itô theorem may be retained with its genuine quadratic variation and stochastic hypotheses; a Gaussian variance-correction formula may be stated with its own established divergence domain. Neither is a proof of the current universal theorem C. Any revision of C must be explicit and reviewed.

## B08 — the Gubinelli theorem has a first-chaos counterexample

T144–150 and T570–584 claim a remainder with second moment `O(|t−s|^min(4H,2H+1))` for `Y_t=E[F|F_t]` using the specified RKHS projected coefficient.

For H≠1/2, as required by the stated fBM theorem, take F=B_T^H and s=0. The proposed leading coefficient vanishes because P₀=0. Conditional-expectation duality gives

`E R_(0,t)² ≥ R_H(T,t)² / t^(2H)`.

As t↓0, this is of order `t^(2H)` if H<1/2, and `t^(2−2H)` if H>1/2, contradicting the claimed exponents. F belongs to every Malliavin Sobolev class. Extra second differentiability does not fix this.

As a separate diagnostic of the claimed uniform mechanism, at H=1/2 take F=W_T. Then DF=1_[0,T], the manuscript's coefficient would be `P_sDF=1_[0,s]`, and its inner product with `k_t−k_s=1_(s,t]` is zero. The resulting remainder has variance t−s, not `O((t−s)²)`. This Brownian diagnostic is outside main F's explicit exclusion of H=1/2; the preceding genuine fBM example is the direct counterexample to its stated range.

A true alternative is the Taylor-controlled path `Y_t=φ(B_t^H)` with bounded φ'': the scalar coefficient is φ'(B_s^H), and `E|R|² ≤ C|t−s|^(4H)`. That is a different theorem, not a repaired proof for arbitrary conditional-expectation martingales. It is optional to central E, and replacing F requires an explicit mathematical scope decision.

## B09 — formalization and mathematical-contribution claims

T1335–1442 must be rewritten only after author review, using the crosswalk. In particular:

- Full original Lean does not compile; the Foundation build does not import it.
- `log_sobolev_tensorization` (L2381) and `sobolev_embedding_from_hypercontractivity` (L2429) conclude `True`.
- The Gaussian LSI axiom has now been replaced in a separate verified integration copy by an exact **one-dimensional Gaussian** theorem. This is not an abstract curvature-dimension/Bakry–Émery theorem.
- Universal Gaussian Stein for arbitrary prescribed derivative data, assumed `leibniz_closure`, and false cancellation premises cannot certify their intended models.
- No verified Foundation theorem currently supplies Brownian predictable realization, the stochastic-volatility sensitivity/rigidity argument, the fBM/Gubinelli theorem, or the claimed time-indexed Itô formula.

Positive results must also be stated accurately. The rewrite genuinely constructs arbitrary finite polynomial cylinders in a countable Gaussian product, proves representation independence, IBP, closability, full adjoint identifications and divergence graph cores. It proves finite-dimensional Hermite spectral domains, one-dimensional Gaussian LSI, and one-site Poisson maximal adjoints. These are new formalization work on established mathematics; theorem names or operator-first exposition do not establish mathematical novelty. The rigidity statement's novelty needs a targeted literature check after its exact corrected statement is fixed.

## B10 — versions, moments, and examples

1. T506–520 and T1079–1114 must use a.e. time statements and a proved jointly measurable derivative version. Pointwise `σ_s∈D^{1,2}` alone does not supply the jointly predictable integrand used in a stochastic integral.
2. T957's smooth bounded SDE coefficients do not imply positive volatility: σ₀+W_t can cross zero. “Heston with bounded parameters” is not a sufficient positivity/Malliavin hypothesis. Give model-specific conditions or defer the examples explicitly.
3. The sensitivity formula at T1032–1038 needs an indicator/guard `r≤t_i`; an unguarded stochastic integral from r to t_i is not a definition for r>t_i.
4. Under the stated second-moment assumptions, M_T² need not lie in L². Let T=2, `Z=exp(3W₁²/16)`, σ_t=1 for t≤1 and σ_t=Z for t>1. Then σ is positive, progressive and in `L²(dt;D^{1,2})`, but `EZ⁴=∞`. Conditioning on F₁ shows `M₂=W₁+Z(W₂−W₁)` has infinite fourth moment. T1287–1308's square calculation needs additional moments or bounded smooth test functions.
5. “σ deterministic” means equality to a deterministic measurable function dt dP-a.e. under current assumptions. An every-time conclusion needs an additional continuous/version argument.
6. T238 says all examples use the natural filtration of X, while the volatility proof uses the natural Brownian filtration. If the revised paper requires the natural filtration of M throughout, prove its equivalence with the Brownian one under the positive-volatility hypotheses. Recovery through the observable quadratic-variation density and `W=∫(1/σ)dM` is an additional argument, not automatic from martingale representation. Alternatively state the Brownian filtration explicitly and disclose that scope choice.

## Nonblocking and optional questions

The standard adjoint-density theorem at T244–252 is true, but the proof repeats the desired density statement rather than deriving it. Use the usual graph orthogonality argument or cite the theorem with all hypotheses. This is an exposition issue distinct from the false main claims.

The Poisson all-L² representation at T446–462 is not refuted by absence of add-one L² regularity. For finite horizon and intensity, Mecke gives `λ∫E|F(η+δ_t)|dt=E[N_T|F|]<∞` by Cauchy–Schwarz. Thus the add-one difference is L¹. Begin IBP with bounded predictable tests, construct its predictable conditional expectation, and identify it with the L² PRP integrand. The displayed proof unjustifiably uses arbitrary L² tests without showing product integrability. The rewrite's one-site Poisson theorem is related, not a time-process realization. The all-L² theorem and a joint predictable version are given in [Last–Penrose, 2010 preprint, Theorem 1.1 and equations (1.3)–(1.5)](https://publikationen.bibliothek.kit.edu/1000015558/1182142).

The claim that sigma-algebra generation yields smooth M-cylinder graph density (T1053–55) needs a new analytic theorem; ambient density is insufficient. The corrected terminal rigidity argument avoids this obligation, without claiming it is solved.

The wild-defect conjecture at T1233–1235 already has an example under its current broad interpretation. For Brownian predictable J*, F=G=W_T gives defect `2(W_t−W_T)`. At 0<t<T it is not measurable with respect to W_T, whereas every polynomial in F,G,J*F,J*G at t is. Restrict the conjecture to a precisely chosen extended operator if something genuinely different is intended.

## Smallest defensible package

Retain the operator-first interpretation, the corrected representation theorem, domain-sensitive cylindrical calculus, weighted unitary transport, and the actual terminal/cylindrical rigidity result. Explicitly revise C and F rather than pretending the counterexamples are Lean implementation problems. Distinguish claims proved on paper using cited Brownian theory from claims verified in Lean. The completion plan gives a finite sequence of acceptance gates; no new formalization was started during this audit.

## Implementation update — 2026-10-12

The original audit above is preserved. Subsequent verified HEAD is
`30d3140f569cb7afc642e220a247949f052ae02f`; see `MATHEMATICAL_AUDIT.md` for exact new statements.

- **B01/B03, abstract part closed:** `Foundation/HilbertRepresentation.lean` proves the bounded-isometry representation, residual orthogonality, ambient-norm adjoint-domain criterion and projected-adjoint identity on its actual domain. PRP and Brownian realization are still separate inputs to the stochastic interpretation.
- **B05, transport ingredients closed:** `AdjointUnitaryTransport.lean`, `WeightedL2Transport.lean`, `WeightedAdjointTransport.lean` and `WeightedMeasurableTransport.lean` prove full-domain adjoint transport by actual multiplication/division and preservation of the actual measurable subspaces. No reciprocal bound or moment assumption is needed.
- **B05, Gaussian constant kernel closed:** `FiniteGaussianKernel.lean` and `InfiniteGaussianKernel.lean` prove that the full constructed closed derivative vanishes exactly on constant classes, including ordinary a.e. constancy in the countable product model.
- **B05, discrete rigidity proved:** `GaussianElementaryIntegral.lean` and `GaussianElementaryRigidity.lean` prove centering, isometry, actual sensitivity and rigidity for finite ordered independent coordinates with polynomial past coefficients. This does not discharge continuous-time theorem E.

Still blocking: time-Hilbert/Brownian realization, predictable integration and its completion, adapted graph approximation and genuine stochastic sensitivity. B06–B08 counterexamples and the required manuscript scope decisions are unchanged. Fixed discrete coordinate integration has no asserted full PRP; its range misses the first coordinate's second Hermite polynomial. No original manuscript was revised.

Verification: full build 4039 jobs; 1323 listed transitive axiom checks, covering all 110 new public declarations; only `propext`, `Classical.choice`, `Quot.sound`. No push.
