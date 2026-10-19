# Independent Banach reconstruction audit — Paper 2

**Verdict: RECONSTRUCTABLE WITH MAJOR CHANGES.**

Audit date: 2026-10-11. Repository baseline: **6d65f6d7472a8696f15fd97aa219c04621795661**. This is a mathematical investigation and source audit, not a new stochastic-calculus formalization. Ordinary mathematical proofs below are explicitly distinguished from Lean-checked results.

## 1. Executive conclusion

The sound organizing idea is to start with a **constructed stochastic integral between specified Banach spaces**, then form its continuous transpose and investigate its range, annihilator, and compatible restricted calculus. This can be a useful extension of the operator-first program.

The original implementation cannot serve as that foundation. Three interfaces are inconsistent: BanachEnergySpace, CompensatedIntegralAxioms, and, newly identified in this audit, PoissonRM. The original file compiles because its conditional proofs are valid under the hypotheses supplied; those hypotheses do not have the advertised concrete models.

Several manuscript claims also fail independently of these Lean defects:

- Global path-reflection parity does not annihilate all predictable stochastic integrals.
- Theorem B splits an integrable expression into terms whose expectations can be positive and negative infinity.
- The adjoint of the predictable Itô integral is confused with the full Malliavin derivative.
- Random predictable stochastic integrals are incorrectly confined to the first Poisson chaos.
- In the proposed stable model, the integral range meets L² only at zero. Consequently, the restricted factorization on Lp ∩ Lq is trivial after centering, since q > 2.
- Absence of the stable identity kernel from either individual Lp or L² space does not exclude it from the classical **sum space** used for compensated Poisson integration.

Substantial mathematics survives: genuine bounded Banach duality; a stable-scale integral isomorphism using classical decoupling; a closed proper range in Lp; explicit large-jump-count and annulus-count annihilators; a corrected deterministic-kernel theorem; and domain-sensitive jump differences. A more substantive replacement for the manuscript's recovery mechanism uses the nonlinear Lp duality map. None of these ordinary mathematical reconstructions has been implemented by this audit.

## 2. Exact sources and reproducibility

The sources actually inspected are:

- [Original Lean source](<C:/Operator/BanachLevyComplete (1).lean>), SHA-256 DF03519BB9EAF55AC107C1CFD565464E13EE32D35D10DCA4CB04DA4FA2DF76AB.
- [Original manuscript](C:/Operator/Banach.tex), SHA-256 A84988211A55B6A413FC7FE3FD5524436ADEC759DCB560229BCCA0F5EDA5FCDC.
- Existing BANACH_INTEGRATION_PLAN.md, AUTONOMOUS_OPERATOR_RESEARCH_REPORT.md and OPERATOR_DERIVATIVE_NON_GAUSSIAN_RESEARCH_AUDIT.md were consulted as prior claims to reassess, not as proof evidence.
- Relevant verified Foundation modules and the pinned Mathlib sources were inspected directly.

Pin: Lean 4.34.1; Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**.

Verification performed during this audit:

1. Full rewrite **lake build passed, 4,021 jobs**.
2. Direct Foundation/AxiomAudit.lean evaluation passed: **1,122 transitive axiom reports**, with the union of dependencies exactly propext, Classical.choice, Quot.sound.
3. The exact original Banach source, copied to a temporary file with audit commands appended, compiled successfully. Its three warnings are the existing deprecated import, unused simp argument and deprecated if_pos.
4. All **165 explicit named public declarations** in the original file were enumerated and their elaborated types checked: 39 definitions, 20 structures, 2 instances, 100 theorems and 4 lemmas. All **104 theorem/lemma declarations** received transitive #print axioms checks.
5. Four additional temporary contradiction proofs, reproduced below, compiled. Their axioms are also only the three standard foundational axioms.
6. Small Mathlib API probes were elaborated separately. These checks do not add project declarations.

Temporary reproduction evidence, retained for this session:

- C:\Users\ramir\AppData\Local\Temp\BanachIndependentOriginalAudit.lean
- C:\Users\ramir\AppData\Local\Temp\BanachIndependentOriginalAudit.log
- C:\Users\ramir\AppData\Local\Temp\BanachIndependentDeclarations.tsv
- C:\Users\ramir\AppData\Local\Temp\banach-reconstruction-root-axioms.log

The original audit can be reproduced by copying the original file, appending the examples below and #check/#print axioms commands, and running the installed Lake executable from the rewrite directory. No original, verified Lean source, or dependency pin was edited. No commit was made.

### Four different questions

1. **Kernel consistency:** an implication E → False is a theorem, not a contradiction in Lean.
2. **Consistency of a structure's fields:** E → False proves that E has no instance.
3. **Existence of a model:** even a consistent interface needs a construction for the claimed process.
4. **Informal correspondence:** a checked type may express much less than the theorem name or manuscript.

A clean axiom report answers none of questions 2–4 by itself.

## 3. Principal theorem inventory

Locations below refer to the exact original files above. Namespace prefixes are written where they matter. E denotes an explicit BanachEnergySpace parameter, not a constructed Banach model.

| Original declaration / location | Exact mathematical content of the elaborated type | Assessment and manuscript correspondence |
|---|---|---|
| ProbabilityTheory.poissonPMFRealSum, Lean 76; poissonPMF, 92; poissonMeasure, 99 | The weights exp(-r) r^n/n! sum to one; a PMF and its probability measure are constructed. | Genuine isolated probability construction. It redeclares Poisson infrastructure under names already available elsewhere in Mathlib; prefer Mathlib on migration. |
| poisson_mean_identity, 250; poisson_mean_hassum, 307; poisson_variance_identity, 325 | The weighted count series has mean r; the centered square series has value r. | Genuine series calculations. They are not a construction of a time-indexed random measure. |
| stableLevyDensity_symmetric, 123; stableLevyDensity_nonneg, 128 | The specified density function is even and nonnegative. | Valid pointwise facts, not a stable process or a measure-integral theorem. |
| stable_small_jump_moment_finite, 145 | c > 0 and a > γ imply 0 < 2c/(a-γ). | Arithmetic only: no measure, integral or finiteness conclusion. |
| stable_small_jump_moment_diverges, 150 | a < γ implies a-γ < 0. | Arithmetic only; does not prove divergence of a moment. |
| poisson_variance_pos, 154 | rate > 0 and T > 0 imply rate*T > 0. | Does not itself identify a variance. |
| ConcreteStableJumpCount.G₀_poisson, 437 | The identity map on ℕ under the chosen Poisson measure has that same law. | Consistent count model; does not identify this count with jumps of a constructed stable path. |
| TruncatedStableMeasure.second_moment_pos, 483; p_moment_ne_zero, 494 | Positivity/nonzero properties of explicitly defined real expressions. | No equality with an actual Lévy-measure moment. For p < γ, the alleged small-jump p-moment expression is negative while the actual integral diverges. |
| finite_telescope, 514; product_jump_leibniz, 547 | Finite telescoping; Δ(ab)=aΔb+bΔa+ΔaΔb for arbitrary real functions. | Genuine algebra. |
| compound_poisson_ito, 680; StableLargeJumpPath.ito_formula_large, 741 | An endpoint difference equals a finite telescope for supplied path values. | No stochastic law, differentiation, compensator or convergence theorem. |
| CompensatedIntegralAxioms, 771; ConstructedCompensatedIntegral.toAxioms, 893 | Supplied approximants, limits and universally quantified expectation/isometry conditions produce an integral interface. | Impossible conditions; see §4. Calling this a construction does not discharge those assumptions. |
| LevyItoDecomposition.trunc_convergence, 951 | Supplied scalar pairings of truncated integrals converge to a supplied full pairing. | Inherits the impossible compensated-integral interface. Not a proof of Lp convergence. |
| LevyItoDecomposition.ito_formula_decomposition, 967 | Assumes the displayed paired decomposition and returns the identical decomposition. | Proof is exactly the input hypothesis. No Itô formula established. |
| l2_cauchy_vanishes, 1145 | 2c ε^(2-γ)/(2-γ) tends to zero as ε ↓ 0 for 1 < γ < 2. | Genuine real limit. No integral difference is identified with this bound. |
| first_chaos_orthogonal, 1260; chaos_coeff_zero_iff, 1270 | A scalar multiple of a zero count-space pairing remains zero; division by a nonzero rate detects a zero coefficient. | No Poisson-space chaos expansion or completeness. poisson_inner, 1194, uses a totalized tsum on unrestricted functions; require summability/L² before analytic interpretation. |
| BanachEnergySpace.D, 1494; D_def, 1500 | pair (D F) u = holder F (δu). | Uses inconsistent mk_dual_spec; no bounded-functional construction. Manuscript definition 288 is repairable by actual continuous duality. |
| D_linear, 1509; D_const, 1518; ker_D_iff_annihilates_im_delta, 1526 | Linearity, vanishing on supplied constants, and D F=0 iff all supplied pairings with δu vanish. | Classical valid patterns after replacing E with real spaces and genuine pairings. Current instances impossible. |
| recovery_map_spec, 1595; fluctuation_factorization, 1607 | Given injectivity and F ∈ range δ, the chosen preimage maps to F. The centeredness argument in the latter is unused. | Right-inverse-on-range identity. No representation theorem, projection formula, closed range, or derivative-based recovery. Manuscript Theorem A, 390. |
| duality_recovery, 1622 | Given arbitrary F:LqΩ and unrelated F_Lp:LpΩ in range δ, concludes D_def for F and u. | F_Lp, its range proof and injectivity are unused. Does not prove manuscript identity with the recovered centered F. |
| even_annihilates_im_delta, 1700; even_in_ker_D, 1715 | If supplied sym says δ is odd and preserves pairings, any supplied even F annihilates δ. | Conditional parity algebra. The supplied δ_odd is false for general predictable integrands. Manuscript 731, 852. |
| representability_obstruction, 1747 | Even nonzero G, plus holder G G_Lp=0 → G=0, implies G_Lp ∉ range δ. | Valid abstract separation pattern under its inputs, but no genuine stable witness. Centering is not the engine of the argument. |
| injective_of_bounded_below, 1792; recovery_map_norm_bound, 1813 | A positive lower norm bound implies injectivity and the corresponding inverse bound on the range. | Classical salvageable arguments; current E is impossible. A closed-range proof additionally needs completeness. |
| derivation_iff_defect_zero, 1890 | The defined property LeibnizHolds is equivalent to its own definition. | Iff.rfl; not a new product theorem. |
| product_ito_paired_derived, 1944; product_rule_with_jump_defect, 1968 | Given LevyItoStructure, the supplied paired Itô decomposition and supplied module identification yield the defect identity. | Substantive decomposition is in fields ito_formula_paired and predictable_eq_module, 1920–1950. Does not justify manuscript Theorem B, 1215. |
| chaos_kernel_characterization, 2092 | Vanishing on H_det iff, for every u ∈ H_det, the scalar Φ_trunc pairing tends to zero. | Pointwise convergence of pairings only. Does not prove the manuscript's L^(γ') norm convergence, Theorem C, 940. |
| StableNoiseData, 2169; stable_noise_annihilates, 2264 | Assumed jump-count pairing, positivity and symmetry give the abstract obstruction. | Inherits impossible E and false general parity assumption. The asserted count variance is a field, not derived from a stable law. |
| StableLevyProcess, 2279; stable_levy_obstruction, 2289 | Given a package containing StableNoiseData, its designated count is outside its designated range. | No time-indexed stable process, characteristic law, filtration or stochastic integral is constructed by this wrapper. |
| HilbertEnergyData.leibniz_defect_vanishes, 2378 | Zero defect follows from the explicit defect_zero field, 2374. | Hilbert structure does not imply no jumps. The verified one-site Poisson Hilbert example already has a nonzero jump-product defect. |

Some representative elaborated signatures, with explicit arguments retained:

~~~lean
BanachEnergySpace.D_def (E : BanachEnergySpace)
    (F : E.LqΩ) (u : E.H_X) :
  E.pair (E.D F) u = E.holder F (E.δ u)

BanachEnergySpace.fluctuation_factorization (E : BanachEnergySpace)
    (h_inj : E.Injective_δ) (F : E.LpΩ)
    (hF_centered : E.expect_Lp F = 0)
    (hF_in_range : F ∈ Set.range ⇑E.δ) :
  E.δ (E.recovery_map h_inj F hF_in_range) = F

BanachEnergySpace.duality_recovery (E : BanachEnergySpace)
    (h_inj : E.Injective_δ) (F : E.LqΩ)
    (F_Lp : E.LpΩ) (hF_in_range : F_Lp ∈ Set.range ⇑E.δ)
    (u : E.H_X) :
  E.pair (E.D F) u = E.holder F (E.δ u)

BanachEnergySpace.representability_obstruction (E : BanachEnergySpace)
    (sym : E.DistributionalSymmetry) (G : E.LqΩ)
    (hG_even : E.IsEven sym G) (hG_nonzero : G ≠ 0)
    (hG_centered : E.expect_Lq G = 0) (G_Lp : E.LpΩ)
    (hG_selfpair : E.holder G G_Lp = 0 → G = 0) :
  G_Lp ∉ Set.range ⇑E.δ

BanachEnergySpace.product_rule_with_jump_defect (E : BanachEnergySpace)
    (li : E.LevyItoStructure) (F G : E.LqΩ) (u : E.H_X) :
  E.leibniz_defect_action li.toLeibnizStructure F G u =
    E.holder (li.product_jump_defect F G) (E.δ u)

BanachEnergySpace.chaos_kernel_characterization (E : BanachEnergySpace)
    (ts : E.TruncationStructure) (F : E.LqΩ) :
  (∀ u ∈ ts.H_det, E.holder F (E.δ u) = 0) ↔
  ∀ u ∈ ts.H_det,
    Filter.Tendsto (fun M => E.pair (ts.Φ_trunc M F) u)
      ts.truncFilter (nhds 0)
~~~

The universe-polymorphic elaborated types and all other explicit arguments were inspected in the compilation log. The abbreviation of universe parameters above changes no mathematical assumptions.

Two additional discrepancies matter for migration. `RepresentationProperty` (Lean 1579) asks for representation of **every centered Lp element**, whereas the manuscript later announces a restriction to Lp ∩ Lq; neither claim is proved by the preimage-selection definition. `ClosedRange_δ` (1585) is only a definition, not a closed-range theorem. Despite its name, `HilbertEnergyData` (2371) does not supply an inner-product-space instance: it supplies the desired zero-defect assertion.

## 4. Reproduced consistency defects

### 4.1 BanachEnergySpace: arbitrary functions are not continuous linear functionals

Lean 1428–1430 accepts every function H_X → ℝ as a dual element and requires evaluation to recover it. Lean 1419 requires homogeneity of the pairing in H_X. These assertions disagree at zero for the constant-one function.

The following minimal proof was Lean-checked after the untouched original:

~~~lean
example (E : BanachEnergySpace) : False := by
  have h := E.pair_smul_right (E.mk_dual (fun _ => 1)) 0 (0 : E.H_X)
  simp only [zero_smul, zero_mul, E.mk_dual_spec] at h
  exact one_ne_zero h
~~~

This is a quantifier/type error in the proposed dual constructor. Restricting to bounded linear functionals repairs the intended meaning. Use StrongDual ℝ H; its elements already contain linearity and continuity. The legacy type also lacks actual Lp identifications, pairing norm estimates, and completeness of the supposed Banach spaces.

### 4.2 CompensatedIntegralAxioms: arbitrary expectation and arbitrary norm

At Lean 780–781, centering is demanded for every functional 𝔼:(Ω→ℝ)→ℝ. At 783–785 the proposed square expectation equals every real norm_sq. Each is independently impossible:

~~~lean
example {Ω : Type*} (A : CompensatedIntegralAxioms Ω) : False := by
  exact one_ne_zero (A.I₁_centered 0 (fun _ _ => 0) (fun _ => 1))

example {Ω : Type*} (A : CompensatedIntegralAxioms Ω) : False := by
  exact zero_ne_one (A.I₁_isometry 0 (fun _ _ => 0) (fun _ => 0) 1)
~~~

The correct deterministic compensated-Poisson theorem is
E[I(h)]=0 and E[I(h)²]=∫h² dm for h∈L²(m), where I is constructed from a PRM of intensity m and expectation is integration against its actual probability measure. For predictable random integrands, replace the right side by E∫h² dtν and use the actual predictable L² space. A stable identity kernel z is outside that L² domain. No finite real norm_sq should be postulated for it.

### 4.3 Newly found: PoissonRM assigns all rates to the same law

Lean 188–190 asserts, for every B and every μB:NNReal,

    P.map (N B) = poissonMeasure μB.

The rate is not tied to an intensity measure of B. Choosing μB=0 and μB=1 gives different laws equal. This checked example proves the interface is uninhabited:

~~~lean
open ProbabilityTheory MeasureTheory

example {Ω : Type*} [MeasurableSpace Ω] (A : PoissonRM Ω) : False := by
  have h : poissonPMF 0 = poissonPMF 1 :=
    PMF.toMeasure_injective
      ((A.N_poisson ∅ 0).symm.trans (A.N_poisson ∅ 1))
  have h1 := congrArg (fun p : PMF ℕ => p 1) h
  change ENNReal.ofReal (poissonPMFReal 0 1) =
    ENNReal.ofReal (poissonPMFReal 1 1) at h1
  have hp : 0 < ENNReal.ofReal (Real.exp (-1)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  simp only [poissonPMFReal, NNReal.coe_zero, NNReal.coe_one, neg_zero,
    Real.exp_zero, pow_one, mul_zero, mul_one, Nat.factorial_one,
    Nat.cast_one, div_one, ENNReal.ofReal_zero] at h1
  exact ne_of_gt hp h1.symm
~~~

The names in this example are the Poisson definitions present in the original source. A corrected random-measure theorem must say N(B) has Poisson law with parameter m(B), for measurable B of finite intensity, and must construct independently scattered counts and countable additivity. StablePoissonRM inherits the current contradiction.

These are three impossible interfaces, with four independently checked contradiction proofs. They do not make Lean's kernel inconsistent.

## 5. Minimal sound operator architecture

### 5.1 The bounded layer needed by the manuscript

Let H be a real normed space, μ an actual measure, and p,q Hölder conjugates at least one. Given a genuine bounded map

    δ : H →L[ℝ] Lp ℝ p μ,

the integral pairing defines

    J : Lp ℝ q μ →L[ℝ] StrongDual ℝ (Lp ℝ p μ),
    J(F)(G) = ∫ F G dμ.

Define D(F)=J(F)∘δ. Then

    D(F)(u) = ∫ F·δu dμ,
    ‖D(F)‖ ≤ ‖F‖q ‖δ‖,
    ker D = {F : ∀u, ∫ F·δu dμ = 0}.

This construction requires neither Riesz nor reflexivity nor a theorem that every Lp functional is represented by an Lq element. On a probability space, if δ is centered, D kills constants. Full scalar Lp dual representation for 1<p<∞ permits calling this the entire transpose after identification; it is a separate theorem, not part of the constructor.

Pinned Mathlib already has the main machinery:

- ContinuousLinearMap.lpPairing and lpPairing_eq_integral, Mathlib/MeasureTheory/Function/Holder.lean:149,152.
- ContinuousLinearMap.mul, the real scalar bilinear multiplication.
- ContinuousLinearMap.precomp, Mathlib/Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean:217.
- ContinuousLinearMap.opNorm_comp_le.
- Holder.holderL and norm_holderL_le, for its norm estimate.
- Foundation/LpProducts.lean:66,75,84, for existing product, representative and norm facts if needed.

Use the existing lpPairing directly. Rebuilding it from the local lpMul would duplicate current Mathlib infrastructure.

### 5.2 A separate unbounded Banach layer

For a densely defined linear partial map T:Dom(T)⊂X→Y, define

    Dom(T*) = {y*∈Y* : x↦y*(Tx) is continuous on Dom(T)
                         with the norm inherited from X}.

Then T*y* is the unique continuous extension of that functional to X. Equivalently:

    (y*,x*)∈graph(T*) ⇔ ∀x∈Dom(T), x*(x)=y*(Tx).

Density of Dom(T) gives uniqueness; extension gives existence. Continuity in the **graph norm** would be the wrong condition: it would automatically admit every y*.

The adjoint is closed because the displayed graph is an intersection of closed equalizers. No inner product is involved. This is the correct Banach analogue of the verified Hilbert construction, but it is unnecessary overhead for the first bounded milestone.

Mathlib reuse:

| Purpose | Pinned declaration / file |
|---|---|
| Partial linear operator and graph | LinearPMap; Mathlib/LinearAlgebra/LinearPMap.lean |
| Closedness, closability, closure | LinearPMap.IsClosed, IsClosable, closure graph results; Mathlib/Topology/Algebra/Module/LinearPMap.lean:60,67,94–133 |
| Continuous extension from dense domain | ContinuousLinearMap.extend, extend_eq, extend_unique; Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Extend.lean:29,56,61 |
| Uniqueness on a dense set | DenseRange.equalizer; Mathlib/Topology/DenseEmbedding.lean:381 |
| Graph relation to partial map | Submodule.toLinearPMap_graph_eq; Mathlib/LinearAlgebra/LinearPMap.lean:1022 |
| Canonical bidual embedding | NormedSpace.inclusionInDoubleDual, inclusionInDoubleDualLi; Mathlib/Analysis/Normed/Module/DoubleDual.lean:58,87 |
| Weak-star topology | StrongDual.toWeakDual; Mathlib/Topology/Algebra/Module/Spaces/WeakDual.lean:115 |

The existing Hilbert adjoint construction in Mathlib/Analysis/InnerProductSpace/LinearPMap.lean:102–119 already demonstrates continuous extension, followed by a Riesz identification. Only the first step transfers unchanged.

### 5.3 Closability and double adjoints: necessary distinctions

For general Banach spaces the right criterion is

    T closable ⇔ Dom(T*) is weak-star dense in Y*.

Norm density is stronger and cannot be substituted. Example: T(x)n=(n+1)xn on ℓ¹ with domain Σ(n+1)|xn|<∞ is closed and densely defined. Its adjoint domain in ℓ∞ is {y:sup(n+1)|yn|<∞}; its norm closure is c₀, not ℓ∞.

If Dom(T*) is norm dense, the ordinary iterated adjoint acts X**→Y**, not X→Y. Under canonical embeddings jX,jY, the safe recovery statement is

    (x,y)∈graph(closure T)
       ⇔ (jX x,jY y)∈graph(T**).

To identify the full operators on the original spaces, require the appropriate reflexivity hypotheses and prove the identifications. Without norm density, use the adjoint relation or a weak-star preadjoint, not an arbitrary chosen extension.

Mathlib's Module.IsReflexive concerns **algebraic duals**; it is not Banach reflexivity. Use explicit surjectivity of inclusionInDoubleDual if necessary. See [Taylor, Outline of Functional Analysis, §8, Proposition 8.1](https://mtaylor.web.unc.edu/wp-content/uploads/sites/16915/2018/04/fctnl.pdf) for the reflexive unbounded-adjoint theorem.

Local reuse:

- Foundation/AdjointClosure.lean:12,19 and OperatorDomains.closed_graph_limit:40 use general graph topology and can inspire separate Banach lemmas.
- Pairing-limit proofs in AdjointClosure.lean:24,41 transfer with continuous evaluation.
- Foundation/Adjoint.lean and AdjointBidual.lean use Hilbert identifications; their statements must not be reused as Banach statements.
- Preserve all existing verified declarations; a later shared generalization can be separately reviewed.

## 6. A genuine symmetric stable realization

Fix T>0, 1<α<2, 1<p<α, q=p/(p-1), and a symmetric stable Lévy process L with characteristic function E exp(iξL_t)=exp(-t|ξ|^α), on its completed right-continuous natural filtration. All terminal Lp/Lq spaces below use the completed terminal sigma-field F_T^L, rather than an unspecified larger ambient sigma-field. Its jump measure has intensity dt ν(dz), ν(dz)=cα |z|^(-1-α)dz.

Take the closed predictable subspace

    H = Lp(Ω; Lα(0,T))pred,
    ‖u‖H = (E(∫₀ᵀ |u_t|^α dt)^(p/α))^(1/p).

It is reflexive and Banach. The stochastic integral must be constructed on elementary predictable processes, then extended. The classical decoupling argument gives

    c ‖u‖H ≤ ‖∫u dL‖p ≤ C ‖u‖H,

and convergence in the martingale S^p norm. A precise route is to introduce an independent copy L′. Conditional on the original path, ∫u(ω)dL′ has stable scale (∫|u(ω)|^α)^(1/α). Its p-moment is the corresponding deterministic stable moment. Two-sided decoupling compares this decoupled integral with the original adapted integral; density completes the construction. Do not assert that the original integral conditioned on its own integrand is stable.

The decoupling input is [Dirksen, 2014, equation (1.4) and Appendix A](https://arxiv.org/pdf/1208.3885). The argument above is a specialization, not an already compiled Lean theorem. The theorem also supplies the appropriate sum-space viewpoint for scalar compensated Poisson integrals.

Consequences, once the construction and estimate are proved: δ:H→Lp is bounded, injective, centered, and has closed range R; δ⁻¹:R→H is bounded. None is obtained merely from a field named stochastic_integral.

### 6.1 Finite pathwise quadratic variation, infinite mean

Banach.tex:468 says [L,L]T is almost surely infinite. This is false. Small-jump square sum has finite expectation T∫|z|≤1 z²ν(dz); the large-jump sum has finitely many finite terms almost surely. Therefore [L,L]T<∞ almost surely, while E[L,L]T=∞. The manuscript itself uses the correct small-jump fact at 1250.

### 6.2 Stronger domain obstruction: R ∩ L² = {0}

This ordinary mathematical theorem is crucial to the reconstruction.

Let u∈H and M_t=∫₀ᵗu_s dL_s. The S^p construction makes M a uniformly integrable martingale. If M_T∈L², then M_t=E[M_T|F_t] is square integrable, hence E[M]T=E M_T²<∞. But

    [M]T = ∫₀ᵀ∫ u_t² z² N(dt,dz),

and the compensator identity for nonnegative predictable functions gives

    E[M]T = E∫₀ᵀ∫u_t² z² ν(dz)dt.

The inner z-integral is infinite wherever u_t≠0. Thus it is finite only if u=0 dt⊗P-almost everywhere, whence M_T=0. This proves R∩L²={0}.

Since q>2 and P is a probability measure, Lq⊂L². Consequently:

- R∩Lq={0}.
- If F∈Lp∩Lq and F−EF∈R, then F is constant.
- Manuscript restricted factorization, Banach.tex:695, is therefore trivial on its announced stable domain.
- The useful isomorphism is H≅R⊂Lp. The useful bounded adjoint has source Lq. These are different spaces; one cannot insert a general represented F into D.

This does not invalidate the bounded transpose. It invalidates the claimed direct recovery interpretation on the overlapping domain.

### 6.3 Large-mark truncation has an explicit estimate

For M>0 and H-predictable u, the scalar martingale p-estimate for the compensated large-jump integral gives

    ‖δu−δᴹu‖p^p
      ≤ C_p E∫₀ᵀ|u_t|^pdt · ∫|z|>M |z|^pν(dz)
      ≤ C T^(1−p/α) M^(p−α) ‖u‖H^p.

Here ∫|z|>M |z|^pν(dz)=2cα M^(p−α)/(α−p). The time estimate is ordinary Hölder. Thus δᴹ→δ in operator norm H→Lp. This repairs Banach.tex:913–934 using an actual tail moment, rather than calling the tail process stable. The truncated integral for arbitrary H inputs must be defined through Lp integration; random u∈H need not lie in L²(dt⊗P).

For the martingale estimate, see [Marinelli–Röckner, Theorem 3.2 and its 1≤p≤2 specialization](https://arxiv.org/pdf/1308.2648): the p-th maximal moment is bounded by the expected integral of the p-th power of the predictable jump integrand. Its §3 also records the scalar sum/intersection-space distinction used below. The stable tail calculation displayed here is the specialization with integrand u_t z 1{|z|>M}.

### 6.4 The two-parameter integral is not excluded by infinite variance

For 1<p<α<2, the stable kernel z splits as

    z = z 1|z|≤1 + z 1|z|>1.

The first part is in Lp(Ω;L²(dtν)); the second is in Lp(Ω×(0,T)×ℝ, Pdtν). Their sum belongs to the classical scalar compensated-Poisson sum space, even though z belongs to neither individual global space. On a finite time interval both displayed norms are finite for this deterministic kernel.

Therefore the blanket exclusions at Banach.tex:1082–1090 and 1453–1467 are false as claims about all legitimate two-parameter Lp stochastic integration. A narrower claim in the separate companion paper would require a separate audit; no finding about its complete theorem is asserted here.

## 7. Corrected representability obstruction — complete ordinary proof

### 7.1 The false reflection argument

If Rω=−ω, then

    (∫u dL)∘R = −∫(u∘R)dL,

not generally −∫u dL. Predictability is preserved by reflection, but this does not make u invariant.

A counterexample exists within the very stable setting and with a bounded test functional. Fix 0<s<T, A=L_s, Y=L_T−L_s. Put

    u_t = sign(A) 1(s,T](t),
    F = sign(A) sign(Y).

Stable increments are independent, symmetric, continuous in law and integrable. F is bounded, centered and even under global reflection. Yet

    E[F δu] = E[sign(A)²] E|Y| = E|Y| > 0.

Thus F∈Lq and D F≠0. This directly refutes “all even centered functionals lie in ker D” (Banach.tex:122,852 and Lean δ_odd-based interpretations). No change of dual-space notation repairs that claim.

### 7.2 A valid explicit annihilator

Under the stable setup in §6, let ψ be a bounded, nonzero, even Borel function supported in {|z|>1}, with ∫ψ²dν>0. Define

    Gψ = ∫₀ᵀ∫ψ(z) N(dt,dz) − T∫ψ(z)ν(dz).

Then:

1. Gψ is centered and belongs to every finite Lr; bounded marks and a finite Poisson count give all moments.
2. E Gψ²=T∫ψ²dν>0.
3. For every u∈H, E[Gψ δu]=0.
4. Therefore D Gψ=0 and Gψ∉R.

Proof of item 3: first let u=Σ ξ_i 1(t_i,t_i+1], with bounded F_t_i-measurable coefficients. Write Gψ as the sum of its centered increments. Terms before t_i vanish after conditioning because ΔL_i is centered; terms after t_i+1 vanish by independent centered future increments. On the same interval, the joint compensated-Poisson covariance is

    E[ΔGψ,i ΔL_i] = (t_i+1−t_i)∫ψ(z)zν(dz)=0.

The covariance exists: ψ is bounded away from the small-jump singularity and ∫|ψ z|ν<∞ because α>1. It can also be proved by splitting off the independent small-jump integral and applying the elementary compound-Poisson sum calculation to the large jumps. The bounded past coefficient factors out using independent increments. Summing yields zero.

Approximate arbitrary u∈H by bounded elementary predictable u_n. The established upper integral bound gives δu_n→δu in Lp. Since Gψ∈Lq, Hölder gives E[Gψ δu_n]→E[Gψ δu]. This completes the proof, including integrability.

If Gψ=δu, item 3 would imply E Gψ²=0, contradicting item 2. This proof requires no full martingale representation theorem and no closed-range hypothesis.

For ψ=1|z|>1 the witness is the centered large-jump count. For ψ_k=1{k<|z|≤k+1}, disjoint Poisson increments give a linearly independent family of full annihilators. This saves a stronger explicit statement than mere failure of surjectivity, while withdrawing the incorrect general parity assertion.

### 7.3 Alternative proof by uniqueness of jump integrands

If the same count were δu, uniform integrability and terminal equality would imply equality of the whole martingales. Their jumps would satisfy

    u_t ΔL_t = 1|ΔL_t|>1.

Compensation of the nonnegative indicator of discrepancy then forces

    u_t z = 1|z|>1 for dt⊗P⊗ν-almost every (t,ω,z).

The right side vanishes on a positive-measure small-mark annulus, forcing u_t=0; it equals one on the large-mark set, a contradiction. This uses uniqueness of the predictable compensated-jump representation through jump equality, not an assumed full PRP or a terminal equality between arbitrary local martingales. Without a true/UI martingale class, terminal equality alone would be insufficient.

For more general range characterizations, let K_F be the unique predictable mark kernel representing the martingale E[F|F_t]−EF in a properly constructed marked integration space. Then F−EF∈R iff K_F(t,z)=u_tz for some u∈H. Existence, uniqueness and norm compatibility of K_F remain analytic/formal prerequisites; they are not obtained from the abstract adjoint.

## 8. Repairing the deterministic-kernel theorem

Banach.tex:940 assumes only F∈L² but later applies an Lq bound with q>2. The pairing can fail to exist. For α−1≤r<α/2, take F=sign(L_T)|L_T|^r. Then F∈L² but F L_T=|L_T|^(r+1) is not integrable. The deterministic test u=1 already invalidates the announced domain.

A corrected theorem can take F∈Lq. Then F∈L² and has a Poisson first-chaos kernel f₁. For bounded deterministic time tests u, the truncated L² pairing gives

    E[F δᴹu] = ∫₀ᵀu(s) Φ_M(s)ds,
    Φ_M(s)=∫|z|≤M f₁(s,z) z ν(dz).

This initially follows on L²∩Lα time tests. Boundedness and density extend it to Lα, producing Φ_M∈L^(α′). The operator-norm tail estimate in §6.3 yields

    ‖Φ_M−Φ‖α′ ≤ ‖F‖q ‖δᴹ−δ‖Hdet→Lp → 0,

where Φ represents the restricted adjoint on deterministic Lα. Thus vanishing against all deterministic tests is equivalent to Φ=0 and to Φ_M→0 in that norm.

This is a genuine repair with stronger explicit F-integrability and a new norm estimate. It is not what Lean chaos_kernel_characterization proves. Pointwise convergence of dual pairings alone does not imply norm convergence.

Higher-chaos elements that also belong to Lq annihilate deterministic integrals, by the truncated chaos calculation and the Lp limit. They do not all annihilate random predictable integrals. The assertion R⊂C₁ is already refuted by δ1=L_T∉L², since the stated C₁ is an L² chaos; random integrands create further chaos orders even in finite-variance models. The corrected count-annihilator proof in §7 handles the particular first-chaos witnesses without this confusion.

There is an explicit higher-chaos counterexample on the same stable space. Let k(z)=z 1{1<|z|≤2}, and let A and B be its compensated integrals over (0,s] and (s,T], respectively. They are independent centered first-chaos variables with all finite moments. Then F=AB is a second-chaos variable (the time supports are disjoint), belongs to Lq, and is even under global reflection. The predictable u=A 1(s,T] belongs to H and satisfies

    E[F δu] = E[A²] (T−s) ∫ k(z)z ν(dz) > 0.

All factors are integrable by the bounded-annulus moment bounds and Hölder. Thus even the stronger proposed higher-chaos annihilation fails for the full predictable adjoint.

## 9. Product rules, chain rules and the Itô/Malliavin distinction

### 9.1 Theorem B is not a finite real expectation identity

Take f(x)=arctan x, g=1 and u_t=f′(L_t−)=1/(1+L_t−²). Both functions meet C_b²; u is bounded, predictable and belongs to H. Let M=∫u dL.

M_T∈Lp but M_T∉L² by §6.2, since u is nonzero. The first “predictable Leibniz contribution” in Theorem B is E[M_T²]=∞. On the other hand, E[f(L_T)M_T] is finite by boundedness of f. In the pathwise Itô identity,

    J_f(T) M_T = (f(L_T)−f(0))M_T − M_T²,

the other expectation is −∞. The finite sum cannot be split into these two real expectations. This refutes the asserted integrability at Banach.tex:1191–1200,1215–1234,1290–1300. Passing through bounded-jump truncations would need uniform integrability, which this example prevents.

The pathwise Itô formula and its a.s. convergent jump remainder remain valid. The word “compensated” for the raw jump remainder also needs correction: the displayed sum itself is not centered.

A corrected paired theorem must impose and prove separate integrability of the split terms, restrict the testing class, or work with a different well-defined combined expression. None should retain the old theorem name while silently changing its domain.

### 9.2 Predictable Itô adjoint versus full Malliavin difference

The manuscript's space at 1375 is predictable L²(dtνdP), and its integral is a bounded isometry. Its adjoint is therefore everywhere bounded on scalar L² and has predictable values. The raw add-one derivative is generally nonpredictable and unbounded on L². They cannot be the same operator.

For a rate-λ Poisson process and F=(N_T−λT)²:

    raw add-one derivative = 2(N_T−λT)+1,
    predictable Itô adjoint = 2(N_t−−λt)+1.

The latter is the predictable conditional projection of the former. Similarly, on Brownian space, the Itô adjoint sends B_T² to 2B_t, whereas the Malliavin derivative is 2B_T.

Thus the identification in Banach.tex:1399–1413 and the ensuing product theorem must be withdrawn as written. The verified rewrite's full Gaussian divergence/Malliavin operator pair and one-site Poisson difference/divergence pair should be preserved; a predictable-integral transpose is a separate construction with a separately proved relationship.

### 9.3 What jump calculus does survive

For a genuine add-one map θ_e and Δ_eF=F∘θ_e−F,

    Δ_e(FG)=F Δ_eG+G Δ_eF+(Δ_eF)(Δ_eG),

and

    Δ_e φ(F)=φ(F+Δ_eF)−φ(F).

These are exact algebraic identities. For a C¹ scalar φ, subtraction of φ′(F)Δ_eF gives the actual nonlinear remainder; a C² bound gives |remainder|≤(‖φ″‖∞/2)|Δ_eF|² when applicable.

Three independent analytic tasks remain: representative independence under add-one, integrability of every term, and membership of FG or φ(F) in the actual closed difference domain. F,G∈L⁴ and ΔF,ΔG∈L² alone do not justify all L² products or FG-domain membership. The manuscript's finite-variance proposition assumes the add-one formula for FG before establishing that membership.

Verified one-site reuse:

- PoissonMultipliers.scalarMul_mem_domain and its shifted/expanded product formulas.
- PoissonMultiplierAlgebra.difference_commutator.
- PoissonLipschitzChain.composition_mem_domain and composition_difference_apply.
- PoissonQuadraticDefect.bounded_square_difference.
- LpProducts for the required Hölder exponents.

The algebra and Hölder estimates generalize. Positive singleton evaluation, the count-shift formulas, λ scaling and one-site graph-core proofs do not automatically generalize to a space-time PRM. In particular, the condition “g bounded” implies bounded one-site difference, but that does not itself supply all space-time integrability over an infinite intensity.

A terminal F does not preserve predictability when multiplying u. The abstract module action on {u:Fu∈H} need not be bounded in the original H norm, so it need not define an element of H*. A correct Banach module action starts with a proved bounded multiplier M_F:H→H and its transpose. Hilbert geometry does not remove this requirement.

## 10. Literature, formalization reuse and novelty

The categories below distinguish A: classical mathematics with Lean infrastructure located; B: classical mathematics for which the required complete Lean realization was not located; C: formulation/synthesis; D: potential new theorem requiring separate novelty work; E: false or unsupported.

| Result / comparison | Category and evidence |
|---|---|
| Continuous transpose, Hölder pairing, canonical bidual embedding | A. The pinned Mathlib declarations in §5 already implement the bounded foundation. An operator-first order of exposition is not a new theorem. |
| General unbounded Banach adjoint/domain and reflexive bidual theorem | B for the complete target layer at this pin. General graph and extension infrastructure exists; the Hilbert proofs cannot replace the Banach separation argument. Taylor §8 gives the classical theorem. |
| Derivative as adjoint of nonanticipating integral | Classical prior art: Di Nunno–Rozanov, §4.1 explicitly defines this adjoint. Their §5.2/Theorem 16 separates the anticipating extension. C at most for the proposed organization; B for a complete corresponding Lean implementation located here. [Primary preprint](https://abelsymposium.no/symp2005/preprints/dinunno.pdf). |
| Pathwise functional derivative and martingale-integral inverse | Cont–Fournié, Theorems 5.8–5.9 and §6, connect a closable functional derivative, Itô adjoint and predictable Malliavin projection. This is different from a purely abstract transpose and supplies prior art for operator-based recovery. [Primary paper](https://arxiv.org/abs/1002.2446). |
| Poisson integration and Banach stochastic duality | Classical extensive theory; Dirksen–Maas–van Neerven, “Poisson stochastic integration in Banach spaces” (2013): Theorem 5.6 gives closability, Lemma 5.7 a cylindrical core, Theorem 5.10 identifies divergence with the stochastic integral on adapted integrands, and Theorem 6.6 gives Clark–Ocone via predictable projection. [Primary preprint](https://arxiv.org/abs/1307.7901). |
| Add-one product/duality calculus | Classical, not created by Banach dualization. Picard's 1996 Poisson duality paper is direct prior art. Local one-site formalizations provide verified examples, not a full PRM construction. [Primary paper](https://www.numdam.org/item/AIHPB_1996__32_4_509_0/). |
| Stable-scale estimate, tail control, marked sum spaces | Classical estimates and their scalar specializations. The stable realization remains a large Lean obligation. The independent-copy argument must be matched to the precise decoupling hypotheses. |
| Explicit count/annulus obstruction and R∩L²={0} | B/C. Ordinary proofs are supplied here from classical martingale facts; no novelty claim is established. Their clean formulation may be useful in a verified operator-domain library. |
| Quotient duality and nonlinear Lp recovery (§11) | Classical functional analysis combined with a process-specific range; C. A new quantitative range/approximation result could become D, but none has been shown novel in this audit. |
| Universal parity kernel, first-chaos range, Theorem B as stated | E. Explicit defects/counterexamples above. |

### Public Lean infrastructure newly located

[slink/LeanLevy](https://github.com/slink/LeanLevy), inspected at commit **7e73fd9b23ad52956ec2756a815889a783131ce4**, dated **2026-07-15**, uses Lean **4.32.0** and an MIT license. Selected actual source bodies were read, rather than relying only on its README:

- [PoissonPointFamily.lean](https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean): IsPoissonPointFamily:209 and exists_isPoissonPointFamily:227 construct counts and marks with the rate tied to the intensity.
- [PoissonCompensated.lean](https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonCompensated.lean): integral_compensatedPoissonSum:334, integral_sq_compensatedPoissonSum:379, compensatedPoissonIntegral:699, eLpNorm_compensatedPoissonIntegral:761, integral_compensatedPoissonIntegral:817 and compensatedPoissonIntegral_eq_sum:832.

The last operator has source Lp ℝ 2 m: **deterministic mark functions**, not arbitrary random predictable integrands. These files are credible reuse candidates, not evidence that the complete stable predictable Banach theory is already formalized. This audit did not build that external repository or audit its complete transitive dependencies. Port compatibility from 4.32.0 to the pinned 4.34.1, licensing and theorem assumptions must be checked before reuse; no dependency was added.

No complete public Lean implementation of the particular stable Banach adjoint/range theory was located in the scoped search. That is a search result, not an assertion of global absence.

## 11. Strongest realistic Paper 2 target

A defensible revised paper can center on the following package:

1. Construct the stable predictable integral δ:H→Lp and prove the two-sided bound.
2. Prove its range R is closed and proper, R∩L²={0}, and produce an infinite family of explicit all-moment annihilators.
3. Construct D:Lq→H* by genuine Hölder duality; prove ker D=R⊥. With scalar Lp dual representation and Hahn–Banach, D is onto H*, and Lq/ker D is isomorphic to H* with the appropriate norm bounds.
4. Give a recovery/approximation theory that respects the asymmetric domains.
5. Treat full add-one Malliavin calculus and its restricted relation to D as a separate result.

For item 4 there is a mathematically substantive classical replacement. Let

    Jp(F)=|F|^(p−2)F ∈ Lq, with Jp(0)=0,
    A(u)=D(Jp(δu)).

Then ⟨A(u),u⟩=‖δu‖p^p≥c^p‖u‖H^p. Strict convexity, reflexivity and the bounded-below integral imply that minimization of

    (1/p)‖δu‖p^p − ℓ(u)

has a unique solution for every ℓ∈H*, giving A(u)=ℓ. Thus, for F∈R,

    u = A⁻¹(D(Jp(F))),    δu=F.

For arbitrary F∈Lp the unique best approximation δu∈R satisfies

    D(Jp(δu−F))=0.

This is a valid nonlinear Banach normal equation. It reduces to the familiar linear Hilbert normal equation when p=2; it does not assert that D(F) is defined for arbitrary F∈R. The construction is known convex/duality machinery, so mathematical novelty would require a sharper new theorem—such as quantitative stability, an explicit process-specific range criterion, or a new comparison between the restricted adjoint and marked derivatives. A carefully verified realization would already be a valuable formalization contribution.

Ranked targets: (i) consistent concrete duality; (ii) genuine Poisson model reuse; (iii) stable range/annihilator theorem; (iv) nonlinear recovery; (v) restricted jump calculus. Rebuilding all general semimartingale theory before these targets would be an inefficient starting point.

## 12. Incremental Lean roadmap

Each milestone must compile independently, use actual spaces, prove model existence when claiming a realization, and receive a transitive axiom audit. None authorizes editing Paper 1 or legacy claims without a separate correspondence review.

### B0 — Bounded Banach derivative through the existing Hölder pairing

**Statement.** For actual μ, conjugate p,q≥1 and δ:H→L[ℝ]Lp ℝ p μ, construct a continuous linear D:Lp ℝ q μ→StrongDual ℝ H. Prove evaluation, ‖DF‖≤‖F‖‖δ‖, and its annihilator-kernel equivalence.

**Reuse.** Mathlib lpPairing, lpPairing_eq_integral, precomp, operator norms; local LpProducts only where useful.

**Construction.** Compose the existing scalar pairing with precomposition by δ. No separately axiomatized dual type.

**Risk/difficulty.** Low mathematics, low-to-moderate Lean API work. Check HolderConjugate orientation and scalar norm simplification.

**Acceptance.** Exact actual-Lp integral formula; genuine integrability; all norms proved; no stochastic representation fields, no new dependency, no legacy import. A trivial bounded map is a concrete model, and the constructor accepts every real bounded δ.

### B1 — Optional general Banach partial-operator layer

**Statement.** For a dense-domain LinearPMap, construct T* with the graph formula in §5 and prove closedness. Later prove the graph-annihilator characterization and weak-star closability criterion.

**Reuse.** LinearPMap, continuous extension, dense equalizer and Hahn–Banach separation. General graph proofs from Foundation/AdjointClosure are patterns; AdjointBidual is not a Banach theorem.

**Construction.** Continuous duals and ambient-domain continuity, or a closed single-valued relation. Biduals retain canonical embeddings.

**Risk/difficulty.** Moderate for existence/closedness; high for separation and weak-star theory. Norm density and graph-norm continuity are dangerous substitutions.

**Acceptance.** Exact domains, uniqueness and values; no Riesz; reflexivity explicit only where needed. This work may run after B0 and need not block the bounded stochastic example.

### B2 — Concrete Lp/domain and restricted-duality infrastructure

**Statement.** Formalize scalar Lq-to-Lp-dual representation at 1<p<∞ on the chosen probability space when required; prove centered-kernel and quotient/range consequences for genuine bounded maps. Formalize only multiplier actions with proved boundedness on H.

**Reuse.** Mathlib Lp, Hölder, Bochner integral, dual extension/separation; local LpProducts, OperatorDomains and MultiplierCore ideas.

**Construction.** Actual centered subspaces, quotients and canonical pairings. Do not encode representation as a field called lp_duality.

**Risk/difficulty.** Pairing is already B0; surjectivity/reflexivity/quotient theory is a larger analytic obligation.

**Acceptance.** Distinguish an embedding into the dual from onto dual representation. Prove all product exponents and all relevant dense-domain conditions.

### B3a — Real Poisson random measure and elementary marked integration

**Statement.** Construct a PRM with intensity dtν; on deterministic and elementary predictable finite-intensity kernels prove centering, covariance and the L² isometry.

**Reuse.** Mathlib Poisson laws and independence; inspect/port selected LeanLevy files at the cited commit; local PoissonMoments and one-site formulas serve only isolated checks.

**Construction.** Actual counts, joint independence, filtration, predictable elementary processes and their stochastic sums.

**Risk/difficulty.** High, but far smaller than a full stable theory. Deterministic mark integrals must not be advertised as arbitrary predictable integration.

**Acceptance.** A concrete model, rates equal intensity, n=0/empty-set behavior correct, integral isometry derived from independence. Axiom audit follows the complete imported chain.

### B3b — Stable predictable Lp integral

**Statement.** For the normalized symmetric α-stable model and 1<p<α<2, construct δ:H→Lp with the two-sided stable-scale estimate, centering and S^p approximation.

**Reuse.** B3a plus genuine stable-law construction, scalar martingale estimates and decoupling. No complete ready-made Mathlib theorem was located for this combination.

**Construction.** Large/small jump limits, bounded elementary predictable density in H, independent-copy law and decoupling, then completion.

**Risk/difficulty.** Very high; this is the principal formalization cost. Do not insert a claimed integral isomorphism as an unchecked assumption.

**Acceptance.** Actual process/integral and normalization, both estimates, true martingale property, exact domain. Infinite variance must appear as a proved exclusion from L², not a totalized moment calculation.

### B4 — Range, explicit annihilators and deterministic adjoint

**Statement.** Prove closed R, R∩L²={0}, the centered count/annulus annihilators and nonrepresentability. Prove operator-norm large-mark truncation, then the corrected deterministic-kernel theorem for F∈Lq.

**Reuse.** B0, B3, independent increments, Poisson moments, compensation and the explicit tail estimate.

**Construction.** The actual Gψ witness, its positive variance and integrability; elementary-predictable pairing followed by density.

**Risk/difficulty.** Moderate ordinary mathematics, high Lean work because process infrastructure is substantial. No full PRP is required for the count theorem.

**Acceptance.** Gψ is a concrete random variable; DGψ=0 and Gψ≠0 proved; no δ_odd field or higher-chaos substitution; dual norm convergence is proved as such.

### B5 — Separate nonlinear recovery and domain-sensitive calculus

**Statement.** First prove abstract δ*Jpδ recovery for a bounded-below map into Lp on a reflexive domain, or the normal equation for best range approximation. Separately prove genuine add-one product/chain rules on explicit integrable domains and any predictable projection relation.

**Reuse.** Convexity, duality and minimization infrastructure; local Poisson multiplier/Lipschitz results as model examples; existing Hölder bounds.

**Construction.** Actual duality map and minimizer, or actual add-one transformations. Anticipating divergence and predictable Itô integral receive different definitions.

**Risk/difficulty.** High. Neither ambient density nor a pointwise algebraic expansion proves closed-operator domain membership.

**Acceptance.** Same actual operator throughout; all split integrals finite; every domain/product claim proved; no Gaussian chain rule imposed on jumps.

### B6 — Exact manuscript correspondence

**Statement.** For every published claim, identify a checked theorem with matching hypotheses, types, normalization and scope.

**Reuse.** The independent inventories and axiom logs, not the old “Proved” labels.

**Construction.** A source-to-theorem table with explicit withdrawals and corrected theorem names.

**Risk/difficulty.** Moderate editorial work after mathematical milestones; rewriting before B3/B4 would obscure what remains unproved.

**Acceptance.** No claim that B0 formalizes a stable process, no claim that predictable adjoint equals full Malliavin derivative, no abstract result presented as a concrete instance.

## 13. Exact first Sol Medium task

Create **Foundation/BanachLpAdjoint.lean**, implementing **B0 only**.

Use the following mathematical interface (ordinary Lean universe parameters may be inferred):

~~~lean
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul

open scoped ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω]
variable {μ : MeasureTheory.Measure Ω} {p q : ℝ≥0∞}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable [ENNReal.HolderConjugate q p]

noncomputable def boundedBanachDerivative
    (δ : H →L[ℝ] MeasureTheory.Lp ℝ p μ) :
    MeasureTheory.Lp ℝ q μ →L[ℝ] StrongDual ℝ H :=
  (δ.precomp ℝ).comp
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p)
~~~

Prove, under exactly these assumptions:

1. The defining product F·δu is integrable.
2. boundedBanachDerivative δ F u = ∫ω, F ω * δ u ω ∂μ.
3. ‖boundedBanachDerivative δ F‖ ≤ ‖F‖ * ‖δ‖.
4. boundedBanachDerivative δ F=0 iff every displayed integral is zero.
5. Optionally, under an actual probability measure and proved centering of δ, its value on actual constant Lq functions is zero.

Import Mathlib.MeasureTheory.Function.Holder and use the existing lpPairing. Do not rebuild a generic pairing framework; do not import the old Banach source. Completeness of H, reflexivity, a stable process and scalar-dual surjectivity are not needed for these results. Add this future module to the root and axiom audit only when implementation is authorized; run a full build and do not commit without explicit authorization.

The constructor, integral evaluation and pointwise norm estimate were checked in an isolated temporary Lean API probe during this audit. They have not been installed as a new Foundation module; completing the listed lemmas, naming and project integration remains the first implementation task.

## 14. Explicit corrections or withdrawals required

The original files were not edited. Before a revised manuscript can claim verification, it must:

1. Replace mk_dual and the impossible stochastic interfaces; withdraw concrete-verification claims based on them (Lean 178,771,1345; TeX 1579 onward).
2. Correct the claims that moment arithmetic and telescoping already formalize stable moments and Itô stochastic integration (appendix table, TeX 1720 onward).
3. Withdraw universal reflection oddness and the corresponding “all even” kernel statements (TeX 122,780–792,852–855).
4. Retain the count obstruction only with a new independent-increments/compensation proof (§7).
5. Correct pathwise quadratic variation versus its expectation (TeX 468).
6. State stable two-sided estimates with an exact classical theorem and derivation, then identify them as unformalized until B3b.
7. Move nontrivial range recovery to Lp and explain the Lq-domain mismatch; the announced restricted Lp∩Lq factorization is constants only (TeX 695).
8. Withdraw Theorem B's finite-expectation claim and the assertion that pathwise cancellation justifies separate expectations (TeX 1141,1215,1288).
9. Withdraw R⊂C₁, the full predictable higher-chaos annihilator, and the weak-to-strong limit argument; add F∈Lq and the explicit tail norm estimate for any corrected deterministic theorem (TeX 885,940–1078).
10. Separate predictable Itô adjoint, raw Malliavin difference and anticipating divergence; remove the false identification and insufficient product-domain conditions (TeX 1399–1437).
11. Correct “Hilbert implies no jumps/ordinary Leibniz.” Hilbert geometry and diffusion locality are independent (Lean 2371; TeX 1339–1345).
12. Replace arbitrary terminal multiplication by proved integrand multipliers. A partially defined functional is not automatically an element of H* (TeX 1108).
13. Correct the non-Hilbert argument: containing deterministic Lα(0,T) proves failure of Hilbert isomorphism for T>0. “Not Hilbert, therefore not isomorphic to its dual” is not a valid general inference. A separate type/cotype argument is needed for this particular H; a quotient is not automatically an embedded subspace (TeX 606–634).
14. Withdraw blanket claims that the stable identity is excluded from all legitimate two-parameter Poisson Lp norms; account for classical sum spaces (TeX 1082,1453).
15. Describe remaining novelty as a proposed synthesis/formalization target until a specific new quantitative theorem is established.

**Recommendation:** reconstruct Paper 2 around genuine Banach duality, a correctly constructed stable integral, explicit range/annihilator results and, if desired, nonlinear duality-map recovery. Start with the small B0 module above. The old interfaces and theorems should be treated as an audited specification with documented failures, not as a migration-ready library.

