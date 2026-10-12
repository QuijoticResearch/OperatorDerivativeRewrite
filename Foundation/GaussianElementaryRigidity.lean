import Foundation.GaussianElementaryIntegral
import Foundation.FiniteGaussianKernel

/-!
# Finite Gaussian elementary sensitivity and rigidity

The coefficients are actual polynomials in earlier independent coordinates.
Differentiating their genuine increment sum gives a coefficient plus another
elementary integral. If its full closed Gaussian gradient equals the coefficient
field, the elementary isometry forces every coefficient to be constant.

This is a finite ordered-coordinate theorem, not continuous-time Brownian
stochastic-volatility rigidity or an assumed stochastic sensitivity rule.
-/

noncomputable section
open MeasureTheory MvPolynomial
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*}

/-- Differentiating a polynomial introduces no new coordinate dependence. -/
theorem pderiv_vars_subset (p : MvPolynomial ι ℝ) (k : ι) :
    (pderiv k p).vars ⊆ p.vars := by
  classical
  intro j hj
  obtain ⟨d, hd, hjd⟩ := (mem_vars_iff_mem_support j).mp hj
  have hc := mem_support_iff.mp hd
  rw [coeff_pderiv] at hc
  have hp : d + Finsupp.single k 1 ∈ p.support :=
    mem_support_iff.mpr (fun hz => hc (by rw [hz, zero_mul]))
  apply (mem_vars_iff_mem_support j).mpr
  refine ⟨d + Finsupp.single k 1, hp, Finsupp.mem_support_iff.mpr ?_⟩
  have hdj := Finsupp.mem_support_iff.mp hjd
  simp only [Finsupp.add_apply]
  omega

variable [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
/-- The differentiated coefficient field still depends only on the past. -/
theorem IsPastPolynomial.pderiv {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) (k : ι) :
    IsPastPolynomial (fun i => pderiv k (u i)) := by
  intro i j hj
  exact hu i j (pderiv_vars_subset (u i) k hj)

omit [LinearOrder ι] in
/-- Actual polynomial sensitivity of the Gaussian random increment sum. -/
theorem elementaryIntegralPolynomial_pderiv (u : ι → MvPolynomial ι ℝ) (k : ι) :
    pderiv k (elementaryIntegralPolynomial u) =
      u k + elementaryIntegralPolynomial (fun i => pderiv k (u i)) := by
  classical
  simp only [elementaryIntegralPolynomial, map_sum, pderiv_mul,
    pderiv_X, Pi.single_apply, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  simp

omit [LinearOrder ι] in
/-- The sensitivity expression is the actual closed Gaussian gradient value. -/
theorem elementaryIntegral_gradient_graph (u : ι → MvPolynomial ι ℝ) :
    (elementaryIntegralL2 u,
      vectorPolynomialL2 (fun k => u k +
        elementaryIntegralPolynomial (fun i => pderiv k (u i)))) ∈ closedGradient.graph := by
  have h := closedGradient_polynomial_graph (elementaryIntegralPolynomial u)
  have he : gradientPolynomial (elementaryIntegralPolynomial u) =
      fun k => u k + elementaryIntegralPolynomial (fun i => pderiv k (u i)) := by
    funext k
    exact elementaryIntegralPolynomial_pderiv u k
  simpa only [gradientPolynomialL2, he, elementaryIntegralL2] using h

omit [LinearOrder ι] in
/-- The same expression is the actual Fréchet derivative on the Euclidean model. -/
theorem elementaryIntegral_hasFDerivAt (u : ι → MvPolynomial ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι =>
      MvPolynomial.eval y.ofLp (elementaryIntegralPolynomial u))
      (innerSL ℝ (vectorPolynomialFunction
        (fun k => u k + elementaryIntegralPolynomial (fun i => pderiv k (u i))) x.ofLp)) x := by
  have h := gradientPolynomial_hasFDerivAt (elementaryIntegralPolynomial u) x
  have he : gradientPolynomial (elementaryIntegralPolynomial u) =
      fun k => u k + elementaryIntegralPolynomial (fun i => pderiv k (u i)) := by
    funext k
    exact elementaryIntegralPolynomial_pderiv u k
  simpa only [he] using h

/-- The actual gradient equality forces all coefficient partial derivatives to
vanish; zero norm follows from the proved elementary isometry. -/
theorem elementaryIntegral_rigidity_pderiv {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u)
    (hg : (elementaryIntegralL2 u, vectorPolynomialL2 u) ∈ closedGradient.graph)
    (k i : ι) : pderiv k (u i) = 0 := by
  have he := closedGradient.mem_graph_snd_inj (elementaryIntegral_gradient_graph u) hg rfl
  have hp : (fun k => u k + elementaryIntegralPolynomial (fun i => pderiv k (u i))) = u :=
    vectorPolynomialEmbedding_injective he
  have hz : elementaryIntegralPolynomial (fun i => pderiv k (u i)) = 0 := by
    have hk := congrFun hp k
    exact add_left_cancel (hk.trans (add_zero (u k)).symm)
  have hL : elementaryIntegralL2 (fun i => pderiv k (u i)) = 0 := by
    change productPolynomialEmbedding _ = 0
    rw [hz, map_zero]
  have hn := elementaryIntegral_norm_sq (hu.pderiv k)
  rw [hL, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn
  have hv : vectorPolynomialL2 (fun i => pderiv k (u i)) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (vectorPolynomialL2 (fun i => pderiv k (u i)))]
  have hv' : (fun i => pderiv k (u i)) = 0 :=
    vectorPolynomialEmbedding_injective (hv.trans (map_zero vectorPolynomialEmbedding).symm)
  exact congrFun hv' i

omit [LinearOrder ι] in
/-- The actual constant polynomial class is its scalar multiple of the vacuum. -/
theorem productPolynomialL2_C_eq_vacuum (c : ℝ) :
    productPolynomialL2 (C c : MvPolynomial ι ℝ) = c • tensorHermite (fun _ : ι => 0) := by
  apply Lp.ext
  filter_upwards [productPolynomialL2_coeFn (C c : MvPolynomial ι ℝ),
    Lp.coeFn_smul c (tensorHermite (fun _ : ι => 0)), tensorHermite_zero_coeFn (ι := ι)]
    with x hp hs hv
  simp only [hp, eval_C, hs, Pi.smul_apply, hv, smul_eq_mul, mul_one]

/-- Discrete triangular Gaussian rigidity as equality of actual polynomial
coefficients. The converse proves the full closed-gradient graph statement. -/
theorem elementaryIntegral_gradient_eq_coefficients_iff {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) :
    (elementaryIntegralL2 u, vectorPolynomialL2 u) ∈ closedGradient.graph ↔
      ∃ c : ι → ℝ, ∀ i, u i = C (c i) := by
  constructor
  · intro hg
    have hc (i : ι) : ∃ c : ℝ, u i = C c := by
      have hd : gradientPolynomial (u i) = 0 := by
        funext k
        exact elementaryIntegral_rigidity_pderiv hu hg k i
      have hgraph : (productPolynomialL2 (u i), (0 : VectorGaussianL2 ι)) ∈
          closedGradient.graph := by
        have h := closedGradient_polynomial_graph (u i)
        have hz : vectorPolynomialL2 (0 : ι → MvPolynomial ι ℝ) = 0 :=
          vectorPolynomialEmbedding.map_zero
        simpa only [gradientPolynomialL2, hd, hz] using h
      obtain ⟨c, hc⟩ := (closedGradient_zero_iff_const _).mp hgraph
      refine ⟨c, productPolynomialEmbedding_injective ?_⟩
      exact hc.trans (productPolynomialL2_C_eq_vacuum c).symm
    choose c hc using hc
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    have he : (fun k => u k + elementaryIntegralPolynomial (fun i => pderiv k (u i))) = u := by
      funext k
      simp [hc, elementaryIntegralPolynomial]
    simpa only [he] using elementaryIntegral_gradient_graph u

/-- The deterministic coefficients have ordinary constant representatives in
the genuine Gaussian measure, not a factorization against random test fields. -/
theorem elementaryIntegral_rigidity_ae {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u)
    (hg : (elementaryIntegralL2 u, vectorPolynomialL2 u) ∈ closedGradient.graph) :
    ∃ c : ι → ℝ, ∀ i, productPolynomialL2 (u i) =ᵐ[productGaussian ι] fun _ => c i := by
  obtain ⟨c, hc⟩ := (elementaryIntegral_gradient_eq_coefficients_iff hu).mp hg
  refine ⟨c, fun i => ?_⟩
  simpa only [hc i, eval_C] using productPolynomialL2_coeFn (C (c i) : MvPolynomial ι ℝ)

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
