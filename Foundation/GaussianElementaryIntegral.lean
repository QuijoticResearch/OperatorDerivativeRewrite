import Foundation.FiniteGaussianOperators
import Foundation.InfiniteGaussianProjectionConvergence

/-!
# Elementary Gaussian integration with genuine random coefficients

On a finite independent standard Gaussian product, the coefficient of coordinate
`i` is a polynomial in strictly earlier coordinates. Its actual Gaussian
divergence is the sum of coefficient times increment, is centered, and satisfies
the L² isometry. This is an elementary ordered-coordinate construction, not a
Brownian-time integral or a completion of the predictable integrand space.
-/

noncomputable section
open MeasureTheory MvPolynomial
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Literal polynomial dependence on strictly earlier independent coordinates. -/
def IsPastPolynomial (u : ι → MvPolynomial ι ℝ) : Prop :=
  ∀ i j, j ∈ (u i).vars → j < i

/-- The elementary random-coefficient Gaussian increment sum as an actual polynomial. -/
def elementaryIntegralPolynomial (u : ι → MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ i, X i * u i

/-- Its actual class in the scalar Gaussian L² space. -/
def elementaryIntegralL2 (u : ι → MvPolynomial ι ℝ) : ScalarGaussianL2 ι :=
  productPolynomialL2 (elementaryIntegralPolynomial u)

omit [Fintype ι] in
/-- Triangular dependence forces the genuine future partial derivatives to vanish. -/
theorem IsPastPolynomial.pderiv_eq_zero {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) {i j : ι} (hij : i ≤ j) :
    pderiv j (u i) = 0 :=
  pderiv_eq_zero_of_notMem_vars (fun hj => (not_lt_of_ge hij) (hu i j hj))

omit [LinearOrder ι] in
/-- The increment sum has all finite Gaussian moments. -/
theorem elementaryIntegral_memLp (u : ι → MvPolynomial ι ℝ)
    (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun x => ∑ i, x i * MvPolynomial.eval x (u i)) r (productGaussian ι) := by
  simpa [elementaryIntegralPolynomial] using
    productPolynomial_memLp (elementaryIntegralPolynomial u) r hr

omit [LinearOrder ι] in
/-- The random increment sum is the actual representative of the L² construction. -/
theorem elementaryIntegralL2_coeFn (u : ι → MvPolynomial ι ℝ) :
    elementaryIntegralL2 u =ᵐ[productGaussian ι]
      fun x => ∑ i, x i * MvPolynomial.eval x (u i) := by
  simpa [elementaryIntegralL2, elementaryIntegralPolynomial] using
    productPolynomialL2_coeFn (elementaryIntegralPolynomial u)

omit [LinearOrder ι] in
/-- Both the increment sum and its square are genuinely integrable. -/
theorem elementaryIntegral_integrable (u : ι → MvPolynomial ι ℝ) :
    Integrable (fun x => ∑ i, x i * MvPolynomial.eval x (u i)) (productGaussian ι) ∧
      Integrable (fun x => (∑ i, x i * MvPolynomial.eval x (u i)) ^ 2)
        (productGaussian ι) := by
  constructor
  · exact (elementaryIntegral_memLp u 1 (by simp)).integrable (by simp)
  · exact (elementaryIntegral_memLp u 2 (by simp)).integrable_sq

/-- Adaptation removes the derivative term from the actual Gaussian divergence formula. -/
theorem divergencePolynomial_eq_elementaryIntegral {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) : divergencePolynomial u = elementaryIntegralPolynomial u := by
  change (∑ i, (X i * u i - pderiv i (u i))) = ∑ i, X i * u i
  simp only [hu.pderiv_eq_zero le_rfl, sub_zero]

/-- Exact graph membership of the genuine polynomial divergence, with its actual value. -/
theorem elementaryIntegral_divergence_graph {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) :
    (vectorPolynomialL2 u, elementaryIntegralL2 u) ∈ polynomialDivergence.graph := by
  simpa only [divergencePolynomial_eq_elementaryIntegral hu, elementaryIntegralL2] using
    polynomialDivergence_polynomial_graph u

/-- Closing the actual divergence preserves the elementary integral value. -/
theorem elementaryIntegral_closedDivergence_graph {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) :
    (vectorPolynomialL2 u, elementaryIntegralL2 u) ∈ closedVectorDivergence.graph := by
  simpa only [divergencePolynomial_eq_elementaryIntegral hu, elementaryIntegralL2] using
    closedVectorDivergence_polynomial_graph u

omit [LinearOrder ι] in
/-- Stein's identity as the already verified integral functional on genuine polynomials. -/
theorem productPolynomialIntegral_stein (p : MvPolynomial ι ℝ) (i : ι) :
    productPolynomialIntegral (X i * p) = productPolynomialIntegral (pderiv i p) := by
  simpa [productPolynomialIntegral] using productPolynomial_stein p i

/-- The elementary random integral is centered, proved from actual Gaussian Stein. -/
theorem elementaryIntegral_centered {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) :
    (∫ x, (∑ i, x i * MvPolynomial.eval x (u i)) ∂productGaussian ι) = 0 := by
  have h : productPolynomialIntegral (elementaryIntegralPolynomial u) = 0 := by
    simp only [elementaryIntegralPolynomial, map_sum, productPolynomialIntegral_stein,
      hu.pderiv_eq_zero le_rfl, map_zero, Finset.sum_const_zero]
  change (∫ x, MvPolynomial.eval x (elementaryIntegralPolynomial u) ∂productGaussian ι) = 0 at h
  simpa only [elementaryIntegralPolynomial, map_sum, map_mul, MvPolynomial.eval_X] using h

/-- Centering also holds for the representative of the actual L² class. -/
theorem elementaryIntegralL2_integral {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) :
    (∫ x, elementaryIntegralL2 u x ∂productGaussian ι) = 0 := by
  rw [integral_congr_ae (elementaryIntegralL2_coeFn u)]
  exact elementaryIntegral_centered hu

/-- A future centered Gaussian increment gives zero off-diagonal pairing, and
unit variance gives the diagonal coefficient pairing. This is proved by Stein
and actual polynomial differentiation, not assumed as an isometry. -/
theorem elementaryIncrement_inner_of_le {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) (i j : ι) (hij : i ≤ j) :
    inner ℝ (productPolynomialL2 (X i * u i)) (productPolynomialL2 (X j * u j)) =
      if i = j then inner ℝ (productPolynomialL2 (u i)) (productPolynomialL2 (u j)) else 0 := by
  have hs := productPolynomialIntegral_stein ((X i * u i) * u j) j
  have hp : pderiv j ((X i * u i) * u j) =
      if i = j then u i * u j else 0 := by
    simp only [pderiv_mul, hu.pderiv_eq_zero hij, hu.pderiv_eq_zero le_rfl,
      pderiv_X, Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h]
  have he : (X i * u i) * (X j * u j) = X j * ((X i * u i) * u j) := by ring
  rw [← he, hp] at hs
  have hinner : inner ℝ (productPolynomialL2 (X i * u i))
      (productPolynomialL2 (X j * u j)) =
      productPolynomialIntegral ((X i * u i) * (X j * u j)) := by
    change _ = ∫ x, MvPolynomial.eval x ((X i * u i) * (X j * u j)) ∂productGaussian ι
    rw [productPolynomialL2_inner]
    congr 1
    funext x
    exact (map_mul (MvPolynomial.eval x) (X i * u i) (X j * u j)).symm
  rw [hinner]
  rw [hs]
  by_cases h : i = j
  · simp only [h, ↓reduceIte]
    simpa only [productPolynomialIntegral, LinearMap.coe_mk, AddHom.coe_mk,
      MvPolynomial.eval_mul] using (productPolynomialL2_inner (u j) (u j)).symm
  · simp only [h, ↓reduceIte, map_zero]

/-- All cross-coordinate elementary integral pairings vanish. -/
theorem elementaryIncrement_inner {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) (i j : ι) :
    inner ℝ (productPolynomialL2 (X i * u i)) (productPolynomialL2 (X j * u j)) =
      if i = j then inner ℝ (productPolynomialL2 (u i)) (productPolynomialL2 (u j)) else 0 := by
  rcases le_total i j with hij | hji
  · exact elementaryIncrement_inner_of_le hu i j hij
  · rw [real_inner_comm, elementaryIncrement_inner_of_le hu j i hji]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]

/-- Centered L² isometry for actual polynomial past-measurable coefficients.
No assertion is made for anticipating coefficients or arbitrary L² products. -/
theorem elementaryIntegral_norm_sq {u : ι → MvPolynomial ι ℝ}
    (hu : IsPastPolynomial u) :
    ‖elementaryIntegralL2 u‖ ^ 2 = ‖vectorPolynomialL2 u‖ ^ 2 := by
  have he : elementaryIntegralL2 u = ∑ i, productPolynomialL2 (X i * u i) := by
    change productPolynomialEmbedding (∑ i, X i * u i) = _
    exact map_sum productPolynomialEmbedding _ _
  rw [← real_inner_self_eq_norm_sq, he]
  simp_rw [sum_inner, inner_sum, elementaryIncrement_inner hu]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← real_inner_self_eq_norm_sq, vectorPolynomialL2_inner]
  simp only [vectorPolynomialL2_component]

end OperatorDerivativeRewrite.Foundation.FiniteGaussian

namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian

/-- The elementary random integral lifts to the already constructed genuine
infinite-product polynomial divergence, with exact graph membership and value. -/
theorem elementaryIntegral_cylindricalDivergence_graph (s : Finset ℕ)
    (u : s → MvPolynomial s ℝ) (hu : FiniteGaussian.IsPastPolynomial u) :
    (finiteVectorPullback s (FiniteGaussian.vectorPolynomialL2 u),
      finitePullback s (FiniteGaussian.elementaryIntegralL2 u)) ∈
        cylindricalDivergence.graph := by
  simpa only [FiniteGaussian.divergencePolynomial_eq_elementaryIntegral hu,
    FiniteGaussian.elementaryIntegralL2] using finitePolynomialDivergence_lift_graph s u

/-- The genuine infinite full divergence retains this elementary integral value. -/
theorem elementaryIntegral_hilbertDivergence_graph (s : Finset ℕ)
    (u : s → MvPolynomial s ℝ) (hu : FiniteGaussian.IsPastPolynomial u) :
    (finiteVectorPullback s (FiniteGaussian.vectorPolynomialL2 u),
      finitePullback s (FiniteGaussian.elementaryIntegralL2 u)) ∈
        hilbertDivergence.graph :=
  (LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence)
    (elementaryIntegral_cylindricalDivergence_graph s u hu)

/-- The random elementary integral isometry is preserved in the actual infinite model. -/
theorem elementaryIntegral_lift_norm_sq (s : Finset ℕ)
    (u : s → MvPolynomial s ℝ) (hu : FiniteGaussian.IsPastPolynomial u) :
    ‖finitePullback s (FiniteGaussian.elementaryIntegralL2 u)‖ ^ 2 =
      ‖finiteVectorPullback s (FiniteGaussian.vectorPolynomialL2 u)‖ ^ 2 := by
  rw [(finitePullback s).norm_map, finiteVectorPullback_eq_isometry]
  change ‖FiniteGaussian.elementaryIntegralL2 u‖ ^ 2 =
    ‖finiteVectorIsometry s (FiniteGaussian.vectorPolynomialL2 u)‖ ^ 2
  rw [(finiteVectorIsometry s).norm_map]
  exact FiniteGaussian.elementaryIntegral_norm_sq hu

/-- Centering of the actual lifted representative, using its Gaussian marginal law. -/
theorem elementaryIntegral_lift_integral (s : Finset ℕ)
    (u : s → MvPolynomial s ℝ) (hu : FiniteGaussian.IsPastPolynomial u) :
    (∫ ω, finitePullback s (FiniteGaussian.elementaryIntegralL2 u) ω ∂gaussianProduct) = 0 := by
  rw [integral_congr_ae (finitePullback_coeFn s (FiniteGaussian.elementaryIntegralL2 u))]
  have hm := finiteProjection_measurePreserving s
  have hi := integral_map hm.measurable.aemeasurable
    (f := (FiniteGaussian.elementaryIntegralL2 u : (s → ℝ) → ℝ))
    (by rw [hm.map_eq]; exact Lp.aestronglyMeasurable _)
  rw [hm.map_eq] at hi
  rw [← hi]
  exact FiniteGaussian.elementaryIntegralL2_integral hu

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
