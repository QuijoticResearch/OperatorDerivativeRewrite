import Foundation.GaussianBrownianSobolevField

/-! First-chaos orthogonal projection, its actual closed derivative, and a
past-preserving formula derived from Gaussian IBP. Higher chaos and the full
Brownian-past projected-gradient intertwining theorem remain separate. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPastFirstChaos
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeDivergence
open GaussianTimePolynomialPairing GaussianSensitivityCore SeparableHilbertEmbedding
open GaussianBrownianSobolevField
attribute [local instance] timeHilbert_secondCountable

/-- The actual bounded orthogonal projection onto the complete first-chaos range. -/
def projection : GaussianL2 →L[ℝ] GaussianL2 :=
  firstChaosEmbedding.toContinuousLinearMap.comp firstChaosEmbedding.toContinuousLinearMap.adjoint

theorem projection_idempotent (f : GaussianL2) : projection (projection f) = projection f :=
  HilbertRepresentation.representationProjection_idempotent firstChaosEmbedding f

theorem projection_residual_orthogonal (f : GaussianL2) :
    f - projection f ∈ firstChaosEmbedding.toLinearMap.rangeᗮ :=
  HilbertRepresentation.representation_residual_orthogonal firstChaosEmbedding f

/-- Every projected class really belongs to the full derivative domain. The
derivative is the constant vector obtained from the actual Hilbert adjoint. -/
theorem projection_closedDerivative_graph (f : GaussianL2) :
    (projection f, firstChaosGradient f) ∈ closedCylindricalDerivative.graph := by
  let h := firstChaosEmbedding.toContinuousLinearMap.adjoint f
  have hg := closedCylindricalDerivative_core_graph (firstChaosPolynomial h)
  have hf : (firstChaosPolynomial h : GaussianL2) = projection f :=
    Lp.ext (firstChaosPolynomial_coeFn h)
  have hd : polynomialDerivative (firstChaosPolynomial h) = firstChaosGradient f := by
    apply Lp.ext
    filter_upwards [firstChaosPolynomial_derivative_coeFn h,
      Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := h)] with ω hg hc
    exact hg.trans hc.symm
  rwa [hf, hd] at hg

/-- Coefficients of the genuine orthogonal projection are expectations of
actual polynomial partial derivatives, even for dependent past observations. -/
theorem adjoint_pastPolynomial {n : ℕ} (r : Fin n → ℝ≥0) (p : MvPolynomial (Fin n) ℝ) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (pastCoefficient r p) =
      ∑ i, (∫ ω, (pastCoefficient r (MvPolynomial.pderiv i p) : GaussianL2) ω ∂gaussianProduct) •
        hilbertEmbedding TimeHilbert (timeVector (r i)) := by
  apply ext_inner_right ℝ
  intro k
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (pastCoefficient r p : GaussianL2) (firstChaosEmbedding k) = _
  rw [L2_inner_eq_integral]
  calc
    _ = ∫ ω, (pastCoefficient r p : GaussianL2) ω * firstChaosEmbedding k ω ∂gaussianProduct := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => by simp [Real.inner_apply, mul_comm]
    _ = ∫ ω, inner ℝ (polynomialDerivative (pastCoefficient r p) ω) k ∂gaussianProduct :=
      (polynomialDerivative_stein (pastCoefficient r p) k).symm
    _ = ∫ ω, ∑ i, (pastCoefficient r (MvPolynomial.pderiv i p) : GaussianL2) ω *
        inner ℝ (hilbertEmbedding TimeHilbert (timeVector (r i))) k ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [past_gradient_expansion r p] with ω hg
      rw [hg, sum_inner]
      simp only [real_inner_smul_left]
    _ = _ := by
      rw [integral_finset_sum Finset.univ (fun i _ =>
        ((Lp.memLp (pastCoefficient r (MvPolynomial.pderiv i p) : GaussianL2)).integrable
          (by simp)).mul_const _), sum_inner]
      simp only [integral_mul_const, real_inner_smul_left]

/-- First-chaos truncation preserves the finite past directions. This is a
derived Gaussian projection formula, not an arbitrary conditional-expectation rule. -/
theorem projection_pastPolynomial {n : ℕ} (r : Fin n → ℝ≥0) (p : MvPolynomial (Fin n) ℝ) :
    projection (pastCoefficient r p) =
      ∑ i, (∫ ω, (pastCoefficient r (MvPolynomial.pderiv i p) : GaussianL2) ω ∂gaussianProduct) •
        wienerL2 (r i) := by
  change firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint _) = _
  rw [adjoint_pastPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rfl

theorem projection_pastPolynomial_measurable {n : ℕ} (s : ℝ≥0) (r : Fin n → ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ) :
    AEStronglyMeasurable[naturalFiltration s] (projection (pastCoefficient r p)) gaussianProduct := by
  rw [projection_pastPolynomial]
  have hmem : (∑ i, (∫ ω, (pastCoefficient r (MvPolynomial.pderiv i p) : GaussianL2) ω
      ∂gaussianProduct) • wienerL2 (r i)) ∈ lpMeas ℝ ℝ (naturalFiltration s) 2 gaussianProduct := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact ((process_stronglyAdapted (r i)).mono (naturalFiltration.mono (hrs i))).aestronglyMeasurable
  exact hmem

/-- The first-chaos projection preserves the ENTIRE raw Brownian past, not
just one finite observation algebra. This uses ambient density legitimately
for a bounded projection; it is not full Sobolev graph density. -/
theorem projection_preserves_past (s : ℝ≥0) (f : GaussianL2)
    (hf : AEStronglyMeasurable[naturalFiltration s] f gaussianProduct) :
    AEStronglyMeasurable[naturalFiltration s] (projection f) gaussianProduct := by
  have hc : IsClosed {g : GaussianL2 |
      AEStronglyMeasurable[naturalFiltration s] (projection g) gaussianProduct} :=
    (isClosed_aestronglyMeasurable (naturalFiltration.le s)).preimage projection.continuous
  apply (closure_minimal (Subset.refl _) hc)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, r, p, hrs, hp⟩ :=
    GaussianTimePastDensity.exists_fin_pastPolynomial_approx s f hf ε hε
  exact ⟨pastCoefficient r p, projection_pastPolynomial_measurable s r hrs p,
    by simpa only [dist_eq_norm] using hp⟩

end OperatorDerivativeRewrite.Foundation.GaussianPastFirstChaos
