import Foundation.GaussianSensitivityIntegral

/-! Genuine parameterized predictable inputs for adapted polynomial gradients,
and agreement with the pre-existing polynomial sensitivity correction. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSensitivityCore
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianProductDerivative
open GaussianDerivativeTimeCoordinates GaussianPredictableFull SeparableHilbertEmbedding
open GaussianSensitivityIntegral GaussianTimeDivergence GaussianAdaptedGraphCore
open GaussianTimeSensitivity
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable

def pastStep {n : ℕ} (s t : ℝ≥0) (r : Fin n → ℝ≥0) (hrs : ∀ i, r i ≤ s)
    (p : MvPolynomial (Fin n) ℝ) : fullPredictable :=
  ⟨GaussianTimeProductL2.productTensor (intervalVector s t) (pastCoefficient r p),
    (past_polynomial_step_mem_predictableSobolev s t r hrs p).1⟩

theorem past_gradient_expansion {n : ℕ} (r : Fin n → ℝ≥0)
    (p : MvPolynomial (Fin n) ℝ) :
    polynomialDerivative (pastCoefficient r p) =ᵐ[gaussianProduct]
      fun ω => ∑ i, (pastCoefficient r (MvPolynomial.pderiv i p) : GaussianL2) ω •
        hilbertEmbedding TimeHilbert (timeVector (r i)) := by
  have he : polynomialDerivative (pastCoefficient r p) = isonormalCylinderGradientL2
      (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p :=
    polynomialDerivative_on_cylinder _ _
  rw [he]
  filter_upwards [isonormalCylinderGradientL2_coeFn
    (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p,
    ae_all_iff.mpr (fun i => pastCoefficient_coeFn r (MvPolynomial.pderiv i p))] with ω hg hc
  rw [hg]
  simp only [isonormalCylinderGradient]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc i]
  rfl

/-- One and the same finite family describes the actual derivative field and its integral. -/
def stepInput {n : ℕ} (s t : ℝ≥0) (r : Fin n → ℝ≥0) (hrs : ∀ i, r i ≤ s)
    (p : MvPolynomial (Fin n) ℝ) : Inputs :=
  ∑ i, BochnerClosedOperator.tensor volume (timeVector (r i))
    (pastStep s t r hrs (MvPolynomial.pderiv i p))

theorem kernelEmbedding_stepInput {n : ℕ} (s t : ℝ≥0) (r : Fin n → ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ) :
    kernelEmbedding (stepInput s t r hrs p) = stepGradient s t r p := by
  classical
  simp only [stepInput, map_sum, kernelEmbedding_tensor]
  apply Lp.ext
  have hg := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (past_gradient_expansion r p)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
    BochnerClosedOperator.tensor timeProbability
      (pastStep s t r hrs (MvPolynomial.pderiv i p) : TimeProbabilityL2)
      (hilbertEmbedding TimeHilbert (timeVector (r i)))),
    ae_all_iff.mpr (fun i => BochnerClosedOperator.tensor_coeFn timeProbability
      (pastStep s t r hrs (MvPolynomial.pderiv i p) : TimeProbabilityL2)
      (hilbertEmbedding TimeHilbert (timeVector (r i)))),
    ae_all_iff.mpr (fun i => GaussianTimeProductL2.productTensor_coeFn (intervalVector s t)
      (pastCoefficient r (MvPolynomial.pderiv i p))),
    ProductL2Curry.productTensor_coeFn volume gaussianProduct (intervalVector s t)
      (polynomialDerivative (pastCoefficient r p)), hg] with z hsum ht hp hv hg
  change stepGradient s t r p z = _ at hv
  change polynomialDerivative (pastCoefficient r p) z.2 =
    ∑ i, (pastCoefficient r (MvPolynomial.pderiv i p) : GaussianL2) z.2 •
      hilbertEmbedding TimeHilbert (timeVector (r i)) at hg
  rw [hsum, hv, hg, Finset.smul_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i]
  change GaussianTimeProductL2.productTensor (intervalVector s t)
    (pastCoefficient r (MvPolynomial.pderiv i p)) z • _ = _
  rw [hp i, smul_smul]

theorem ito_pastStep {n : ℕ} (s t : ℝ≥0) (hst : s ≤ t) (r : Fin n → ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ) :
    itoIntegral (pastStep s t r hrs p) = incrementProductL2 r p s t := by
  apply Lp.ext
  filter_upwards [itoIntegral_past_step s t hst (pastCoefficient r p)
    (GaussianPastStepCompletion.past_polynomial_measurable s r hrs p),
    pastCoefficient_coeFn r p, incrementProductL2_coeFn r p s t] with ω hi hc hp
  change itoIntegral (pastStep s t r hrs p) ω = _ at hi
  rw [hi, hc, hp]

theorem integral_stepInput {n : ℕ} (s t : ℝ≥0) (hst : s ≤ t) (r : Fin n → ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ) :
    integral (stepInput s t r hrs p) = incrementSensitivity r p s t := by
  classical
  simp only [stepInput, map_sum, integral_tensor, ito_pastStep s t hst]
  apply Lp.ext
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
      scalarTensor (hilbertEmbedding TimeHilbert (timeVector (r i)))
        (incrementProductL2 r (MvPolynomial.pderiv i p) s t)),
    ae_all_iff.mpr (fun i => scalarTensor_coeFn
      (hilbertEmbedding TimeHilbert (timeVector (r i)))
        (incrementProductL2 r (MvPolynomial.pderiv i p) s t)),
    ae_all_iff.mpr (fun i => incrementProductL2_coeFn r (MvPolynomial.pderiv i p) s t),
    ae_all_iff.mpr (fun i => pastCoefficient_coeFn r (MvPolynomial.pderiv i p)),
    incrementSensitivity_coeFn r p s t hst, past_gradient_expansion r p]
      with ω hsum ht hi hc hS hg
  rw [hsum, hS, hg, Finset.smul_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i, hi i, hc i, smul_smul, mul_comm]

theorem correction_stepGradient {n : ℕ} (s t : ℝ≥0) (hst : s ≤ t)
    (r : Fin n → ℝ≥0) (hrs : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ) :
    correction (stepGradient s t r p) = incrementSensitivity r p s t := by
  rw [← kernelEmbedding_stepInput s t r hrs p, correction_embedding]
  exact integral_stepInput s t hst r hrs p

/-- Predictability of the parameterized input is proved and preserved under graph limits. -/
theorem completedGraph_admissible {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) : z.2 ∈ kernelEmbedding.toLinearMap.range := by
  have h : completedGraph ≤ kernelEmbedding.toLinearMap.range.comap
      (LinearMap.snd ℝ TimeProbabilityL2 ProductDerivativeL2) := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨n, s, t, r, p, hrs, hst, rfl⟩
      exact ⟨stepInput s t r hrs p, kernelEmbedding_stepInput s t r hrs p⟩
    · exact kernelEmbedding_closed_range.preimage continuous_snd
  exact h hz

theorem completedGraph_correction_norm {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) : ‖correction z.2‖ = ‖z.2‖ :=
  correction_norm z.2 (completedGraph_admissible hz)

end OperatorDerivativeRewrite.Foundation.GaussianSensitivityCore
