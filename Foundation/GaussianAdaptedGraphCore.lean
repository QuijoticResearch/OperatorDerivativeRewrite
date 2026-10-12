import Foundation.GaussianDerivativeTimeCoordinates

/-! Causal support and lossless time coordinates on the adapted polynomial graph
and its closure. Equality with the independently specified predictable Sobolev
domain is not asserted. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianAdaptedGraphCore
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianProductDerivative
open GaussianDerivativeTimeCoordinates GaussianTimeDivergence SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable

def stepGradient {n : ℕ} (s t : ℝ≥0) (r : Fin n → ℝ≥0)
    (p : MvPolynomial (Fin n) ℝ) : ProductDerivativeL2 :=
  ProductL2Curry.productTensor volume gaussianProduct (intervalVector s t)
    (polynomialDerivative (pastCoefficient r p))

theorem stepGradient_time_range {n : ℕ} (s t : ℝ≥0) (r : Fin n → ℝ≥0)
    (p : MvPolynomial (Fin n) ℝ) : stepGradient s t r p ∈ embedTimeField.toLinearMap.range := by
  refine ⟨projectTimeField (stepGradient s t r p), ?_⟩
  apply Lp.ext
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp
      (past_gradient_reconstruction r p)
  filter_upwards [BochnerLinearIsometry.lift_coeFn timeProbability
    (hilbertEmbedding TimeHilbert) (projectTimeField (stepGradient s t r p)),
    projectTimeField_coeFn (stepGradient s t r p),
    ProductL2Curry.productTensor_coeFn volume gaussianProduct (intervalVector s t)
      (polynomialDerivative (pastCoefficient r p)), hp] with z he hP ht hr
  change hilbertEmbedding TimeHilbert
    (timeProjection (polynomialDerivative (pastCoefficient r p) z.2)) = _ at hr
  change embedTimeField (projectTimeField (stepGradient s t r p)) z = stepGradient s t r p z
  change embedTimeField (projectTimeField (stepGradient s t r p)) z = _ at he
  change stepGradient s t r p z = _ at ht
  rw [he, hP, ht, map_smul, map_smul, hr]
  rfl

theorem past_gradient_supported {n : ℕ} (s : ℝ≥0) (r : Fin n → ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ) :
    ∀ᵐ ω ∂gaussianProduct, ∀ᵐ a ∂(volume : Measure ℝ),
      a ∉ Ioc 0 (s : ℝ) → timeProjection (polynomialDerivative (pastCoefficient r p) ω) a = 0 := by
  filter_upwards [past_gradient_timeProjection r p] with ω hω
  rw [hω]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
      MvPolynomial.eval (fun j => GaussianTimeProcess.process (r j) ω)
        (MvPolynomial.pderiv i p) • timeVector (r i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul
      (MvPolynomial.eval (fun j => GaussianTimeProcess.process (r j) ω)
        (MvPolynomial.pderiv i p)) (timeVector (r i))),
    ae_all_iff.mpr (fun i => timeVector_coeFn (r i))] with a hsum hsm hi ha
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [hsm i]
  simp only [Pi.smul_apply, smul_eq_mul, hi i]
  have hai : a ∉ Ioc 0 (r i : ℝ) := fun h => ha ⟨h.1, h.2.trans (hrs i)⟩
  simp [hai]

/-- Integration time is `z.1.1`, derivative time is `z.2`. -/
def causalRegion : Set ((ℝ × SampleSpace) × ℝ) := {z | 0 < z.2 ∧ z.2 ≤ z.1.1}

theorem causalRegion_measurable : MeasurableSet causalRegion :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))

theorem stepGradient_causal {n : ℕ} (s t : ℝ≥0) (r : Fin n → ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (p : MvPolynomial (Fin n) ℝ) :
    timeCoordinates (stepGradient s t r p) ∈ supportedL2 causalRegion_measurable := by
  classical
  rw [mem_supportedL2_iff]
  have hm : MeasurableSet {z | z ∉ causalRegion →
      timeCoordinates (stepGradient s t r p) z = 0} := by
    simp only [imp_iff_not_or, not_not]
    exact causalRegion_measurable.union (measurableSet_eq_fun
      (Lp.stronglyMeasurable _).measurable measurable_const)
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn s t)
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae (past_gradient_supported s r hrs p)
  filter_upwards [timeCoordinates_coeFn (stepGradient s t r p),
    ProductL2Curry.productTensor_coeFn volume gaussianProduct (intervalVector s t)
      (polynomialDerivative (pastCoefficient r p)), ht, hp] with z hc hv ht hp
  change stepGradient s t r p z = _ at hv
  change intervalVector s t z.1 = (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => 1) z.1 at ht
  rw [hv, map_smul] at hc
  filter_upwards [hc, Lp.coeFn_smul (intervalVector s t z.1)
    (timeProjection (polynomialDerivative (pastCoefficient r p) z.2)), hp] with a hc hs hp ha
  rw [← hc, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hz : z.1 ∈ Ioc (s : ℝ) (t : ℝ)
  · have has : a ∉ Ioc 0 (s : ℝ) := by
      intro h
      exact ha ⟨h.1, h.2.trans hz.1.le⟩
    rw [hp has, mul_zero]
  · rw [ht, indicator_of_notMem hz, zero_mul]

/-- Independently specified lossless causal derivative values. -/
def causalValues : Submodule ℝ ProductDerivativeL2 :=
  embedTimeField.toLinearMap.range ⊓
    (supportedL2 causalRegion_measurable).comap timeCoordinates.toLinearMap

theorem causalValues_isClosed : IsClosed (causalValues : Set ProductDerivativeL2) :=
  embedTimeField.isometry.isClosedEmbedding.isClosed_range.inter
    ((supportedL2_isClosed causalRegion_measurable).preimage timeCoordinates.continuous)

def graphGenerators : Set (TimeProbabilityL2 × ProductDerivativeL2) :=
  {z | ∃ (n : ℕ) (s t : ℝ≥0) (r : Fin n → ℝ≥0) (p : MvPolynomial (Fin n) ℝ),
    (∀ i, r i ≤ s) ∧ s ≤ t ∧ z =
      (GaussianTimeProductL2.productTensor (intervalVector s t) (pastCoefficient r p),
        stepGradient s t r p)}

def polynomialGraph : Submodule ℝ (TimeProbabilityL2 × ProductDerivativeL2) :=
  Submodule.span ℝ graphGenerators

/-- An explicit restricted graph completion, not a definition of the full Sobolev domain. -/
def completedGraph : Submodule ℝ (TimeProbabilityL2 × ProductDerivativeL2) :=
  polynomialGraph.topologicalClosure

theorem completedGraph_le_derivative : completedGraph ≤ derivative.graph := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro z ⟨n, s, t, r, p, hrs, hst, rfl⟩
    exact polynomial_tensor_graph _ _
  · exact derivative_isClosed

theorem completedGraph_predictable {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) : z.1 ∈ GaussianPredictableFull.fullPredictable := by
  have h : completedGraph ≤ GaussianPredictableFull.fullPredictable.comap
      (LinearMap.fst ℝ TimeProbabilityL2 ProductDerivativeL2) := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨n, s, t, r, p, hrs, hst, rfl⟩
      exact (past_polynomial_step_mem_predictableSobolev s t r hrs p).1
    · exact GaussianPredictableFull.fullPredictable_isClosed.preimage continuous_fst
  exact h hz

theorem completedGraph_causal {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) : z.2 ∈ causalValues := by
  have h : completedGraph ≤ causalValues.comap
      (LinearMap.snd ℝ TimeProbabilityL2 ProductDerivativeL2) := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨n, s, t, r, p, hrs, hst, rfl⟩
      exact ⟨stepGradient_time_range s t r p, stepGradient_causal s t r hrs p⟩
    · exact causalValues_isClosed.preimage continuous_snd
  exact h hz

theorem completedGraph_mem_predictableSobolev {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) : z.1 ∈ predictableSobolev :=
  ⟨completedGraph_predictable hz,
    LinearPMap.mem_domain_iff.mpr ⟨z.2, completedGraph_le_derivative hz⟩⟩

theorem completedGraph_time_norm {z : TimeProbabilityL2 × ProductDerivativeL2}
    (hz : z ∈ completedGraph) : ‖timeCoordinates z.2‖ = ‖z.2‖ :=
  timeCoordinates_norm z.2 (completedGraph_causal hz).1

end OperatorDerivativeRewrite.Foundation.GaussianAdaptedGraphCore
