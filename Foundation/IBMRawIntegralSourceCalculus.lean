import Foundation.IBMRawDeterministicIntegral
import Foundation.GaussianFirstChaosRecovery
import Foundation.BochnerLiftAdjointInclusion
import Foundation.IBMIntrinsicOperators

/-! The completed deterministic raw integral belongs to the ORIGINAL source
derivative domain. Its actual source gradient is also in the original source
divergence domain, with divergence equal to the integral. This says nothing
about the separate clock derivative domain or random-integrand integration. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawIntegralSourceCalculus
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMFiniteAverageCore
open GaussianBrownianSobolevField IBMRawDeterministicIntegral
local notation "rawIntegral" => IBMRawDeterministicIntegral.integral
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local irreducible] sourceDerivative

theorem source_curry (u : ValueSpace) : sourceUnitary (jointRealization u) = u := by
  change ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct
        ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm u))) = u
  exact (congrArg (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct)
    (IBMNonlinearAverageGraph.swap_swap
      ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm u))).trans
    (LinearIsometryEquiv.apply_symm_apply _ _)

/-- Bounded first-source projection-gradient; only the following graph theorems
identify it with the unbounded derivative on the completed raw integral. -/
def ambientGradient : JointL2 →L[ℝ] FieldSpace :=
  (firstChaosGradient.compLpL 2 gaussianProduct).comp
    sourceUnitary.toLinearIsometry.toContinuousLinearMap

def gradient : Domain →L[ℝ] FieldSpace := ambientGradient.comp rawIntegral

attribute [local irreducible] ambientGradient gradient IBMRawDeterministicIntegral.integral
  LinearPMap.adjoint LinearPMap.graph

theorem point_gradient (t : ℝ≥0) :
    ambientGradient (IBMDeterministicRangeObstruction.observed t) =
      IBMUnmollifiedSourceDerivative.gradient t := by
  unfold ambientGradient
  change firstChaosGradient.compLp
    (sourceUnitary (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t))) = _
  rw [source_curry]
  rfl

theorem gradient_kernel (t : ℝ≥0) :
    gradient (kernelVector t) = IBMUnmollifiedSourceDerivative.gradient t := by
  unfold gradient
  change ambientGradient (rawIntegral (kernelVector t)) = _
  rw [integral_kernel, point_gradient]

theorem point_derivative_graph (t : ℝ≥0) :
    (IBMDeterministicRangeObstruction.observed t,
      ambientGradient (IBMDeterministicRangeObstruction.observed t)) ∈
      sourceDerivative.graph := by
  rw [point_gradient]
  unfold sourceDerivative
  apply (AdjointUnitaryTransport.mem_pullback_graph _ _ _ _).mpr
  change (sourceUnitary (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t)), _) ∈ _
  rw [source_curry]
  exact IBMUnmollifiedSourceDerivative.randomSource_graph t

private theorem first_gradient_divergence (h : CoefficientSpace) :
    (firstChaosGradient (firstChaosEmbedding h), firstChaosEmbedding h) ∈
      hilbertDivergence.graph := by
  have he : firstChaosGradient (firstChaosEmbedding h) = scalarTensor h gaussianOne := by
    rw [firstChaosGradient_apply]
    apply Lp.ext
    filter_upwards [Lp.coeFn_const 2 gaussianProduct h,
      scalarTensor_coeFn h gaussianOne, gaussianOne_coeFn]
      with ω hc ht ho
    simp only [hc, ht, ho, one_smul, Function.const_apply]
  rw [he]
  exact GaussianFirstChaosRecovery.firstChaos_divergence_graph h

private theorem point_lift_divergence (t : ℝ≥0) :
    (IBMUnmollifiedSourceDerivative.gradient t, IBMRandomTimeHilbert.randomSourceL2 t) ∈
      (BochnerClosedOperator.lift gaussianProduct hilbertDivergence).graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [firstChaosGradient.coeFn_compLp (IBMRandomTimeHilbert.randomSourceL2 t),
    (IBMRandomTimeHilbert.randomSourceClass_memLp t).coeFn_toLp] with ω hg hu
  change IBMUnmollifiedSourceDerivative.gradient t ω = _ at hg
  change IBMRandomTimeHilbert.randomSourceL2 t ω = IBMRandomTimeHilbert.randomSourceClass t ω at hu
  rw [hg, hu]
  exact first_gradient_divergence _

theorem point_divergence_graph (t : ℝ≥0) :
    (ambientGradient (IBMDeterministicRangeObstruction.observed t),
      IBMDeterministicRangeObstruction.observed t) ∈ sourceDerivative.adjoint.graph := by
  have hg := LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct
      closedCylindricalDerivative closedCylindricalDerivative_dense_domain)
    (point_lift_divergence t)
  have hm := LinearPMap.mem_domain_of_mem_graph hg
  have hs : IBMUnmollifiedSourceDerivative.gradient t ∈ sourceDerivative.adjoint.domain := by
    rw [source_adjoint_domain]
    exact hm
  rw [point_gradient]
  apply sourceDerivative.adjoint.mem_graph_iff.mpr
  refine ⟨⟨_, hs⟩, rfl, ?_⟩
  rw [source_adjoint_apply _ hs hm]
  have hv := ((partialDerivative.adjoint.image_iff hm).mpr hg).symm
  calc
    _ = sourceUnitary.symm (IBMRandomTimeHilbert.randomSourceL2 t) := congrArg _ hv
    _ = IBMDeterministicRangeObstruction.observed t := by
      apply sourceUnitary.injective
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact (source_curry _).symm

private theorem extend_graph {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ (E × F)) (hS : IsClosed (S : Set (E × F)))
    (A : Domain →L[ℝ] E) (B : Domain →L[ℝ] F)
    (hp : ∀ t, (A (kernelVector t), B (kernelVector t)) ∈ S) (f : Domain) :
    (A f, B f) ∈ S := by
  have hm : ∀ x ∈ Set.range reference, (A x, B x) ∈ S := by
    rintro x ⟨a, rfl⟩
    change (A (∑ t ∈ a.support, a t • kernelVector t),
      B (∑ t ∈ a.support, a t • kernelVector t)) ∈ S
    rw [map_sum, map_sum]
    simp only [map_smul]
    simpa only [Prod.smul_mk, ← prod_mk_sum] using
      S.sum_mem (fun t (_ : t ∈ a.support) => S.smul_mem (a t) (hp t))
  exact reference_dense.induction hm (hS.preimage (A.continuous.prodMk B.continuous)) f

theorem derivative_graph (f : Domain) : (rawIntegral f, gradient f) ∈ sourceDerivative.graph := by
  apply extend_graph sourceDerivative.graph sourceDerivative_closed rawIntegral gradient _ f
  intro t
  unfold gradient
  change (rawIntegral (kernelVector t), ambientGradient (rawIntegral (kernelVector t))) ∈ _
  rw [integral_kernel]
  exact point_derivative_graph t

theorem divergence_graph (f : Domain) :
    (gradient f, rawIntegral f) ∈ sourceDerivative.adjoint.graph := by
  apply extend_graph sourceDerivative.adjoint.graph
    (sourceDerivative.adjoint_isClosed sourceDerivative_dense) gradient rawIntegral _ f
  intro t
  unfold gradient
  change (ambientGradient (rawIntegral (kernelVector t)), rawIntegral (kernelVector t)) ∈ _
  rw [integral_kernel]
  exact point_divergence_graph t

def domainValue (f : Domain) : sourceDerivative.domain :=
  ⟨rawIntegral f, LinearPMap.mem_domain_of_mem_graph (derivative_graph f)⟩

def divergenceValue (f : Domain) : sourceDerivative.adjoint.domain :=
  ⟨gradient f, LinearPMap.mem_domain_of_mem_graph (divergence_graph f)⟩

theorem derivative_value (f : Domain) : sourceDerivative (domainValue f) = gradient f :=
  ((sourceDerivative.image_iff _).mpr (derivative_graph f)).symm

theorem divergence_value (f : Domain) :
    sourceDerivative.adjoint (divergenceValue f) = rawIntegral f :=
  ((sourceDerivative.adjoint.image_iff _).mpr (divergence_graph f)).symm

/-- Exact first-source energy, not an isometry from the reference input norm. -/
theorem gradient_norm (f : Domain) : ‖gradient f‖ = ‖rawIntegral f‖ := by
  have h := sourceDerivative.adjoint_isFormalAdjoint sourceDerivative_dense
    (divergenceValue f) (domainValue f)
  rw [divergence_value, derivative_value] at h
  change inner ℝ (rawIntegral f) (rawIntegral f) = inner ℝ (gradient f) (gradient f) at h
  have hs : ‖rawIntegral f‖ ^ 2 = ‖gradient f‖ ^ 2 :=
    (real_inner_self_eq_norm_sq (rawIntegral f)).symm.trans
      (h.trans (real_inner_self_eq_norm_sq (gradient f)))
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs.symm

theorem integration_by_parts (f : Domain) (F : sourceDerivative.domain) :
    inner ℝ (rawIntegral f) (F : JointL2) = inner ℝ (gradient f) (sourceDerivative F) := by
  have h := sourceDerivative.adjoint_isFormalAdjoint sourceDerivative_dense (divergenceValue f) F
  rw [divergence_value] at h
  exact h

theorem gradient_inner (f g : Domain) :
    inner ℝ (gradient f) (gradient g) = inner ℝ (rawIntegral f) (rawIntegral g) := by
  have h := integration_by_parts f (domainValue g)
  rw [derivative_value] at h
  exact h.symm

theorem actual_product_integrable (f : Domain) (F : JointL2) :
    Integrable (fun p => rawIntegral f p * F p) IBMSourceLaws.jointMeasure :=
  (Lp.memLp (rawIntegral f)).integrable_mul (Lp.memLp F)

theorem actual_integration_by_parts (f : Domain) (F : sourceDerivative.domain) :
    (∫ p, rawIntegral f p * (F : JointL2) p ∂IBMSourceLaws.jointMeasure) =
      inner ℝ (gradient f) (sourceDerivative F) := by
  calc
    _ = inner ℝ (rawIntegral f) (F : JointL2) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact ae_of_all _ fun p => by simp only [Real.inner_apply, mul_comm]
    _ = _ := integration_by_parts f F

/-- BOTH original graph coordinates converge strongly for every input approximation. -/
theorem graph_limit (a : ℕ → (ℝ≥0 →₀ ℝ)) (f : Domain)
    (ha : Tendsto (fun n => reference (a n)) atTop (𝓝 f)) :
    Tendsto (fun n => (finite (a n), ambientGradient (finite (a n)))) atTop
      (𝓝 (rawIntegral f, gradient f)) := by
  have h := ((rawIntegral).continuous.prodMk gradient.continuous).continuousAt.tendsto.comp ha
  simpa only [Function.comp_def, integral_finite, gradient, ContinuousLinearMap.comp_apply] using h

end OperatorDerivativeRewrite.Foundation.IBMRawIntegralSourceCalculus
