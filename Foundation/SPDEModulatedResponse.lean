import Foundation.FractionalForcingKernel

/-! Sharp L2 threshold for scalar fractional forcing with a bounded multiplier. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.SPDEModulatedResponse
open FractionalForcingKernel
open GaussianTimeHilbert InfiniteGaussian GaussianHilbertProcess
attribute [local instance] timeHilbert_secondCountable

def modulatedResponse (α : ℝ) (t : ℝ≥0) (g : ℝ → ℝ) : ℝ → ℝ :=
  fun s => g s * response α t s

theorem modulatedResponse_memLp (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) :
    MemLp (modulatedResponse α t g) 2 volume := by
  have hbase := (GaussianPowerVolterra.kernel_memLp (α - 1) (by linarith) t).const_smul
    (Real.Gamma α)⁻¹
  have hmod : AEStronglyMeasurable (modulatedResponse α t g) volume :=
    (hg.mul ((GaussianPowerVolterra.kernel_measurable (α - 1) t).const_mul _)).aestronglyMeasurable
  apply MemLp.of_le_mul (c := M) hbase hmod
  filter_upwards [] with s
  dsimp [modulatedResponse]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hupper s) (abs_nonneg _)

def modulatedVector (α : ℝ) (hα : 1 / 2 < α) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) : TimeHilbert :=
  (modulatedResponse_memLp α hα t g hg M hupper).toLp (modulatedResponse α t g)

theorem modulatedVector_coeFn (α : ℝ) (hα : 1 / 2 < α) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) :
    modulatedVector α hα t g hg M hupper =ᵐ[volume]
      modulatedResponse α t g := MemLp.coeFn_toLp _

theorem modulatedVector_energy (α : ℝ) (hα : 1 / 2 < α) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) :
    ‖modulatedVector α hα t g hg M hupper‖ ^ 2 =
      ∫ s, (modulatedResponse α t g s)^2 := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [modulatedVector_coeFn α hα t g hg M hupper] with s hs
  simp [hs, pow_two]

def stochasticModulatedResponse (α : ℝ) (hα : 1 / 2 < α) (t : ℝ≥0)
    (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) : GaussianL2 :=
  isonormalEmbedding TimeHilbert (modulatedVector α hα t g hg M hupper)

theorem stochasticModulatedResponse_energy (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) :
    ‖stochasticModulatedResponse α hα t g hg M hupper‖ ^ 2 =
      ∫ s, (modulatedResponse α t g s)^2 := by
  rw [stochasticModulatedResponse, LinearIsometry.norm_map,
    modulatedVector_energy]

theorem response_energy_integral (α : ℝ) (hα : 1 / 2 < α) (t : ℝ≥0) :
    (∫ s, (response α t s)^2) =
      (t : ℝ)^(2*α - 1) / ((Real.Gamma α)^2 * (2*α - 1)) := by
  rw [← responseVector_norm_sq α hα t,
    ← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [responseVector_coeFn α hα t] with s hs
  simp [hs, pow_two]

theorem stochasticModulatedResponse_energy_le (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) :
    ‖stochasticModulatedResponse α hα t g hg M hupper‖ ^ 2 ≤
      M^2 * ((t : ℝ)^(2*α - 1) / ((Real.Gamma α)^2 * (2*α - 1))) := by
  rw [stochasticModulatedResponse_energy]
  have hbase : Integrable (fun s => (response α t s)^2) volume :=
    ((GaussianPowerVolterra.kernel_memLp (α - 1) (by linarith) t).const_smul
      (Real.Gamma α)⁻¹).integrable_sq
  have hmod : Integrable (fun s => (modulatedResponse α t g s)^2) volume :=
    (modulatedResponse_memLp α hα t g hg M hupper).integrable_sq
  have hM : 0 ≤ M := le_trans (abs_nonneg (g 0)) (hupper 0)
  have hcmp : ∀ s, (modulatedResponse α t g s)^2 ≤
      M^2 * (response α t s)^2 := by
    intro s
    have hg2 : (g s)^2 ≤ M^2 := by
      have hp := mul_nonneg (sub_nonneg.mpr (hupper s))
        (add_nonneg hM (abs_nonneg (g s)))
      nlinarith [sq_abs (g s)]
    unfold modulatedResponse
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hg2 (sq_nonneg _)
  have hi := integral_mono hmod (hbase.const_mul (M^2)) hcmp
  rw [integral_const_mul, response_energy_integral α hα t] at hi
  exact hi

theorem stochasticModulatedResponse_law (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) :
    gaussianProduct.map (stochasticModulatedResponse α hα t g hg M hupper) =
      gaussianReal 0 ⟨∫ s, (modulatedResponse α t g s)^2,
        by rw [← modulatedVector_energy α hα t g hg M hupper]; positivity⟩ := by
  change gaussianProduct.map (isonormal TimeHilbert
    (modulatedVector α hα t g hg M hupper)) = _
  rw [isonormal_law]
  congr 1
  exact Subtype.ext (modulatedVector_energy α hα t g hg M hupper)

theorem stochasticModulatedResponse_derivative_graph (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hupper : ∀ s, |g s| ≤ M) :
    (stochasticModulatedResponse α hα t g hg M hupper,
      GaussianContinuousRigidity.fieldEmbedding
        (GaussianTimeProductL2.productTensor
          (modulatedVector α hα t g hg M hupper) gaussianOne)) ∈
        closedCylindricalDerivative.graph :=
  GaussianDeterministicIntegral.firstChaos_closedDerivative_graph _

theorem modulatedResponse_memLp_iff (α : ℝ) (hα : 0 < α)
    (t : ℝ≥0) (ht : 0 < t) (g : ℝ → ℝ)
    (hg : Measurable g) (M m : ℝ) (hm : 0 < m)
    (hupper : ∀ s, |g s| ≤ M) (hlower : ∀ s, m ≤ |g s|) :
    MemLp (modulatedResponse α t g) 2 volume ↔ 1 / 2 < α := by
  have hmod : AEStronglyMeasurable (modulatedResponse α t g) volume := by
    exact (hg.mul
      ((GaussianPowerVolterra.kernel_measurable (α - 1) t).const_mul _)).aestronglyMeasurable
  have hresponse : AEStronglyMeasurable (response α t) volume := by
    exact
      ((GaussianPowerVolterra.kernel_measurable (α - 1) t).const_mul _).aestronglyMeasurable
  constructor
  · intro hres
    have hbase : MemLp (response α t) 2 volume := by
      apply MemLp.of_le_mul (c := m⁻¹) hres hresponse
      filter_upwards [] with s
      have h := hlower s
      dsimp [modulatedResponse]
      rw [abs_mul]
      have hnon : 0 ≤ |response α t s| := abs_nonneg _
      have hineq : m * |response α t s| ≤ |g s| * |response α t s| :=
        mul_le_mul_of_nonneg_right h hnon
      have hinv : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
      have hprod := mul_le_mul_of_nonneg_left hineq hinv
      have heq : m⁻¹ * (m * |response α t s|) = |response α t s| := by
        field_simp
      simpa [heq, mul_assoc] using hprod
    exact (response_memLp_iff α hα t ht).mp hbase
  · intro horder
    have hbase := (response_memLp_iff α hα t ht).mpr horder
    apply MemLp.of_le_mul (c := M) hbase hmod
    filter_upwards [] with s
    dsimp [modulatedResponse]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hupper s) (abs_nonneg _)

end OperatorDerivativeRewrite.Foundation.SPDEModulatedResponse
