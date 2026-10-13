import Foundation.GaussianDeterministicVolterra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! An actual singular power Volterra kernel, including time zero. This is a
Riemann--Liouville kernel; no standard fractional Brownian covariance is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPowerVolterra
open InfiniteGaussian GaussianTimeHilbert GaussianDeterministicVolterra
attribute [local instance] timeHilbert_secondCountable

def kernel (β : ℝ) (t : ℝ≥0) : ℝ → ℝ :=
  (Ioc 0 (t : ℝ)).indicator (fun s => ((t : ℝ) - s) ^ β)

theorem kernel_measurable (β : ℝ) (t : ℝ≥0) : Measurable (kernel β t) :=
  ((measurable_const.sub measurable_id).pow_const β).indicator measurableSet_Ioc

theorem kernel_sq (β : ℝ) (t : ℝ≥0) :
    (fun s => kernel β t s ^ 2) =
      (Ioc 0 (t : ℝ)).indicator (fun s => ((t : ℝ) - s) ^ (2 * β)) := by
  funext s
  by_cases hs : s ∈ Ioc 0 (t : ℝ)
  · simp only [kernel, indicator_of_mem hs]
    rw [mul_comm (2 : ℝ) β]
    exact (Real.rpow_mul_natCast (sub_nonneg.mpr hs.2) β 2).symm
  · simp [kernel, hs]

theorem power_intervalIntegrable (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) :
    IntervalIntegrable (fun s => ((t : ℝ) - s) ^ (2 * β)) volume 0 t := by
  have h := ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ))
    (b := (t : ℝ)) (r := 2 * β) (by linarith)).comp_sub_left (t : ℝ)).symm
  simpa only [sub_self, sub_zero] using h

theorem kernel_sq_integrable (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) :
    Integrable (fun s => kernel β t s ^ 2) volume := by
  rw [kernel_sq]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp
    (power_intervalIntegrable β hβ t)).integrable_indicator measurableSet_Ioc

theorem kernel_memLp (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) :
    MemLp (kernel β t) 2 volume :=
  (memLp_two_iff_integrable_sq (kernel_measurable β t).aestronglyMeasurable).mpr
    (kernel_sq_integrable β hβ t)

theorem kernel_energy (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) :
    ∫ s, kernel β t s ^ 2 = (t : ℝ) ^ (2 * β + 1) / (2 * β + 1) := by
  rw [kernel_sq, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le t.coe_nonneg,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (2 * β)) (t : ℝ)]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith : -1 < 2 * β))]
  rw [Real.zero_rpow (by linarith : 2 * β + 1 ≠ 0), sub_zero]

def vector (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) : TimeHilbert :=
  (kernel_memLp β hβ t).toLp (kernel β t)

theorem vector_coeFn (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) :
    vector β hβ t =ᵐ[volume] kernel β t := MemLp.coeFn_toLp _

theorem vector_norm_sq (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) :
    ‖vector β hβ t‖ ^ 2 = (t : ℝ) ^ (2 * β + 1) / (2 * β + 1) := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral, ← kernel_energy β hβ t]
  apply integral_congr_ae
  filter_upwards [vector_coeFn β hβ t] with s hs
  simp [hs, pow_two]

theorem vector_support (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∉ Ioc 0 (t : ℝ) → vector β hβ t s = 0 := by
  filter_upwards [vector_coeFn β hβ t] with s hs hst
  rw [hs, kernel, indicator_of_notMem hst]

def profile (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) : positiveProfiles :=
  ⟨vector β hβ t, causal_profile_mem t _ (vector_support β hβ t)⟩

def value (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) : GaussianL2 :=
  profileIntegral (profile β hβ t)

theorem value_law (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) :
    gaussianProduct.map (value β hβ t) = gaussianReal 0
      ⟨(t : ℝ) ^ (2 * β + 1) / (2 * β + 1),
        by rw [← vector_norm_sq β hβ t]; positivity⟩ := by
  have h := profileIntegral_law (profile β hβ t)
  simpa only [value, profile, vector_norm_sq] using h

theorem value_derivative (β : ℝ) (hβ : -1 / 2 < β) (t : ℝ≥0) :
    (value β hβ t, GaussianContinuousRigidity.fieldEmbedding
      (GaussianTimeProductL2.productTensor (vector β hβ t) gaussianOne)) ∈
        closedCylindricalDerivative.graph :=
  profileIntegral_derivative (profile β hβ t)

theorem vector_zero (β : ℝ) (hβ : -1 / 2 < β) : vector β hβ 0 = 0 := by
  apply Lp.ext
  filter_upwards [vector_coeFn β hβ 0] with s hs
  simpa [kernel] using hs

theorem vector_exponent_zero (t : ℝ≥0) : vector 0 (by norm_num) t = timeVector t := by
  apply Lp.ext
  filter_upwards [vector_coeFn 0 (by norm_num) t, timeVector_coeFn t] with s hs ht
  rw [hs, ht]
  simp [kernel]

theorem value_isGaussianProcess (β : ℝ) (hβ : -1 / 2 < β) :
    IsGaussianProcess (fun t ω => value β hβ t ω) gaussianProduct :=
  volterraProcess_isGaussianProcess (vector β hβ) (vector_support β hβ)

theorem kernel_pair_integrable (β : ℝ) (hβ : -1 / 2 < β) (s t : ℝ≥0) :
    Integrable (fun r => kernel β s r * kernel β t r) volume :=
  mul_L2_integrable (kernel_memLp β hβ s) (kernel_memLp β hβ t)

theorem value_covariance (β : ℝ) (hβ : -1 / 2 < β) (s t : ℝ≥0) :
    cov[value β hβ s, value β hβ t; gaussianProduct] =
      ∫ r, kernel β s r * kernel β t r := by
  rw [value, value, profileIntegral_covariance]
  apply integral_congr_ae
  filter_upwards [vector_coeFn β hβ s, vector_coeFn β hβ t] with r hs ht
  exact congrArg₂ (· * ·) hs ht

theorem value_zero (β : ℝ) (hβ : -1 / 2 < β) : value β hβ 0 = 0 := by
  rw [value, profileIntegral_eq_isonormal]
  change GaussianHilbertProcess.isonormalEmbedding TimeHilbert (vector β hβ 0) = 0
  rw [vector_zero, map_zero]

theorem value_exponent_zero (t : ℝ≥0) :
    value 0 (by norm_num) t = GaussianTimeProcess.wienerL2 t := by
  rw [value, profileIntegral_eq_isonormal]
  change GaussianHilbertProcess.isonormalEmbedding TimeHilbert (vector 0 (by norm_num) t) = _
  rw [vector_exponent_zero]
  rfl

/-- Variance normalization alone does not identify standard fBM. -/
def normalizedVector (H : ℝ) (hH : 0 < H) (t : ℝ≥0) : TimeHilbert :=
  Real.sqrt (2 * H) • vector (H - 1 / 2) (by linarith) t

theorem normalizedVector_norm_sq (H : ℝ) (hH : 0 < H) (t : ℝ≥0) :
    ‖normalizedVector H hH t‖ ^ 2 = (t : ℝ) ^ (2 * H) := by
  rw [normalizedVector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity), vector_norm_sq]
  rw [show 2 * (H - 1 / 2) + 1 = 2 * H by ring]
  exact mul_div_cancel₀ _ (by positivity : 2 * H ≠ 0)
end OperatorDerivativeRewrite.Foundation.GaussianPowerVolterra
