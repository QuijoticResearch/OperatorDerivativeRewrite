import Foundation.IBMScalarSecondProjection
import Foundation.GaussianAbsoluteMoments

/-! Polynomial-weighted Stein recurrence on genuine integrable domains.
The observable is bounded; its polynomial multiple need not be bounded. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPolynomialWeightedStein
open InfiniteGaussian IBMScaledGaussianStein IBMFirstChaosDiagonalStein
open HelicalWeightedPressureIBP

theorem weighted_integrable (k : ℕ) (a : ℝ) {φ : ℝ → ℝ} (hc : Continuous φ)
    {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) :
    Integrable (fun x : ℝ => x^k*φ (a*x)) ν := by
  have hi : Integrable (fun x : ℝ => |x|^k) ν := by
    simpa only [Real.norm_eq_abs, id_eq] using
      (memLp_id_gaussianReal' (μ := 0) (v := (1/4)) (k : ℝ≥0∞) (by simp)).integrable_norm_pow'
  apply (hi.mul_const M).mono'
    ((continuous_id.pow k).mul (hc.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖x^k*φ (a*x)‖ ≤ |x|^k*M
    rw [norm_mul, Real.norm_eq_abs, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM _) (by positivity)

theorem scaled_power_integrable (k : ℕ) (a : ℝ) {φ : ℝ → ℝ} (hc : Continuous φ)
    {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) :
    Integrable (fun x : ℝ => (a*x)^k*φ (a*x)) ν := by
  convert (weighted_integrable k a hc hM).const_mul (a^k) using 1
  funext x
  ring

theorem scaled_coordinate_integrable (k : ℕ) (a : ℝ) {φ : ℝ → ℝ} (hc : Continuous φ)
    {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) :
    Integrable (fun x : ℝ => x*((a*x)^k*φ (a*x))) ν := by
  convert (weighted_integrable (k+1) a hc hM).const_mul (a^k) using 1
  funext x
  ring

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {A B : ℝ}
  (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)

include hφ hA hB in
theorem scaled_recurrence (k : ℕ) (a : ℝ) :
    (∫ x, (a*x)^(k+1)*φ (a*x) ∂ν) =
      ((k : ℝ)*a^2/4)*(∫ x, (a*x)^(k-1)*φ (a*x) ∂ν) +
        (a^2/4)*(∫ x, (a*x)^k*deriv φ (a*x) ∂ν) := by
  have hc := hφ.continuous
  have hd := hφ.continuous_deriv (by norm_num)
  have hp (x : ℝ) : HasDerivAt (fun t => (a*t)^k*φ (a*t))
      (((k : ℝ)*a)*(a*x)^(k-1)*φ (a*x)+a*((a*x)^k*deriv φ (a*x))) x := by
    have he := (((hasDerivAt_id x).const_mul a).pow k).mul (scaled_hasDerivAt hφ a x)
    convert he using 1
    · rfl
    · simp only [Pi.pow_apply, id_eq]
      ring
  have h₁ := (scaled_power_integrable (k-1) a hc hA).const_mul ((k : ℝ)*a)
  have h₂ := (scaled_power_integrable k a hd hB).const_mul a
  have hg : Integrable (fun x => ((k : ℝ)*a)*(a*x)^(k-1)*φ (a*x)+
      a*((a*x)^k*deriv φ (a*x))) ν := by
    convert h₁.add h₂ using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have he := HelicalWeightedPressureIBP.stein_integrable hp
    (scaled_power_integrable k a hc hA) hg (scaled_coordinate_integrable k a hc hA)
  have hf : (fun x => ((k : ℝ)*a)*(a*x)^(k-1)*φ (a*x)+a*((a*x)^k*deriv φ (a*x))) =
      fun x => ((k : ℝ)*a)*((a*x)^(k-1)*φ (a*x))+a*((a*x)^k*deriv φ (a*x)) := by
    funext x; ring
  rw [hf, integral_add h₁ h₂, integral_const_mul, integral_const_mul] at he
  have hx : (∫ x, (a*x)^(k+1)*φ (a*x) ∂ν) =
      a*(∫ x, x*((a*x)^k*φ (a*x)) ∂ν) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [pow_succ]
    ring
  rw [hx]
  linear_combination -(a/4)*he

def moment (u : CoefficientSpace) (φ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ ω, (firstChaosEmbedding u ω)^k*φ (firstChaosEmbedding u ω) ∂gaussianProduct

theorem moment_integrable (u : CoefficientSpace) (k : ℕ) {φ : ℝ → ℝ} (hc : Continuous φ)
    {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) :
    Integrable (fun ω => (firstChaosEmbedding u ω)^k*φ (firstChaosEmbedding u ω)) gaussianProduct := by
  apply ((GaussianAbsoluteMoments.firstChaos_absolute_integrable u k).mul_const M).mono'
    (((Lp.stronglyMeasurable (firstChaosEmbedding u)).pow k).mul
      (hc.comp_stronglyMeasurable (Lp.stronglyMeasurable _))).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    change ‖(firstChaosEmbedding u ω)^k*φ (firstChaosEmbedding u ω)‖ ≤ |firstChaosEmbedding u ω|^k*M
    rw [norm_mul, Real.norm_eq_abs, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM _) (by positivity)

include hφ hA hB in
theorem moment_recurrence (u : CoefficientSpace) (k : ℕ) :
    moment u φ (k+1) = (k : ℝ)*‖u‖^2*moment u φ (k-1) + ‖u‖^2*moment u (deriv φ) k := by
  have ht (j : ℕ) (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
      moment u ψ j = ∫ x, ((2*‖u‖)*x)^j*ψ ((2*‖u‖)*x) ∂ν :=
    integral_transport u (f := fun x => x^j*ψ x) ((measurable_id.pow_const j).mul hψ)
  rw [ht (k+1) φ hφ.continuous.measurable, ht (k-1) φ hφ.continuous.measurable,
    ht k (deriv φ) (hφ.continuous_deriv (by norm_num)).measurable]
  have he := scaled_recurrence hφ hA hB k (2*‖u‖)
  convert he using 1 <;> ring

end OperatorDerivativeRewrite.Foundation.IBMPolynomialWeightedStein
