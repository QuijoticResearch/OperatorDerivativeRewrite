import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Integration against actual complex density measures, with bounded measurable tests. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexDensityIntegral

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem finite_variation (ρ : Ω → ℂ) (hρ : Integrable ρ μ) :
    IsFiniteMeasure (μ.withDensityᵥ ρ).variation := by
  let : IsFiniteMeasure (μ.withDensity (fun x => ‖ρ x‖ₑ)) := ⟨by simpa using! hρ.2⟩
  rw [Measure.variation_withDensityᵥ hρ]
  infer_instance

theorem simple_density (ρ : Ω → ℂ) (hρ : Integrable ρ μ) (g : SimpleFunc Ω ℂ) :
    (μ.withDensityᵥ ρ).Integrable g ∧ Integrable (fun x => g x * ρ x) μ ∧
      (∫ᵛ x, g x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ ρ]) =
        ∫ x, g x * ρ x ∂μ := by
  let := finite_variation μ ρ hρ
  induction g using SimpleFunc.induction with
  | @const c s hs =>
    have he : (fun x => (SimpleFunc.piecewise s hs (SimpleFunc.const Ω c)
        (SimpleFunc.const Ω 0)) x) = s.indicator (fun _ => c) := by
      ext x
      simp [SimpleFunc.coe_piecewise, Set.indicator]
    change (μ.withDensityᵥ ρ).Integrable _ ∧ Integrable (fun x =>
      (SimpleFunc.piecewise s hs (SimpleFunc.const Ω c) (SimpleFunc.const Ω 0) : Ω → ℂ) x * ρ x) μ ∧ _
    simp only [he]
    have hp : (fun x => s.indicator (fun _ : Ω => c) x * ρ x) =
        s.indicator (fun x => c * ρ x) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    refine ⟨(integrable_const c).indicator hs, ?_, ?_⟩
    · change Integrable (fun x => s.indicator (fun _ => c) x * ρ x) μ
      rw [hp]
      exact (hρ.const_mul c).indicator hs
    · change (∫ᵛ x, s.indicator (fun _ => c) x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ ρ]) =
        ∫ x, s.indicator (fun _ => c) x * ρ x ∂μ
      rw [VectorMeasure.integral_indicator_const c hs, withDensityᵥ_apply hρ hs,
        hp, integral_indicator hs, integral_const_mul]
      rfl
  | @add f g _ hf hg =>
    change (μ.withDensityᵥ ρ).Integrable (fun x => f x + g x) ∧ _
    have hp : (fun x => (f x + g x) * ρ x) =
        (fun x => f x * ρ x + g x * ρ x) := by ext x; ring
    refine ⟨hf.1.add hg.1, ?_, ?_⟩
    · change Integrable (fun x => (f x + g x) * ρ x) μ
      rw [hp]
      exact hf.2.1.add hg.2.1
    · change (∫ᵛ x, f x + g x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ ρ]) =
        ∫ x, (f x + g x) * ρ x ∂μ
      rw [VectorMeasure.integral_fun_add hf.1 hg.1, hf.2.2, hg.2.2, hp,
        integral_add hf.2.1 hg.2.1]

theorem integral_density (ρ : Ω → ℂ) (hρ : Integrable ρ μ)
    (g : Ω → ℂ) (hg : Measurable g) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C) :
    (∫ᵛ x, g x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ ρ]) =
      ∫ x, g x * ρ x ∂μ := by
  let := finite_variation μ ρ hρ
  let a := hg.stronglyMeasurable.approxBounded C
  have ha n x : ‖a n x‖ ≤ C := hg.stronglyMeasurable.norm_approxBounded_le hC n x
  have ht x : Tendsto (fun n => a n x) atTop (𝓝 (g x)) :=
    hg.stronglyMeasurable.tendsto_approxBounded_of_norm_le (hbound x)
  have hv := VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := μ.withDensityᵥ ρ) (B := ContinuousLinearMap.mul ℝ ℂ) (fun _ => C)
    (fun n => (a n).stronglyMeasurable.aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (ha n)) (Eventually.of_forall ht)
  have hp := tendsto_integral_of_dominated_convergence (fun x => C * ‖ρ x‖)
    (fun n => (a n).stronglyMeasurable.aestronglyMeasurable.mul hρ.aestronglyMeasurable)
    (hρ.norm.const_mul C)
    (fun n => Eventually.of_forall fun x => by
      change ‖a n x * ρ x‖ ≤ C * ‖ρ x‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ha n x) (norm_nonneg _))
    (Eventually.of_forall fun x => (ht x).mul_const (ρ x))
  have he : (fun n => ∫ᵛ x, a n x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ ρ]) =
      (fun n => ∫ x, a n x * ρ x ∂μ) := by
    funext n
    exact (simple_density μ ρ hρ (a n)).2.2
  rw [he] at hv
  exact tendsto_nhds_unique hv hp

end OperatorDerivativeRewrite.Foundation.ComplexDensityIntegral
