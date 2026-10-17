import Foundation.ComplexDensityIntegral

/-! Unbounded complex density transfer, justified by actual absolute integrability. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexDensityUnbounded

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem integrable_density (ρ : Ω → ℂ) (hρ : Integrable ρ μ)
    (g : Ω → ℂ) (hg : Measurable g) (hp : Integrable (fun x => g x * ρ x) μ) :
    (μ.withDensityᵥ ρ).Integrable g := by
  rw [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hρ]
  apply (integrable_withDensity_iff_integrable_smul₀'
    hρ.aestronglyMeasurable.enorm (Eventually.of_forall fun _ => enorm_lt_top)).mpr
  simp only [toReal_enorm]
  apply hp.norm.mono' (hρ.aestronglyMeasurable.norm.smul hg.aestronglyMeasurable)
  filter_upwards with x
  simp [mul_comm]

theorem integrable_product (ρ : Ω → ℂ) (hρ : Integrable ρ μ)
    (g : Ω → ℂ) (hg : Measurable g) (hv : (μ.withDensityᵥ ρ).Integrable g) :
    Integrable (fun x => g x * ρ x) μ := by
  rw [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hρ] at hv
  have hi := (integrable_withDensity_iff_integrable_smul₀'
    hρ.aestronglyMeasurable.enorm (Eventually.of_forall fun _ => enorm_lt_top)).mp hv
  simp only [toReal_enorm] at hi
  apply hi.norm.mono' (hg.aestronglyMeasurable.mul hρ.aestronglyMeasurable)
  filter_upwards with x
  simp [mul_comm]

theorem integrable_density_iff (ρ : Ω → ℂ) (hρ : Integrable ρ μ)
    (g : Ω → ℂ) (hg : Measurable g) :
    (μ.withDensityᵥ ρ).Integrable g ↔ Integrable (fun x => g x * ρ x) μ :=
  ⟨integrable_product μ ρ hρ g hg, integrable_density μ ρ hρ g hg⟩

theorem integral_density (ρ : Ω → ℂ) (hρ : Integrable ρ μ)
    (g : Ω → ℂ) (hg : Measurable g) (hp : Integrable (fun x => g x * ρ x) μ) :
    (∫ᵛ x, g x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ ρ]) =
      ∫ x, g x * ρ x ∂μ := by
  let S (n : ℕ) := {x | ‖g x‖ ≤ (n : ℝ)}
  have hS n : MeasurableSet (S n) := measurableSet_le hg.norm measurable_const
  let a (n : ℕ) := (S n).indicator g
  have hm n : Measurable (a n) := hg.indicator (hS n)
  have hb n x : ‖a n x‖ ≤ (n : ℝ) := by
    by_cases hx : x ∈ S n
    · change ‖(S n).indicator g x‖ ≤ (n : ℝ)
      rw [Set.indicator_of_mem hx]
      exact hx
    · simp [a, hx]
  have hnorm n x : ‖a n x‖ ≤ ‖g x‖ := norm_indicator_le_norm_self _ _
  have ht x : Tendsto (fun n => a n x) atTop (𝓝 (g x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖g x‖] with n hn
    simp [a, S, hn]
  have hi := integrable_density μ ρ hρ g hg hp
  have hv := VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := μ.withDensityᵥ ρ) (B := ContinuousLinearMap.mul ℝ ℂ) (fun x => ‖g x‖)
    (fun n => (hm n).aestronglyMeasurable) hi.norm
    (fun n => Eventually.of_forall (hnorm n)) (Eventually.of_forall ht)
  have hs := tendsto_integral_of_dominated_convergence (fun x => ‖g x * ρ x‖)
    (fun n => (hm n).aestronglyMeasurable.mul hρ.aestronglyMeasurable) hp.norm
    (fun n => Eventually.of_forall fun x => by
      change ‖a n x * ρ x‖ ≤ ‖g x * ρ x‖
      simpa only [norm_mul] using
        mul_le_mul_of_nonneg_right (hnorm n x) (norm_nonneg (ρ x)))
    (Eventually.of_forall fun x => (ht x).mul_const (ρ x))
  have he : (fun n => ∫ᵛ x, a n x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ ρ]) =
      (fun n => ∫ x, a n x * ρ x ∂μ) := by
    funext n
    exact ComplexDensityIntegral.integral_density μ ρ hρ (a n) (hm n) n
      (Nat.cast_nonneg n) (hb n)
  rw [he] at hv
  exact tendsto_nhds_unique hv hs

end OperatorDerivativeRewrite.Foundation.ComplexDensityUnbounded
