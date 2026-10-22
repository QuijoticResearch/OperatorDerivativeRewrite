import Foundation.IBMClockGermLocalization
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Bounded whole-past factors and dominated pairings for actual IBM localization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundedGermFactors
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMConstructedSources
open IBMIntrinsicRightGerm IBMClippedSceneryForecast IBMClockGermLocalization
set_option backward.isDefEq.respectTransparency false

def clamp (C x : ℝ) : ℝ := max (-C) (min C x)

theorem clamp_measurable (C : ℝ) : Measurable (clamp C) :=
  measurable_const.max (measurable_const.min measurable_id)

theorem clamp_bound {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clamp C x| ≤ C := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clamp_eq {C x : ℝ} (hx : |x| ≤ C) : clamp C x = x := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  rw [clamp, min_eq_right hu, max_eq_right hl]

theorem exists_bounded_past_factor (s : ℝ≥0) (f : JointL2) (hf : f ∈ past s)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |f ω| ≤ C) :
    ∃ g : (Iic s → ℝ) → ℝ, Measurable g ∧ (∀ p, |g p| ≤ C) ∧
      GaussianPredictableStep.pastCoefficient ibmValue s g =ᵐ[IBMSourceLaws.jointMeasure] f := by
  change AEStronglyMeasurable[naturalFiltration s] f IBMSourceLaws.jointMeasure at hf
  obtain ⟨g, hg, he⟩ := (GaussianPredictableStep.measurable_natural_iff_exists_pastCoefficient
    (fun t => (point_stronglyMeasurable t).measurable) s (hf.mk f)).mp
      hf.stronglyMeasurable_mk.measurable
  refine ⟨fun p => clamp C (g p), (clamp_measurable C).comp hg,
    fun p => clamp_bound hC _, ?_⟩
  have heq := hf.ae_eq_mk.trans (EventuallyEq.of_eq he)
  filter_upwards [heq, hb] with ω hω hbω
  change clamp C (GaussianPredictableStep.pastCoefficient ibmValue s g ω) = f ω
  rw [← hω, clamp_eq hbω]

theorem bounded_germ_factors (f : JointL2) (hf : f ∈ rightPast 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |f ω| ≤ C)
    (τ : ℕ → ℝ≥0) (hτ : ∀ n, 0 < τ n) :
    ∃ g : (n : ℕ) → (Iic (τ n) → ℝ) → ℝ,
      (∀ n, Measurable (g n)) ∧ (∀ n p, |g n p| ≤ C) ∧
      (∀ n, GaussianPredictableStep.pastCoefficient ibmValue (τ n) (g n)
        =ᵐ[IBMSourceLaws.jointMeasure] f) := by
  have hex n := exists_bounded_past_factor (τ n) f (rightPast_le_past (hτ n) hf) C hC hb
  choose g hg hb he using hex
  exact ⟨g, hg, hb, he⟩

theorem localized_pairing_tendsto (δ : ℝ≥0) (hδ : 0 < δ)
    (τ : ℕ → ℝ≥0) (hτ : Tendsto τ atTop (𝓝 0))
    (g : (n : ℕ) → (Iic (τ n) → ℝ) → ℝ) (hg : ∀ n, Measurable (g n))
    (C : ℝ) (hb : ∀ n p, |g n p| ≤ C) (f : IBMSourceLaws.JointSample → ℝ)
    (hf : ∀ n, GaussianPredictableStep.pastCoefficient ibmValue (τ n) (g n)
      =ᵐ[IBMSourceLaws.jointMeasure] f)
    (A : IBMSourceLaws.JointSample → ℝ) (hA : Integrable A IBMSourceLaws.jointMeasure) :
    Tendsto (fun n => ∫ ω, A ω * GaussianPredictableStep.pastCoefficient
      (actualValue δ) (τ n) (g n) ω ∂IBMSourceLaws.jointMeasure)
      atTop (𝓝 (∫ ω, A ω * f ω ∂IBMSourceLaws.jointMeasure)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖A ω‖ * C)
  · intro n
    exact hA.aestronglyMeasurable.mul
      ((hg n).comp (Measurable.of_eval fun r => actual_measurable δ r)).aestronglyMeasurable
  · exact hA.norm.mul_const C
  · intro n
    exact ae_of_all _ fun ω => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb n _) (abs_nonneg _)
  · filter_upwards [past_functional_tendsto δ hδ τ hτ g f hf] with ω hω
    exact tendsto_const_nhds.mul hω

end OperatorDerivativeRewrite.Foundation.IBMBoundedGermFactors
