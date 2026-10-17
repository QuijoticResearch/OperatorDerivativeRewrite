import Foundation.HigherHeatRealizationClassification
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-! Bounded continuous soft-sign tests detect the full mass of an integrable real density. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ContinuousDensityDuality
variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]

def softSign (f : α → ℝ) (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) : α →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f x / (|f x|+ε))
    (hf.div (hf.abs.add continuous_const) (fun x => ne_of_gt (by positivity))) 1 (by
      intro x
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0 < |f x|+ε)]
      exact (div_le_one (by positivity)).2 (by linarith [abs_nonneg (f x)]))

theorem softSign_bound (f : α → ℝ) (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) (x : α) :
    ‖softSign f hf ε hε x‖ ≤ 1 := by
  change ‖f x/(|f x|+ε)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0 < |f x|+ε)]
  exact (div_le_one (by positivity)).2 (by linarith [abs_nonneg (f x)])

theorem density_dual_approximation (μ : Measure α) (f : α → ℝ) (hf : Continuous f)
    (hi : Integrable f μ) :
    Tendsto (fun n : ℕ => ∫ x, f x * softSign f hf (1/(n+1:ℝ)) (by positivity) x ∂μ)
      atTop (𝓝 (∫ x, ‖f x‖ ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact (hf.mul (softSign f hf _ _).continuous).aestronglyMeasurable
  · exact hi.norm
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (softSign_bound f hf _ _ x)
  · apply Eventually.of_forall
    intro x
    by_cases hx : f x=0
    · simp [softSign,hx]
    · have ha : |f x| ≠ 0 := abs_ne_zero.mpr hx
      have ht : Tendsto (fun n : ℕ => f x * (f x/(|f x|+1/(n+1:ℝ))))
          atTop (𝓝 (f x * (f x/(|f x|+0)))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.div
        (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (𝓝 0))) (by simpa using ha))
      have he : f x * (f x / (|f x|+0))=‖f x‖ := by
        rw [add_zero,Real.norm_eq_abs]
        field_simp
        nlinarith [sq_abs (f x)]
      change Tendsto (fun n : ℕ => f x * (f x/(|f x|+1/(n+1:ℝ)))) atTop (𝓝 ‖f x‖)
      simpa only [he] using ht

theorem exists_norm_one_test (μ : Measure α) (f : α → ℝ) (hf : Continuous f)
    (hi : Integrable f μ) (C : ℝ) (hC : C < ∫ x, ‖f x‖ ∂μ) :
    ∃ g : α →ᵇ ℝ, (∀ x, ‖g x‖ ≤ 1) ∧ C < ∫ x, f x*g x ∂μ := by
  have ht := density_dual_approximation μ f hf hi
  obtain ⟨n,hn⟩ := (ht.eventually (eventually_gt_nhds hC)).exists
  exact ⟨softSign f hf (1/(n+1:ℝ)) (by positivity),softSign_bound f hf _ _,hn⟩

end OperatorDerivativeRewrite.Foundation.ContinuousDensityDuality
