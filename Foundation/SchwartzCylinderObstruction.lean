import Foundation.GaussianSchwartzKernel
import Mathlib.Analysis.Normed.Group.Bounded

/-! Native decay excludes nonzero additive coordinate cylinders from multivariate Schwartz space. -/
noncomputable section
open Filter Bornology
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.SchwartzCylinderObstruction

theorem real_escape : Tendsto (fun t : ℝ => t) atTop (cocompact ℝ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  exact tendsto_atTop_mono (fun t : ℝ => le_abs_self t) tendsto_id

theorem second_escape (x : ℝ) :
    Tendsto (fun t : ℝ => (x,t)) atTop (cocompact (ℝ × ℝ)) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  apply tendsto_atTop_mono _ tendsto_id
  intro t
  exact (le_abs_self t).trans (by simp only [Prod.norm_def, Real.norm_eq_abs]; exact le_max_right _ _)

theorem first_escape (y : ℝ) :
    Tendsto (fun t : ℝ => (t,y)) atTop (cocompact (ℝ × ℝ)) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  apply tendsto_atTop_mono _ tendsto_id
  intro t
  exact (le_abs_self t).trans (by simp only [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _)

theorem additive_cylinder_zero (g h : 𝓢(ℝ,ℝ)) (F : 𝓢(ℝ × ℝ,ℝ))
    (hF : ∀ x y, F (x,y) = g x + h y) : g = 0 ∧ h = 0 := by
  constructor
  · ext x
    have hz := F.tendsto_cocompact.comp (second_escape x)
    have he := (tendsto_const_nhds (x := g x)).add (h.tendsto_cocompact.comp real_escape)
    have ht : Tendsto (fun t : ℝ => F (x,t)) atTop (𝓝 (g x)) := by
      simpa only [Function.comp_def, hF, add_zero] using he
    exact tendsto_nhds_unique ht hz
  · ext y
    have hz := F.tendsto_cocompact.comp (first_escape y)
    have he := (g.tendsto_cocompact.comp real_escape).add (tendsto_const_nhds (x := h y))
    have ht : Tendsto (fun t : ℝ => F (t,y)) atTop (𝓝 (h y)) := by
      simpa only [Function.comp_def, hF, zero_add] using he
    exact tendsto_nhds_unique ht hz

theorem nonzero_sum_not_schwartz (g : 𝓢(ℝ,ℝ)) (hg : g ≠ 0) :
    ¬ ∃ F : 𝓢(ℝ × ℝ,ℝ), ∀ x y, F (x,y) = g x + g y := by
  rintro ⟨F,hF⟩
  exact hg (additive_cylinder_zero g g F hF).1

theorem weighted_sum_not_schwartz (g : 𝓢(ℝ,ℝ)) (hg : g ≠ 0)
    (a b : ℝ) (ha : a ≠ 0) :
    ¬ ∃ F : 𝓢(ℝ × ℝ,ℝ), ∀ x y, F (x,y) = a*g x + b*g y := by
  rintro ⟨F,hF⟩
  have hz : a • g = 0 := (additive_cylinder_zero (a • g) (b • g) F (by
    intro x y
    change F (x,y) = a*g x + b*g y
    exact hF x y)).1
  exact (smul_eq_zero.mp hz).elim ha hg

theorem gaussian_sum_not_schwartz :
    ¬ ∃ F : 𝓢(ℝ × ℝ,ℝ), ∀ x y, F (x,y) = Real.exp (-x^2)+Real.exp (-y^2) := by
  apply nonzero_sum_not_schwartz GaussianSchwartzKernel.realSchwartz
  intro h
  have he := congrArg (fun g : 𝓢(ℝ,ℝ) => g 0) h
  change Real.exp (-(0 : ℝ)^2) = 0 at he
  norm_num at he

end OperatorDerivativeRewrite.Foundation.SchwartzCylinderObstruction
