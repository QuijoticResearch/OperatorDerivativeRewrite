import Foundation.SchwartzCylinderObstruction
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Actual bounded continuous cylinder lifts and uniform quadrature bounds for Schwartz tests. -/
noncomputable section
open scoped SchwartzMap BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.SchwartzBoundedCylinders
variable {ι : Type*} [Fintype ι]

def coordinateLift (i : ι) : 𝓢(ℝ,ℝ) →L[ℝ] ((ι → ℝ) →ᵇ ℝ) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun x : ι → ℝ => x i, continuous_apply i⟩).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℝ ℝ ℝ)

theorem coordinateLift_apply (i : ι) (g : 𝓢(ℝ,ℝ)) (x : ι → ℝ) :
    coordinateLift i g x = g (x i) := rfl

theorem coordinateLift_bound (i : ι) (g : 𝓢(ℝ,ℝ)) :
    ‖coordinateLift i g‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
  change ‖g.toBoundedContinuousFunction.compContinuous
    (⟨fun x : ι → ℝ => x i, continuous_apply i⟩ : C(ι → ℝ,ℝ))‖ ≤ _
  exact (BoundedContinuousFunction.norm_compContinuous_le g.toBoundedContinuousFunction
    (⟨fun x : ι → ℝ => x i, continuous_apply i⟩ : C(ι → ℝ,ℝ))).trans
      g.norm_toBoundedContinuousFunction_le

def quadrature (w : ι → ℝ) : 𝓢(ℝ,ℝ) →L[ℝ] ((ι → ℝ) →ᵇ ℝ) :=
  ∑ i, w i • coordinateLift i

theorem quadrature_apply (w : ι → ℝ) (g : 𝓢(ℝ,ℝ)) (x : ι → ℝ) :
    quadrature w g x = ∑ i, w i*g (x i) := by
  simp [quadrature, coordinateLift_apply]

theorem quadrature_bound (w : ι → ℝ) (g : 𝓢(ℝ,ℝ)) :
    ‖quadrature w g‖ ≤ (∑ i, |w i|)*SchwartzMap.seminorm ℝ 0 0 g := by
  have he : quadrature w g = ∑ i, w i • coordinateLift i g := by
    ext x
    simp [quadrature]
  rw [he]
  calc
    _ ≤ ∑ i, ‖w i • coordinateLift i g‖ := norm_sum_le _ _
    _ = ∑ i, |w i| * ‖coordinateLift i g‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |w i| * SchwartzMap.seminorm ℝ 0 0 g := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (coordinateLift_bound i g) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

def pathQuadrature (w t : ι → ℝ) : 𝓢(ℝ,ℝ) →L[ℝ] (C(ℝ,ℝ) →ᵇ ℝ) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun ω i => ω (t i), continuous_pi (fun i => continuous_eval_const (t i))⟩).comp
      (quadrature w)

theorem pathQuadrature_apply (w t : ι → ℝ) (g : 𝓢(ℝ,ℝ)) (ω : C(ℝ,ℝ)) :
    pathQuadrature w t g ω = ∑ i, w i*g (ω (t i)) := quadrature_apply w g _

theorem pathQuadrature_bound (w t : ι → ℝ) (g : 𝓢(ℝ,ℝ)) :
    ‖pathQuadrature w t g‖ ≤ (∑ i, |w i|)*SchwartzMap.seminorm ℝ 0 0 g :=
  (BoundedContinuousFunction.norm_compContinuous_le (quadrature w g) _).trans
    (quadrature_bound w g)

end OperatorDerivativeRewrite.Foundation.SchwartzBoundedCylinders
