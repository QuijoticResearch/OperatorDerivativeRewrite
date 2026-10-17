import Foundation.ComplexRootPoissonTrajectory

/-! Exact marginal laws and operator expectations of the constructed infinite process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder Finset
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonMarginals
open ComplexRootPoissonKernel ComplexRootPoissonTrajectory ComplexRootPoissonSemigroup

theorem marginal_successor (a : ℝ) (δ : ℝ≥0) (n : ℕ) :
    (law a δ).map (coordinate (n+1)) =
      kernel a δ ∘ₘ (law a δ).map (coordinate n) := by
  have he := congrArg Measure.snd (joint_next a δ n)
  rw [Measure.snd_compProd] at he
  rw [Measure.snd, Measure.map_map measurable_snd
    ((measurable_frestrictLe n).prodMk (coordinate_measurable (n+1)))] at he
  change historyKernel a δ n ∘ₘ (law a δ).map (frestrictLe n) =
    (law a δ).map (coordinate (n+1)) at he
  have hm : Measurable (fun h : History n => h ⟨n, by simp⟩) :=
    measurable_pi_apply (X := fun _ : ↥(Iic n) => ℂ) ⟨n, by simp⟩
  rw [← he, historyKernel, ← Kernel.comp_deterministic_eq_comap,
    ← Measure.comp_assoc, Measure.deterministic_comp_eq_map,
    Measure.map_map hm (measurable_frestrictLe n)]
  rfl

theorem marginal_kernel (a : ℝ) (δ : ℝ≥0) (n : ℕ) :
    (law a δ).map (coordinate n) = kernel a (n • δ) 0 := by
  induction n with
  | zero => rw [initial_law, zero_nsmul, kernel_zero, Kernel.id_apply]
  | succ n ih =>
    rw [marginal_successor, ih, succ_nsmul,
      kernel_add, Kernel.comp_apply]

theorem coordinate_integral (a : ℝ) (δ : ℝ≥0) (n : ℕ)
    (f : ComplexRootTransitionOperator.Test) :
    (∫ ω, f (coordinate n ω) ∂law a δ) = transition a (n • δ : ℝ≥0) f 0 := by
  rw [← integral_map (coordinate_measurable n).aemeasurable
    f.continuous.aestronglyMeasurable, marginal_kernel, kernel_integral]

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonMarginals
