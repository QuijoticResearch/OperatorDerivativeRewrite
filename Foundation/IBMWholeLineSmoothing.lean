import Foundation.IBMContinuousDerivative

/-! Transfer compact-interval Gaussian smoothing bounds to genuine whole-line convolution. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open InfiniteGaussian GaussianHilbertProcess FractionalSpectralKernel
open IBMFiniteScenerySmoothing
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

/-- A kernel whose shifted support lies inside `[a,b]` has the same
whole-line and compact-interval Bochner convolutions. -/
theorem wholeLineScenery_eq_kernelScenery (a b x : ℝ) (ρ : ℝ → ℝ)
    (hsupp : ∀ r, r ∉ Set.Icc a b → ρ (x - r) = 0) :
    wholeLineScenery ρ x = kernelScenery a b x ρ := by
  rw [wholeLineScenery_eq_integral, kernelScenery]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (f := fun r : ℝ => ρ (x - r) • sourceScenery r)
    (s := Set.Icc a b)
    (fun r hr => by simp [hsupp r hr])).symm

theorem wholeLineScenery_eq_embedding (a b x : ℝ) (ρ : ℝ → ℝ)
    (hsupp : ∀ r, r ∉ Set.Icc a b → ρ (x - r) = 0) :
    wholeLineScenery ρ x =
      isonormalEmbedding SpectralSpace (kernelDirection a b x ρ) := by
  rw [wholeLineScenery_eq_kernelScenery a b x ρ hsupp,
    kernelScenery_eq_embedding]

/-- Quantitative Gaussian L² smoothing of the actual whole-line convolution
under positive mass-one support in a radius `δ`. -/
theorem wholeLineScenery_error_sq_le (a b x δ : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ)
    (hsupp : ∀ r, r ∉ Set.Icc a b → ρ (x - r) = 0)
    (hmass : (∫ r in Set.Icc a b, ρ (x - r)) = 1)
    (hw : ∀ r ∈ Set.Icc a b, 0 ≤ ρ (x - r))
    (hδ : 0 ≤ δ) (hradius : ∀ r ∈ Set.Icc a b, |r - x| ≤ δ) :
    ‖wholeLineScenery ρ x - sourceScenery x‖ ^ 2 ≤ δ := by
  rw [wholeLineScenery_eq_kernelScenery a b x ρ hsupp]
  exact kernelScenery_error_sq_le a b x δ hρ hmass hw hδ hradius

/-- Actual whole-line Gaussian L² convolutions converge to the original
scenery coordinate for shrinking positive normalized support intervals. -/
theorem wholeLineScenery_tendsto
    (a b δ : ℕ → ℝ) (ρ : ℕ → ℝ → ℝ) (x : ℝ)
    (hρ : ∀ n, Continuous (ρ n))
    (hsupp : ∀ n r, r ∉ Set.Icc (a n) (b n) → ρ n (x - r) = 0)
    (hmass : ∀ n, (∫ r in Set.Icc (a n) (b n), ρ n (x - r)) = 1)
    (hw : ∀ n r, r ∈ Set.Icc (a n) (b n) → 0 ≤ ρ n (x - r))
    (hδ : ∀ n, 0 ≤ δ n)
    (hradius : ∀ n r, r ∈ Set.Icc (a n) (b n) → |r - x| ≤ δ n)
    (hδlim : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => wholeLineScenery (ρ n) x) Filter.atTop
      (nhds (sourceScenery x)) := by
  have heq : (fun n => wholeLineScenery (ρ n) x) =
      (fun n => kernelScenery (a n) (b n) x (ρ n)) := by
    funext n
    exact wholeLineScenery_eq_kernelScenery (a n) (b n) x (ρ n) (hsupp n)
  rw [heq]
  exact kernelScenery_tendsto a b δ ρ x hρ hmass hw hδ hradius hδlim

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
