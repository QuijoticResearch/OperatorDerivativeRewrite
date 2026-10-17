import Foundation.GaussianAcceleratedKernelLimit
import Foundation.FixedLawPathObstruction

/-! The actual limiting Mehler kernels admit no realization from a deterministic
start with almost surely right-continuous paths, even after modification. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianKernelPathObstruction
open GaussianMehler GaussianAcceleratedKernelLimit FixedLawPathObstruction
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

local instance : NullSingletonClass γ := nullSingletonClass_gaussianReal (by norm_num)

theorem positive_row_law (X : ℝ → Ω → ℝ) (x : ℝ)
    (hlaw : ∀ t, 0 ≤ t → HasLaw (X t) (limitKernel t x) μ)
    (t : ℝ) (ht : 0 < t) : HasLaw (X t) γ μ := by
  have h := hlaw t ht.le
  simpa only [limit_positive t ht, Kernel.const_apply] using h

theorem zero_row_ae (X : ℝ → Ω → ℝ) (x : ℝ)
    (hlaw : ∀ t, 0 ≤ t → HasLaw (X t) (limitKernel t x) μ) :
    X 0 =ᵐ[μ] fun _ => x := by
  have h := hlaw 0 le_rfl
  rw [limit_zero, Kernel.id_apply] at h
  exact h.ae_eq_of_dirac

theorem no_in_measure_initial (X : ℝ → Ω → ℝ) (x : ℝ)
    (hlaw : ∀ t, 0 ≤ t → HasLaw (X t) (limitKernel t x) μ) :
    ¬ TendstoInMeasure μ (fun n => X (smallTime n)) atTop (fun _ => x) :=
  not_in_measure_constant μ γ (fun n => X (smallTime n))
    (fun n => positive_row_law μ X x hlaw _ (smallTime_positive n)) x

theorem no_right_continuous_paths (X : ℝ → Ω → ℝ) (x : ℝ)
    (hlaw : ∀ t, 0 ≤ t → HasLaw (X t) (limitKernel t x) μ) :
    ¬ ∀ᵐ ω ∂μ, ContinuousWithinAt (fun t => X t ω) (Ici 0) 0 :=
  not_right_continuous μ γ X x (zero_row_ae μ X x hlaw)
    (positive_row_law μ X x hlaw)

theorem no_right_continuous_modification (X Y : ℝ → Ω → ℝ) (x : ℝ)
    (hlaw : ∀ t, 0 ≤ t → HasLaw (X t) (limitKernel t x) μ)
    (hmod : ∀ t, Y t =ᵐ[μ] X t) :
    ¬ ∀ᵐ ω ∂μ, ContinuousWithinAt (fun t => Y t ω) (Ici 0) 0 := by
  apply no_right_continuous_paths μ Y x
  intro t ht
  exact (hlaw t ht).congr (hmod t)

end OperatorDerivativeRewrite.Foundation.GaussianKernelPathObstruction
