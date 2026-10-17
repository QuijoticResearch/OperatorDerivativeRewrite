import Foundation.BrownianRestartConditioning
import Foundation.BrownianContinuousPathLaw

/-! The whole actual continuous future at a bounded stopping time has Wiener
law and is independent of the stopped past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianBoundedStrongMarkov
open InfiniteGaussian BrownianMassClockStoppingTime BrownianBoundedRestartProcess
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

include hτ in
theorem path_law (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    gaussianProduct.map (path τ) = gaussianProduct.map IBMConstructedSources.clockPath := by
  exact BrownianContinuousPathLaw.path_law_unique _ _ _ _ (path_measurable τ hτ)
    IBMConstructedSources.clockPath_measurable
    (isBrownian τ hτ N hN).toIsPreBrownianReal
    IBMConstructedSources.clock_isBrownian.toIsPreBrownianReal

theorem conditional_path_law (N : ℕ) (hN : ∀ ω, τ ω ≤ N)
    (A : Set SampleSpace) (hA : MeasurableSet[hτ.measurableSpace] A)
    (hμA : gaussianProduct A ≠ 0) :
    gaussianProduct[|A].map (path τ) = gaussianProduct.map (path τ) := by
  exact BrownianContinuousPathLaw.path_law_unique _ _ _ _ (path_measurable τ hτ)
    (path_measurable τ hτ)
    (BrownianRestartConditioning.isBrownian_cond τ hτ N hN A hA hμA).toIsPreBrownianReal
    (isBrownian τ hτ N hN).toIsPreBrownianReal

theorem path_independent (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    Indep (MeasurableSpace.comap (path τ) inferInstance) hτ.measurableSpace
      gaussianProduct := by
  apply (indep_iff_forall_indepSet gaussianProduct).mpr
  intro S A hS hA
  obtain ⟨B,hB,rfl⟩ := hS
  have hp := path_measurable τ hτ
  apply (indepSet_iff_measure_inter_eq_mul (hp hB)
    (hτ.measurableSpace_le A hA) gaussianProduct).mpr
  by_cases hμA : gaussianProduct A = 0
  · rw [measure_mono_null inter_subset_right hμA,hμA,mul_zero]
  · have he := congrArg (fun ν : Measure C(ℝ≥0, ℝ) => ν B)
      (conditional_path_law τ hτ N hN A hA hμA)
    rw [Measure.map_apply hp hB,Measure.map_apply hp hB,cond_apply' (hp hB)] at he
    have hh := congrArg (fun x => gaussianProduct A * x) he
    rw [← mul_assoc,ENNReal.mul_inv_cancel hμA (measure_ne_top _ _),one_mul] at hh
    rw [inter_comm]
    exact hh.trans (mul_comm _ _)

end OperatorDerivativeRewrite.Foundation.BrownianBoundedStrongMarkov
