import Foundation.RootMarkComplexClarkLimit
import Foundation.RootMarkGKWConditioning
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Strong Hilbert convergence of actual prefix conditioning and stochastic projections. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RootMarkL2Limit
open RootMarkStochasticIntegral RootMarkGKWConditioning
open MarkedRootRenewalProcess (MarkSample marks)

def prefixSpace (n : ℕ) : Submodule ℂ (Lp ℂ 2 marks) := lpMeas ℂ ℂ (history n) 2 marks

private instance prefixFact (n : ℕ) :
    Fact ((history n) ≤ (inferInstance : MeasurableSpace MarkSample)) := ⟨history.le n⟩

instance prefixProjection (n : ℕ) : (prefixSpace n).HasOrthogonalProjection := by
  unfold prefixSpace
  infer_instance

theorem prefixSpace_mono : Monotone prefixSpace := by
  intro m n h Y hY
  obtain ⟨g,hg,he⟩ := hY
  exact ⟨g,hg.mono (history.mono h),he⟩

theorem prefix_projection_condExp_ae (n : ℕ) (Y : Lp ℂ 2 marks) :
    (prefixSpace n).starProjection Y =ᵐ[marks] marks[(Y : MarkSample → ℂ) | history n] := by
  have he := (Lp.memLp Y).condExpL2_ae_eq_condExp (𝕜 := ℂ) (history.le n)
  rw [Lp.toLp_coeFn] at he
  exact he

theorem conditionalValue_L2_limit (Y : Lp ℂ 2 marks) :
    Tendsto (fun n : ℕ => conditionalValue n Y) atTop (𝓝 Y) := by
  have hP := Submodule.starProjection_tendsto_closure_iSup prefixSpace prefixSpace_mono Y
  have hM := tendstoInMeasure_of_tendsto_Lp hP
  have hi : Integrable (Y : MarkSample → ℂ) marks :=
    memLp_one_iff_integrable.mp ((Lp.memLp Y).mono_exponent one_le_two)
  have hC := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (RootMarkComplexClarkLimit.integrable_condExp_L1_limit Y hi)
  have hC' := hC.congr (fun n => (prefix_projection_condExp_ae n Y).symm) (EventuallyEq.rfl)
  have he := tendstoInMeasure_ae_unique hM hC'
  have heq : (⨆ n : ℕ, prefixSpace n).topologicalClosure.starProjection Y = Y := Lp.ext he
  rw [heq] at hP
  exact hP

theorem stochastic_projection_L2_limit (a : ℝ) (ha : a ≠ 0) (Y : Lp ℂ 2 marks)
    (hmean : (∫ η, Y η ∂marks) = 0) :
    Tendsto (fun n : ℕ => RootMarkGKWProjection.projection a n Y) atTop (𝓝 Y) := by
  simpa only [projection_eq_conditionalValue a ha _ Y hmean] using conditionalValue_L2_limit Y

end OperatorDerivativeRewrite.Foundation.RootMarkL2Limit
