import Foundation.GaussianTimeProcess
import Foundation.GaussianPredictableStep
import Foundation.IndependentInnovationConditioning

/-! Actual Gaussian transition conditioning on the ENTIRE raw Brownian history.
Integrability is explicit; no boundedness or current-value-only conditioning. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianBrownianConditionalTransition
open InfiniteGaussian GaussianTimeProcess GaussianPredictableStep

def past (S : ℝ≥0) : SampleSpace → (Iic S → ℝ) := pastProcess process S

theorem past_measurable (S : ℝ≥0) : Measurable (past S) :=
  measurable_pi_iff.mpr fun r => (process_stronglyMeasurable r.val).measurable

theorem history_eq_comap (S : ℝ≥0) :
    naturalFiltration S = MeasurableSpace.comap (past S) inferInstance := by
  rw [naturalFiltration, Filtration.natural_eq_comap]
  rfl

theorem past_increment_independent (S T : ℝ≥0) (hST : S ≤ T) :
    IndepFun (past S) (fun Y => process T Y-process S Y) gaussianProduct := by
  have h := (process_isPreBrownian.indepFun_shift S).symm.comp measurable_id
    (measurable_pi_apply (T-S))
  change IndepFun (fun Y (r : Iic S) => process r.val Y)
    (fun Y => process T Y-process S Y) gaussianProduct
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hST] using h

theorem increment_law (S T : ℝ≥0) (hST : S ≤ T) :
    HasLaw (fun Y => process T Y-process S Y) (gaussianReal 0 (T-S)) gaussianProduct := by
  simpa only [add_tsub_cancel_of_le hST] using
    (process_isPreBrownian.shift S).hasLaw_eval (T-S)

theorem conditional_transition {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S T : ℝ≥0) (hST : S ≤ T) (f : ℝ → E)
    (hf : StronglyMeasurable f) (hi : Integrable (fun Y => f (process T Y)) gaussianProduct) :
    gaussianProduct[fun Y => f (process T Y) | naturalFiltration S] =ᵐ[gaussianProduct]
      fun Y => ∫ y, f (process S Y+y) ∂gaussianReal 0 (T-S) := by
  let F : (Iic S → ℝ) × ℝ → E := fun p => f (p.1 ⟨S,by simp⟩+p.2)
  have hF : StronglyMeasurable F := hf.comp_measurable
    (((measurable_pi_apply (⟨S,by simp⟩ : Iic S)).comp measurable_fst).add measurable_snd)
  have he : (fun Y => F (past S Y,process T Y-process S Y)) =
      (fun Y => f (process T Y)) := by
    funext Y
    dsimp [F,past,pastProcess]
    congr 1
    ring
  have h := IndependentInnovationConditioning.conditional_integral gaussianProduct
    (past S) (fun Y => process T Y-process S Y) (past_measurable S)
    ((process_stronglyMeasurable T).measurable.sub (process_stronglyMeasurable S).measurable)
    (past_increment_independent S T hST) F hF (he.symm ▸ hi)
  rw [he, ← history_eq_comap S, (increment_law S T hST).map_eq] at h
  exact h

end OperatorDerivativeRewrite.Foundation.GaussianBrownianConditionalTransition
