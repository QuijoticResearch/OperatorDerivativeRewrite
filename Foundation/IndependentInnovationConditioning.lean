import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Basic

/-! Native conditioning of an independent standard-Borel innovation on an arbitrary past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.IndependentInnovationConditioning

variable {Ω P S E : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace S]
  [StandardBorelSpace S] [Nonempty S] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (past : Ω → P) (fresh : Ω → S) (hp : Measurable past) (hf : Measurable fresh)
  (hi : IndepFun past fresh μ)

include hp hf hi

theorem conditional_law :
    condDistrib fresh past μ =ᵐ[μ.map past] Kernel.const P (μ.map fresh) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd hp.aemeasurable hf.aemeasurable
  rw [Measure.compProd_const]
  exact (indepFun_iff_map_prod_eq_prod_map_map hp.aemeasurable hf.aemeasurable).mp hi

theorem conditional_integral (F : P × S → E) (hF : StronglyMeasurable F)
    (hInt : Integrable (fun ω => F (past ω, fresh ω)) μ) :
    μ[fun ω => F (past ω,fresh ω) | MeasurableSpace.comap past inferInstance] =ᵐ[μ]
      fun ω => ∫ y, F (past ω,y) ∂μ.map fresh := by
  have he := condExp_prod_ae_eq_integral_condDistrib hp hf.aemeasurable hF hInt
  have hk := ae_of_ae_map hp.aemeasurable (conditional_law μ past fresh hp hf hi)
  filter_upwards [he,hk] with ω he hk
  rw [he,hk,Kernel.const_apply]

end OperatorDerivativeRewrite.Foundation.IndependentInnovationConditioning
