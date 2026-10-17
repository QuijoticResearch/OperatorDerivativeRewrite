import Foundation.MarkedOperatorConditional
import Foundation.ComplexRootPoissonTransform

/-! Unbounded holomorphic exponential conditioning for the genuine complex marked process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedHolomorphicExponential
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedConditionalPolynomial MarkedPastReconstruction
open MarkedOperatorConditional

def symbol (a ξ : ℝ) : ℂ := ComplexFourthRootWalk.stepTransform a ξ-1

def phase (a ξ : ℝ) (t : ℝ≥0) (ω : StateSample) : ℂ :=
  Complex.exp (Complex.I*(ξ : ℂ)*process a t ω)

theorem phase_adapted (a ξ : ℝ) : StronglyAdapted (history a) (phase a ξ) := by
  intro t
  exact ((measurable_const.mul (process_adapted a t).measurable).cexp).stronglyMeasurable

theorem phase_integrable (a ξ : ℝ) (t : ℝ≥0) : Integrable (phase a ξ t) probability := by
  have hm : Measurable (fun z : ℂ => Complex.exp (Complex.I*(ξ : ℂ)*z)) := by fun_prop
  have hi : Integrable (fun z : ℂ => Complex.exp (Complex.I*(ξ : ℂ)*z))
      (probability.map (process a t)) := by
    rw [process_law]
    exact ComplexRootPoissonTransform.exponential_integrable t a ξ
  exact (integrable_map_measure hm.aestronglyMeasurable
    (process_measurable a t).aemeasurable).mp hi

theorem phase_mean (a ξ : ℝ) (t : ℝ≥0) :
    (∫ ω, phase a ξ t ω ∂probability) = Complex.exp ((t : ℂ)*symbol a ξ) := by
  have hm : Measurable (fun z : ℂ => Complex.exp (Complex.I*(ξ : ℂ)*z)) := by fun_prop
  have he := integral_map (μ := probability) (process_measurable a t).aemeasurable
    hm.aestronglyMeasurable
  rw [process_law,ComplexRootPoissonTransform.transform] at he
  exact he.symm

theorem phase_condExp (a ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[phase a ξ t | history a s] =ᵐ[probability]
      fun ω => phase a ξ s ω*Complex.exp (((t-s : ℝ≥0) : ℂ)*symbol a ξ) := by
  let F : PastPath s × ℂ → ℂ :=
    fun p => Complex.exp (Complex.I*(ξ : ℂ)*(p.1 ⟨s,by simp⟩+p.2))
  have hm : Measurable F := by
    apply Measurable.cexp
    exact measurable_const.mul
      (((measurable_pi_apply (⟨s,by simp⟩ : Set.Iic s)).comp measurable_fst).add measurable_snd)
  have hfun : (fun ω => F (pastPath a s ω,increment a s t ω)) = phase a ξ t := by
    funext ω
    dsimp only [F,pastPath,increment,phase,process]
    congr 2
    abel
  have hi : Integrable (fun ω => F (pastPath a s ω,increment a s t ω)) probability := by
    rw [hfun]
    exact phase_integrable a ξ t
  have he := IndependentInnovationConditioning.conditional_integral probability
    (pastPath a s) (increment a s t) (pastPath_measurable a s)
    (increment_measurable a s t) (past_increment_independent a s t hst)
    F hm.stronglyMeasurable hi
  rw [hfun,← history_eq_past,increment_law a s t hst] at he
  filter_upwards [he] with ω he
  rw [he]
  change (∫ y : ℂ, Complex.exp (Complex.I*(ξ : ℂ)*(process a s ω+y))
    ∂ComplexRootPoissonLaw.law (t-s) a) = _
  simp_rw [mul_add,Complex.exp_add]
  rw [integral_const_mul,ComplexRootPoissonTransform.transform]
  rfl

end OperatorDerivativeRewrite.Foundation.MarkedHolomorphicExponential
