import Foundation.MarkedPastFutureIndependence
import Foundation.ComplexRootPoissonPolynomialDomain
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic

/-! A native complex martingale on the actual cadlag compound-root source and its natural past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedRenewalMartingale
open MarkedRootRenewalProcess MarkedRenewalRegeneration MarkedPastReconstruction

def process (a : ℝ) (t : ℝ≥0) : StateSample → ℂ := MarkedRootRenewalProcess.process a t

theorem process_measurable (a : ℝ) (t : ℝ≥0) : Measurable (process a t) :=
  MarkedRootRenewalProcess.process_measurable a t

def history (a : ℝ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace StateSample) :=
  Filtration.natural (process a) (fun t => (process_measurable a t).stronglyMeasurable)

theorem process_adapted (a : ℝ) : StronglyAdapted (history a) (process a) :=
  Filtration.stronglyAdapted_natural (u := process a)
    (fun t : ℝ≥0 => (process_measurable a t).stronglyMeasurable)

theorem difference_eq_future (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) (ω : StateSample) :
    process a t ω-process a s ω = (futurePath a s ω) (t-s) := by
  have hsum : (s : ℝ)+((t-s : ℝ≥0) : ℝ) = (t : ℝ) := by rw [NNReal.coe_sub hst]; ring
  simp only [process,futurePath,hsum]

theorem difference_independent_past (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => process a t ω-process a s ω) inferInstance)
      (history a s) probability := by
  have hi := (MarkedPastFutureIndependence.past_future_independent a s).symm.comp
    (measurable_pi_apply (t-s)) measurable_id
  have he : (fun ω => process a t ω-process a s ω) =
      (fun γ : ProcessPath => γ (t-s)) ∘ futurePath a s :=
    funext (difference_eq_future a s t hst)
  rw [he,history,Filtration.natural_eq_comap]
  exact hi

theorem process_law (a : ℝ) (t : ℝ≥0) :
    probability.map (process a t) = ComplexRootPoissonLaw.law t a :=
  ConstructedRenewalPoissonLaw.process_law_eq_poisson a t

theorem process_power_integrable (a : ℝ) (t : ℝ≥0) (k : ℕ) :
    Integrable (fun ω => process a t ω^k) probability := by
  have hm : Measurable (fun z : ℂ => z^k) := by fun_prop
  have hi : Integrable (fun z : ℂ => z^k) (probability.map (process a t)) := by
    rw [process_law]
    exact ComplexRootPoissonPolynomialDomain.power_integrable t a k
  exact (integrable_map_measure hm.aestronglyMeasurable (process_measurable a t).aemeasurable).mp hi

theorem process_integrable (a : ℝ) (t : ℝ≥0) : Integrable (process a t) probability := by
  simpa only [pow_one] using process_power_integrable a t 1

theorem compound_mean_zero (a : ℝ) (t : ℝ≥0) :
    (∫ z : ℂ, z ∂ComplexRootPoissonLaw.law t a) = 0 := by
  have he := ComplexRootPoissonPolynomialDomain.power_mixture t a 1
  simpa [ComplexFourthRootWalk.terminal_mean] using he

theorem process_mean (a : ℝ) (t : ℝ≥0) : (∫ ω, process a t ω ∂probability) = 0 := by
  have he := integral_map (μ := probability) (process_measurable a t).aemeasurable
    (measurable_id : Measurable (id : ℂ → ℂ)).aestronglyMeasurable
  rw [process_law] at he
  simp only [id_eq] at he
  rw [compound_mean_zero] at he
  exact he.symm

theorem difference_mean (a : ℝ) (s t : ℝ≥0) :
    (∫ ω, process a t ω-process a s ω ∂probability) = 0 := by
  rw [integral_sub (process_integrable a t) (process_integrable a s),
    process_mean,process_mean,sub_self]

theorem difference_condExp (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[fun ω => process a t ω-process a s ω | history a s] =ᵐ[probability] fun _ => 0 := by
  have hm := (process_measurable a t).sub (process_measurable a s)
  have he := condExp_indep_eq hm.comap_le ((history a).le s)
    (comap_measurable (fun ω => process a t ω-process a s ω)).stronglyMeasurable
    (difference_independent_past a s t hst)
  simpa only [difference_mean] using he

theorem process_condExp (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[process a t | history a s] =ᵐ[probability] process a s := by
  have he := condExp_sub (process_integrable a t) (process_integrable a s) (history a s)
  have hp := condExp_of_stronglyMeasurable (μ := probability) ((history a).le s)
    (process_adapted a s) (process_integrable a s)
  rw [hp] at he
  have hd := difference_condExp a s t hst
  filter_upwards [he,hd] with ω he hd
  change probability[process a t-process a s | history a s] ω =
    probability[process a t | history a s] ω-process a s ω at he
  change probability[process a t-process a s | history a s] ω = 0 at hd
  exact sub_eq_zero.mp (he.symm.trans hd)

theorem process_martingale (a : ℝ) : Martingale (process a) (history a) probability :=
  ⟨process_adapted a,fun s t hst => process_condExp a s t hst⟩

end OperatorDerivativeRewrite.Foundation.MarkedRenewalMartingale
