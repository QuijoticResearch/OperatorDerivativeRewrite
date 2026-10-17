import Foundation.RootMarkSourceRegeneration
import Foundation.ComplexRootMarkRepresentation
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Independence.Integration

/-! Genuine predictable stochastic sums on the actual infinite four-point mark source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.RootMarkStochasticIntegral
open MarkedRootRenewalProcess (MarkSample marks)
open RootRenewalWalkMarginal (initialSegment prefix_measurable prefix_preserving)
open ComplexFourthRootNoise (noise)

abbrev Coefficients := (n : ℕ) → ComplexFourthRootWalk.Sample n → ℂ

def history : Filtration ℕ (inferInstance : MeasurableSpace MarkSample) where
  seq n := MeasurableSpace.comap (initialSegment n) inferInstance
  mono' := by
    intro n m hnm
    let mPast : MeasurableSpace MarkSample := MeasurableSpace.comap (initialSegment m) inferInstance
    have hp : @Measurable MarkSample (ComplexFourthRootWalk.Sample m) mPast inferInstance
        (initialSegment m) := comap_measurable _
    have hn : @Measurable MarkSample (ComplexFourthRootWalk.Sample n) mPast inferInstance
        (initialSegment n) := by
      exact Measurable.of_eval fun i : Fin n =>
        (measurable_pi_apply (⟨i.val,lt_of_lt_of_le i.isLt hnm⟩ : Fin m)).comp hp
    exact hn.comap_le
  le' n := (prefix_measurable n).comap_le

theorem prefix_past (n : ℕ) : Measurable[history n] (initialSegment n) :=
  comap_measurable _

theorem coefficient_past (H : Coefficients) (n : ℕ) :
    StronglyMeasurable[history n] (fun η => H n (initialSegment n η)) :=
  ((measurable_of_countable (H n)).comp (prefix_past n)).stronglyMeasurable

theorem coefficient_integrable (H : Coefficients) (n : ℕ) :
    Integrable (fun η => H n (initialSegment n η)) marks := by
  have hi : Integrable (H n) (marks.map (initialSegment n)) := by
    rw [(prefix_preserving n).map_eq]
    exact Integrable.of_finite
  exact (integrable_map_measure (measurable_of_countable (H n)).aestronglyMeasurable
    (prefix_measurable n).aemeasurable).mp hi

theorem fresh_independent (n : ℕ) :
    Indep (MeasurableSpace.comap (fun η : MarkSample => η n) inferInstance) (history n) marks := by
  have hi := (RootMarkSourceRegeneration.past_tail_independent n).symm.comp
    (measurable_pi_apply 0) measurable_id
  have he : ((fun f : MarkSample => f 0) ∘ RootMarkSourceRegeneration.tail n) =
      (fun η : MarkSample => η n) := by
    funext η
    simp [RootMarkSourceRegeneration.tail]
  rw [he, Function.id_comp] at hi
  exact hi

def freshPower (a : ℝ) (r : Fin 3) (n : ℕ) (η : MarkSample) : ℂ :=
  (noise a (η n))^(r.val+1)

theorem freshPower_measurable (a : ℝ) (r : Fin 3) (n : ℕ) :
    Measurable (freshPower a r n) :=
  ((ComplexFourthRootNoise.noise_measurable a).comp (measurable_pi_apply n)).pow_const _

theorem freshPower_integrable (a : ℝ) (r : Fin 3) (n : ℕ) :
    Integrable (freshPower a r n) marks := by
  have hm : Measurable (fun k : Fin 4 => (noise a k)^(r.val+1)) := measurable_of_countable _
  have hi : Integrable (fun k : Fin 4 => (noise a k)^(r.val+1))
      (marks.map (fun η : MarkSample => η n)) := by
    rw [(MarkedRootRenewalProcess.mark_preserving n).map_eq]
    exact Integrable.of_finite
  exact (integrable_map_measure hm.aestronglyMeasurable (measurable_pi_apply n).aemeasurable).mp hi

theorem freshPower_mean (a : ℝ) (r : Fin 3) (n : ℕ) :
    (∫ η, freshPower a r n η ∂marks) = 0 := by
  have hm : Measurable (fun k : Fin 4 => (noise a k)^(r.val+1)) := measurable_of_countable _
  have he := integral_map (μ := marks) (measurable_pi_apply n).aemeasurable hm.aestronglyMeasurable
  rw [(MarkedRootRenewalProcess.mark_preserving n).map_eq] at he
  change (∫ η, (noise a (η n))^(r.val+1) ∂marks) = 0
  rw [← he]
  fin_cases r
  · simpa using ComplexFourthRootNoise.mean a
  · simpa using ComplexFourthRootNoise.second a
  · simpa using ComplexFourthRootNoise.third a

theorem freshPower_independent (a : ℝ) (r : Fin 3) (n : ℕ) :
    Indep (MeasurableSpace.comap (freshPower a r n) inferInstance) (history n) marks := by
  have hm : Measurable[MeasurableSpace.comap (fun η : MarkSample => η n) inferInstance]
      (freshPower a r n) :=
    ((ComplexFourthRootNoise.noise_measurable a).comp
      (comap_measurable (fun η : MarkSample => η n))).pow_const _
  exact indep_of_indep_of_le (fresh_independent n) hm.comap_le le_rfl

theorem freshPower_condExp (a : ℝ) (r : Fin 3) (n : ℕ) :
    marks[freshPower a r n | history n] =ᵐ[marks] fun _ => (0 : ℂ) := by
  have he := condExp_indep_eq (freshPower_measurable a r n).comap_le (history.le n)
    (comap_measurable (freshPower a r n)).stronglyMeasurable (freshPower_independent a r n)
  simpa only [freshPower_mean] using he

def increment (a : ℝ) (r : Fin 3) (H : Coefficients) (n : ℕ) (η : MarkSample) : ℂ :=
  H n (initialSegment n η)*freshPower a r n η

theorem coefficient_fresh_independent (a : ℝ) (r : Fin 3) (H : Coefficients) (n : ℕ) :
    IndepFun (fun η => H n (initialSegment n η)) (freshPower a r n) marks :=
  indep_of_indep_of_le (freshPower_independent a r n).symm
    (coefficient_past H n).measurable.comap_le le_rfl

theorem increment_integrable (a : ℝ) (r : Fin 3) (H : Coefficients) (n : ℕ) :
    Integrable (increment a r H n) marks :=
  (coefficient_fresh_independent a r H n).integrable_mul
    (coefficient_integrable H n) (freshPower_integrable a r n)

theorem increment_condExp (a : ℝ) (r : Fin 3) (H : Coefficients) (n : ℕ) :
    marks[increment a r H n | history n] =ᵐ[marks] fun _ => (0 : ℂ) := by
  have he := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    (coefficient_past H n) (increment_integrable a r H n) (freshPower_integrable a r n)
  have hz := freshPower_condExp a r n
  filter_upwards [he,hz] with η he hz
  change marks[increment a r H n | history n] η =
    H n (initialSegment n η)*marks[freshPower a r n | history n] η at he
  rw [he,hz,mul_zero]

def stochasticIntegral (a : ℝ) (r : Fin 3) (H : Coefficients) (n : ℕ) (η : MarkSample) : ℂ :=
  ∑ j ∈ Finset.range n, increment a r H j η

theorem stochasticIntegral_adapted (a : ℝ) (r : Fin 3) (H : Coefficients) :
    StronglyAdapted history (stochasticIntegral a r H) := by
  intro n
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have hH := (coefficient_past H j).mono (history.mono hjn.le)
  have hm : Measurable[history n] (fun η : MarkSample => η j) :=
    (measurable_pi_apply (⟨j,hjn⟩ : Fin n)).comp (prefix_past n)
  exact hH.measurable.mul
    (((ComplexFourthRootNoise.noise_measurable a).comp hm).pow_const (r.val+1))

theorem stochasticIntegral_integrable (a : ℝ) (r : Fin 3) (H : Coefficients) (n : ℕ) :
    Integrable (stochasticIntegral a r H n) marks :=
  integrable_finsetSum (Finset.range n) (fun j _ => increment_integrable a r H j)

theorem stochasticIntegral_successor (a : ℝ) (r : Fin 3) (H : Coefficients) (n : ℕ) :
    stochasticIntegral a r H (n+1)-stochasticIntegral a r H n = increment a r H n := by
  funext η
  simp only [stochasticIntegral, Pi.sub_apply, Finset.sum_range_succ, add_sub_cancel_left]

theorem stochasticIntegral_martingale (a : ℝ) (r : Fin 3) (H : Coefficients) :
    Martingale (stochasticIntegral a r H) history marks := by
  apply martingale_of_condExp_sub_eq_zero_nat (stochasticIntegral_adapted a r H)
    (stochasticIntegral_integrable a r H)
  intro n
  rw [stochasticIntegral_successor]
  exact increment_condExp a r H n

end OperatorDerivativeRewrite.Foundation.RootMarkStochasticIntegral
