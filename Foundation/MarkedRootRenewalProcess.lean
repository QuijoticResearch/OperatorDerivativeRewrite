import Foundation.ExponentialRenewalCadlag
import Foundation.ComplexFourthRootNoise

/-! A genuine jointly measurable cadlag complex jump process with exponential arrival clocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedRootRenewalProcess
open ExponentialNonexplosiveClock ExponentialRenewalCount ExponentialRenewalCadlag

abbrev MarkSample := ℕ → Fin 4
abbrev StateSample := ExponentialHoldingSequence.Sample × MarkSample

def marks : Measure MarkSample :=
  Measure.infinitePi (fun _ : ℕ => ComplexFourthRootNoise.probability)

instance marks_probability : IsProbabilityMeasure marks := by
  unfold marks
  infer_instance

def probability : Measure StateSample := ExponentialHoldingSequence.probability.prod marks

instance probability_isProbability : IsProbabilityMeasure probability := by
  unfold probability
  infer_instance

theorem mark_preserving (n : ℕ) :
    MeasurePreserving (fun η : MarkSample => η n) marks ComplexFourthRootNoise.probability :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => ComplexFourthRootNoise.probability) n

theorem marks_independent : iIndepFun (fun n (η : MarkSample) => η n) marks :=
  iIndepFun_infinitePi (X := fun _ : ℕ => (id : Fin 4 → Fin 4)) (by fun_prop)

theorem sources_independent : IndepFun (Prod.fst : StateSample → ExponentialHoldingSequence.Sample)
    (Prod.snd : StateSample → MarkSample) probability :=
  indepFun_prod measurable_id measurable_id

theorem clock_good_ae : ∀ᵐ ω : StateSample ∂probability, Good ω.1 := by
  have hp : MeasurePreserving (Prod.fst : StateSample → ExponentialHoldingSequence.Sample)
      probability ExponentialHoldingSequence.probability := measurePreserving_fst
  exact hp.quasiMeasurePreserving.ae good_ae

def position (a : ℝ) (n : ℕ) (η : MarkSample) : ℂ :=
  ∑ i ∈ Finset.range n, ComplexFourthRootNoise.noise a (η i)

theorem position_measurable (a : ℝ) (n : ℕ) : Measurable (position a n) :=
  Finset.measurable_sum _ (fun i _ =>
    (ComplexFourthRootNoise.noise_measurable a).comp (measurable_pi_apply i))

theorem position_joint_measurable (a : ℝ) :
    Measurable (fun p : ℕ × MarkSample => position a p.1 p.2) :=
  measurable_from_prod_countable_right (fun n => position_measurable a n)

def process (a : ℝ) (t : ℝ) (ω : StateSample) : ℂ := position a (count t ω.1) ω.2

theorem process_joint_measurable (a : ℝ) :
    Measurable (fun p : ℝ × StateSample => process a p.1 p.2) := by
  have hproj : Measurable (fun p : ℝ × StateSample => (p.1,p.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hc0 := count_joint_measurable.comp hproj
  have hc : Measurable (fun p : ℝ × StateSample => count p.1 p.2.1) := by
    simpa only [Function.comp_def] using hc0
  have hm : Measurable (fun p : ℝ × StateSample => p.2.2) := measurable_snd.comp measurable_snd
  have he := (position_joint_measurable a).comp (hc.prodMk hm)
  simpa only [Function.comp_def, process] using he

theorem process_measurable (a t : ℝ) : Measurable (process a t) := by
  have he := (process_joint_measurable a).comp
    (show Measurable (fun ω : StateSample => (t,ω)) from measurable_const.prodMk measurable_id)
  simpa only [Function.comp_def] using he

theorem process_cadlag (a : ℝ) (ω : StateSample) : IsCadlag (fun t : ℝ => process a t ω) := by
  have he := (count_cadlag ω.1).continuous_comp
    (show Continuous (fun n : ℕ => position a n ω.2) from continuous_of_discreteTopology)
  simpa only [Function.comp_def, process] using he

theorem process_zero (a : ℝ) (ω : StateSample) : process a 0 ω = 0 := by
  simp [process, count_zero, position]

theorem process_at_clock (a : ℝ) (ω : StateSample) (h : Good ω.1) (n : ℕ) :
    process a (clock n ω.1) ω = position a n ω.2 := by rw [process, count_at_clock h]

theorem jump_increment (a : ℝ) (ω : StateSample) (h : Good ω.1) (n : ℕ) :
    process a (clock (n+1) ω.1) ω - process a (clock n ω.1) ω =
      ComplexFourthRootNoise.noise a (ω.2 n) := by
  rw [process_at_clock a ω h (n+1), process_at_clock a ω h n]
  simp only [position, Finset.sum_range_succ]
  abel

theorem first_jump_nonzero (a : ℝ) (ha : a ≠ 0) (ω : StateSample) (h : Good ω.1) :
    process a (clock 1 ω.1) ω ≠ 0 := by
  have he : process a (clock 1 ω.1) ω = ComplexFourthRootNoise.noise a (ω.2 0) := by
    rw [process_at_clock a ω h 1]
    simp [position]
  rw [he]
  intro hz
  have hs := ComplexFourthRootNoise.norm_square a (ω.2 0)
  rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  have hp : 0 < a^2 := sq_pos_of_ne_zero ha
  nlinarith

end OperatorDerivativeRewrite.Foundation.MarkedRootRenewalProcess
