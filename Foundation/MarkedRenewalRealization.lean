import Foundation.MarkedRootRenewalProcess
import Foundation.RenewalCompensatedMartingale
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual marked-renewal realizations reusable across probability innovation sources. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedRenewalRealization
open ExponentialNonexplosiveClock ExponentialRenewalCount ExponentialRenewalCadlag
variable {A : Type*} [MeasurableSpace A]

abbrev MarkSample (A : Type*) := ℕ → A
abbrev Sample (A : Type*) := ExponentialHoldingSequence.Sample × MarkSample A

def marks (μ : Measure A) : Measure (MarkSample A) := Measure.infinitePi (fun _ : ℕ => μ)

instance marks_probability (μ : Measure A) [IsProbabilityMeasure μ] : IsProbabilityMeasure (marks μ) := by
  unfold marks
  infer_instance

def probability (μ : Measure A) : Measure (Sample A) :=
  ExponentialHoldingSequence.probability.prod (marks μ)

instance probability_isProbability (μ : Measure A) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (probability μ) := by
  unfold probability
  infer_instance

theorem mark_preserving (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun η : MarkSample A => η n) (marks μ) μ :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => μ) n

theorem marks_independent (μ : Measure A) [IsProbabilityMeasure μ] :
    iIndepFun (fun n (η : MarkSample A) => η n) (marks μ) :=
  iIndepFun_infinitePi (X := fun _ : ℕ => (id : A → A)) (by fun_prop)

theorem sources_independent (μ : Measure A) [IsProbabilityMeasure μ] :
    IndepFun (Prod.fst : Sample A → ExponentialHoldingSequence.Sample)
      (Prod.snd : Sample A → MarkSample A) (probability μ) :=
  indepFun_prod measurable_id measurable_id

theorem clock_good_ae (μ : Measure A) [IsProbabilityMeasure μ] :
    ∀ᵐ ω : Sample A ∂probability μ, Good ω.1 := by
  have hp : MeasurePreserving (Prod.fst : Sample A → ExponentialHoldingSequence.Sample)
      (probability μ) ExponentialHoldingSequence.probability := measurePreserving_fst
  exact hp.quasiMeasurePreserving.ae good_ae

def position (z : A → ℂ) (n : ℕ) (η : MarkSample A) : ℂ := ∑ i ∈ Finset.range n, z (η i)

theorem position_measurable (z : A → ℂ) (hz : Measurable z) (n : ℕ) : Measurable (position z n) :=
  Finset.measurable_sum _ (fun i _ => hz.comp (measurable_pi_apply i))

theorem position_joint_measurable (z : A → ℂ) (hz : Measurable z) :
    Measurable (fun p : ℕ × MarkSample A => position z p.1 p.2) :=
  measurable_from_prod_countable_right (fun n => position_measurable z hz n)

def process (z : A → ℂ) (t : ℝ) (ω : Sample A) : ℂ := position z (count t ω.1) ω.2

theorem process_joint_measurable (z : A → ℂ) (hz : Measurable z) :
    Measurable (fun p : ℝ × Sample A => process z p.1 p.2) := by
  have hproj : Measurable (fun p : ℝ × Sample A => (p.1,p.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hc : Measurable (fun p : ℝ × Sample A => count p.1 p.2.1) := by
    simpa only [Function.comp_def] using count_joint_measurable.comp hproj
  have hm : Measurable (fun p : ℝ × Sample A => p.2.2) := measurable_snd.comp measurable_snd
  simpa only [Function.comp_def,process] using (position_joint_measurable z hz).comp (hc.prodMk hm)

theorem process_measurable (z : A → ℂ) (hz : Measurable z) (t : ℝ) : Measurable (process z t) := by
  simpa only [Function.comp_def] using (process_joint_measurable z hz).comp
    (show Measurable (fun ω : Sample A => (t,ω)) from measurable_const.prodMk measurable_id)

theorem process_cadlag (z : A → ℂ) (ω : Sample A) : IsCadlag (fun t : ℝ => process z t ω) := by
  have he := (count_cadlag ω.1).continuous_comp
    (show Continuous (fun n : ℕ => position z n ω.2) from continuous_of_discreteTopology)
  simpa only [Function.comp_def,process] using he

theorem process_zero (z : A → ℂ) (ω : Sample A) : process z 0 ω = 0 := by
  simp [process,count_zero,position]

theorem process_at_clock (z : A → ℂ) (ω : Sample A) (h : Good ω.1) (n : ℕ) :
    process z (clock n ω.1) ω = position z n ω.2 := by rw [process,count_at_clock h]

theorem jump_increment (z : A → ℂ) (ω : Sample A) (h : Good ω.1) (n : ℕ) :
    process z (clock (n+1) ω.1) ω-process z (clock n ω.1) ω = z (ω.2 n) := by
  rw [process_at_clock z ω h (n+1),process_at_clock z ω h n]
  simp only [position,Finset.sum_range_succ]
  abel

theorem position_norm_bound (z : A → ℂ) (C : ℝ) (hz : ∀ x, ‖z x‖ ≤ C)
    (n : ℕ) (η : MarkSample A) : ‖position z n η‖ ≤ (n : ℝ)*C := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖z (η i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range n, C := Finset.sum_le_sum (fun i _ => hz (η i))
    _ = _ := by simp

theorem count_integrable (μ : Measure A) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    Integrable (fun ω : Sample A => (count t ω.1 : ℝ)) (probability μ) :=
  (show MeasurePreserving (Prod.fst : Sample A → ExponentialHoldingSequence.Sample)
    (probability μ) ExponentialHoldingSequence.probability from measurePreserving_fst).integrable_comp_of_integrable
      (RenewalCompensatedMartingale.process_integrable t)

theorem process_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (t : ℝ≥0) :
    Integrable (process z t) (probability μ) :=
  ((count_integrable μ t).mul_const C).mono' (process_measurable z hz t).aestronglyMeasurable
    (Eventually.of_forall fun ω => position_norm_bound z C hC (count t ω.1) ω.2)

theorem count_power_integrable (μ : Measure A) [IsProbabilityMeasure μ] (t : ℝ≥0) (k : ℕ) :
    Integrable (fun ω : Sample A => (count t ω.1 : ℝ)^k) (probability μ) := by
  have hi := (RenewalCompensatedMartingale.count_preserving t).integrable_comp_of_integrable
    (PoissonCountMoments.count_power_integrable t k)
  exact (show MeasurePreserving (Prod.fst : Sample A → ExponentialHoldingSequence.Sample)
    (probability μ) ExponentialHoldingSequence.probability from measurePreserving_fst).integrable_comp_of_integrable hi

theorem process_square_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (t : ℝ≥0) :
    Integrable (fun ω => ‖process z t ω‖^2) (probability μ) := by
  apply ((count_power_integrable μ t 2).mul_const (C^2)).mono'
    (((process_measurable z hz t).norm.pow_const 2).aestronglyMeasurable)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (process z t ω))
    (position_norm_bound z C hC (count t ω.1) ω.2) 2

theorem process_memLp_two (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (t : ℝ≥0) :
    MemLp (process z t) 2 (probability μ) :=
  (memLp_two_iff_integrable_sq_norm (process_measurable z hz t).aestronglyMeasurable).mpr
    (process_square_integrable μ z hz C hC t)

theorem position_mean (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Integrable z μ) (n : ℕ) :
    (∫ η, position z n η ∂marks μ) = (n : ℂ)*(∫ x, z x ∂μ) := by
  have hi (i : ℕ) : (∫ η, z (η i) ∂marks μ) = ∫ x, z x ∂μ := by
    have hm : AEStronglyMeasurable z ((marks μ).map (fun η : MarkSample A => η i)) := by
      rw [(mark_preserving μ i).map_eq]
      exact hz.aestronglyMeasurable
    have he := integral_map (mark_preserving μ i).measurable.aemeasurable hm
    rw [(mark_preserving μ i).map_eq] at he
    exact he.symm
  have hI (i : ℕ) : Integrable (fun η : MarkSample A => z (η i)) (marks μ) :=
    (mark_preserving μ i).integrable_comp_of_integrable hz
  unfold position
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp only [hi,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

theorem process_mean (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (t : ℝ≥0) :
    (∫ ω, process z t ω ∂probability μ) = (t : ℂ)*(∫ x, z x ∂μ) := by
  have hi : Integrable z μ := Integrable.of_bound hz.aestronglyMeasurable C (Eventually.of_forall hC)
  rw [probability,integral_prod _ (process_integrable μ z hz C hC t)]
  simp only [process,position_mean μ z hi]
  rw [integral_mul_const]
  have hc : (∫ ω : ExponentialHoldingSequence.Sample, (count t ω : ℂ)
      ∂ExponentialHoldingSequence.probability) = (t : ℂ) := by
    simp_rw [← Complex.ofReal_natCast]
    rw [integral_complex_ofReal]
    exact congrArg Complex.ofReal (RenewalCompensatedMartingale.process_mean t)
  rw [hc]

theorem fourth_probability_eq : probability ComplexFourthRootNoise.probability =
    MarkedRootRenewalProcess.probability := rfl

theorem fourth_process_eq (a : ℝ) : process (ComplexFourthRootNoise.noise a) =
    MarkedRootRenewalProcess.process a := rfl

end OperatorDerivativeRewrite.Foundation.MarkedRenewalRealization
