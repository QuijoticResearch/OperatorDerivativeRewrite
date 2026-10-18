import Foundation.MarkedRenewalRealization
import Foundation.HigherEvenRootInnovation

/-! Actual continuous-time cadlag probability processes for all even-order cyclic innovations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherEvenRenewalProcess
open ExponentialNonexplosiveClock
open HigherEvenRootInnovation

abbrev Sample (m : ℕ) := MarkedRenewalRealization.Sample (ZMod (2*m))

def probability (m : ℕ) [NeZero m] : Measure (Sample m) :=
  MarkedRenewalRealization.probability (CyclicRootProbabilityNoise.probability (2*m))

instance probability_isProbability (m : ℕ) [NeZero m] : IsProbabilityMeasure (probability m) := by
  unfold probability
  infer_instance

def process (m : ℕ) [NeZero m] (a : ℝ) : ℝ → Sample m → ℂ :=
  MarkedRenewalRealization.process (innovation m a)

theorem process_joint_measurable (m : ℕ) [NeZero m] (a : ℝ) :
    Measurable (fun p : ℝ × Sample m => process m a p.1 p.2) :=
  MarkedRenewalRealization.process_joint_measurable _ (measurable_of_countable _)

theorem process_measurable (m : ℕ) [NeZero m] (a t : ℝ) : Measurable (process m a t) :=
  MarkedRenewalRealization.process_measurable _ (measurable_of_countable _) t

theorem process_cadlag (m : ℕ) [NeZero m] (a : ℝ) (ω : Sample m) :
    IsCadlag (fun t : ℝ => process m a t ω) := MarkedRenewalRealization.process_cadlag _ ω

theorem process_zero (m : ℕ) [NeZero m] (a : ℝ) (ω : Sample m) : process m a 0 ω = 0 :=
  MarkedRenewalRealization.process_zero _ ω

theorem clock_good_ae (m : ℕ) [NeZero m] : ∀ᵐ ω : Sample m ∂probability m, Good ω.1 :=
  MarkedRenewalRealization.clock_good_ae _

theorem jump_increment (m : ℕ) [NeZero m] (a : ℝ) (ω : Sample m) (h : Good ω.1) (n : ℕ) :
    process m a (clock (n+1) ω.1) ω-process m a (clock n ω.1) ω = innovation m a (ω.2 n) :=
  MarkedRenewalRealization.jump_increment _ ω h n

theorem innovation_norm (m : ℕ) [NeZero m] (a : ℝ) (k : ZMod (2*m)) :
    ‖innovation m a k‖ = |a| := by
  rw [innovation,CyclicRootProbabilityNoise.noise_norm,norm_mul,phase_norm,mul_one,
    Complex.norm_real,Real.norm_eq_abs]

theorem jump_norm (m : ℕ) [NeZero m] (a : ℝ) (ω : Sample m) (h : Good ω.1) (n : ℕ) :
    ‖process m a (clock (n+1) ω.1) ω-process m a (clock n ω.1) ω‖ = |a| := by
  rw [jump_increment m a ω h n,innovation_norm]

theorem process_integrable (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) :
    Integrable (process m a t) (probability m) :=
  MarkedRenewalRealization.process_integrable _ _ (measurable_of_countable _) |a|
    (fun k => (innovation_norm m a k).le) t

theorem process_mean_zero (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) :
    (∫ ω, process m a t ω ∂probability m) = 0 := by
  have he := MarkedRenewalRealization.process_mean (CyclicRootProbabilityNoise.probability (2*m))
    (innovation m a) (measurable_of_countable _) |a| (fun k => (innovation_norm m a k).le) t
  have hm : (∫ k, innovation m a k ∂CyclicRootProbabilityNoise.probability (2*m)) = 0 := by
    have hpos := NeZero.pos m
    simpa only [pow_one] using HigherEvenRootInnovation.lower_moment m a 1 (by decide) (by omega)
  simpa only [process,probability,hm,mul_zero] using he

theorem process_nontrivial (m : ℕ) [NeZero m] (a : ℝ) (ha : a ≠ 0) (ω : Sample m)
    (h : Good ω.1) : ¬ ∀ t : ℝ, process m a t ω = 0 := by
  intro hz
  have he := jump_norm m a ω h 0
  rw [hz _,hz _,sub_self,norm_zero] at he
  exact (abs_ne_zero.mpr ha) he.symm

theorem process_memLp_two (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) :
    MemLp (process m a t) 2 (probability m) :=
  MarkedRenewalRealization.process_memLp_two _ _ (measurable_of_countable _) |a|
    (fun k => (innovation_norm m a k).le) t

def variableL2 (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) : Lp ℂ 2 (probability m) :=
  (process_memLp_two m a t).toLp (process m a t)

theorem variableL2_ae (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) :
    variableL2 m a t =ᵐ[probability m] process m a t := (process_memLp_two m a t).coeFn_toLp

abbrev CadlagPath := {f : ℝ → ℂ // IsCadlag f}

def path (m : ℕ) [NeZero m] (a : ℝ) (ω : Sample m) : CadlagPath :=
  ⟨fun t => process m a t ω,process_cadlag m a ω⟩

theorem path_measurable (m : ℕ) [NeZero m] (a : ℝ) : Measurable (path m a) :=
  (measurable_pi_iff.mpr (fun t => process_measurable m a t)).subtype_mk

def pathLaw (m : ℕ) [NeZero m] (a : ℝ) : Measure CadlagPath :=
  (probability m).map (path m a)

instance pathLaw_isProbability (m : ℕ) [NeZero m] (a : ℝ) : IsProbabilityMeasure (pathLaw m a) := by
  unfold pathLaw
  infer_instance

def law (m : ℕ) [NeZero m] (a t : ℝ) : Measure ℂ := (probability m).map (process m a t)

instance law_isProbability (m : ℕ) [NeZero m] (a t : ℝ) : IsProbabilityMeasure (law m a t) := by
  unfold law
  infer_instance

theorem pathLaw_marginal (m : ℕ) [NeZero m] (a t : ℝ) :
    (pathLaw m a).map (fun f : CadlagPath => f.val t) = law m a t := by
  have he : Measurable (fun f : CadlagPath => f.val t) :=
    (measurable_pi_apply t).comp measurable_subtype_coe
  exact Measure.map_map he (path_measurable m a)

end OperatorDerivativeRewrite.Foundation.HigherEvenRenewalProcess
