import Foundation.MarkedRenewalRealization

/-! Actual finite-prefix and Poisson-mixture transport for finite marked-renewal realizations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteMarkedRenewalMarginals
open MarkedRenewalRealization
variable {A : Type*} [MeasurableSpace A]

abbrev Prefix (A : Type*) (n : ℕ) := Fin n → A

def finiteProbability (μ : Measure A) (n : ℕ) : Measure (Prefix A n) := Measure.pi (fun _ => μ)

instance finiteProbability_isProbability (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (finiteProbability μ n) := by unfold finiteProbability; infer_instance

def initialSegment (n : ℕ) (η : MarkSample A) : Prefix A n := fun i => η i.val

theorem prefix_measurable (n : ℕ) : Measurable (initialSegment (A := A) n) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)

theorem prefix_preserving (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (initialSegment n) (marks μ) (finiteProbability μ n) := by
  refine ⟨prefix_measurable n,?_⟩
  change (marks μ).map (fun η (i : Fin n) => η i.val) = Measure.pi (fun _ : Fin n => μ)
  have hi := (marks_independent μ).precomp (g := fun i : Fin n => i.val) Fin.val_injective
  simpa only [(mark_preserving μ _).map_eq] using
    hi.map_fun_eq_pi_map (fun i : Fin n => (measurable_pi_apply i.val).aemeasurable)

def terminal (z : A → ℂ) (n : ℕ) (ξ : Prefix A n) : ℂ := ∑ i : Fin n, z (ξ i)

theorem position_eq_terminal (z : A → ℂ) (n : ℕ) (η : MarkSample A) :
    position z n η = terminal z n (initialSegment n η) :=
  (Fin.sum_univ_eq_sum_range (fun i => z (η i)) n).symm

theorem process_norm_power_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (t : ℝ≥0) (k : ℕ) :
    Integrable (fun ω => ‖process z t ω‖^k) (probability μ) := by
  apply ((count_power_integrable μ t k).mul_const (C^k)).mono'
    (((process_measurable z hz t).norm.pow_const k).aestronglyMeasurable)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) k)]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (process z t ω))
    (position_norm_bound z C hC (ExponentialRenewalCount.count t ω.1) ω.2) k

theorem process_power_integrable (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (hz : Measurable z) (C : ℝ) (hC : ∀ x, ‖z x‖ ≤ C) (t : ℝ≥0) (k : ℕ) :
    Integrable (fun ω => process z t ω^k) (probability μ) :=
  (process_norm_power_integrable μ z hz C hC t k).mono'
    (((process_measurable z hz t).pow_const k).aestronglyMeasurable)
      (Eventually.of_forall fun ω => (norm_pow (process z t ω) k).le)

variable [Fintype A] [MeasurableSingletonClass A]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem position_integral (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (n : ℕ) (F : ℂ → E) (x : ℂ) :
    (∫ η, F (x+position z n η) ∂marks μ) =
      ∫ ξ, F (x+terminal z n ξ) ∂finiteProbability μ n := by
  have hm : StronglyMeasurable (fun ξ : Prefix A n => F (x+terminal z n ξ)) :=
    StronglyMeasurable.of_discrete
  have he := integral_map (μ := marks μ) (prefix_preserving μ n).measurable.aemeasurable hm.aestronglyMeasurable
  rw [(prefix_preserving μ n).map_eq] at he
  simpa only [position_eq_terminal] using he.symm

theorem terminal_successor (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ)
    (n : ℕ) (F : ℂ → E) (x : ℂ) :
    (∫ ξ, F (x+terminal z (n+1) ξ) ∂finiteProbability μ (n+1)) =
      ∫ k, (∫ ξ, F (x+z k+terminal z n ξ) ∂finiteProbability μ n) ∂μ := by
  calc
    _ = ∫ p : A × Prefix A n, F (x+z p.1+terminal z n p.2)
        ∂μ.prod (finiteProbability μ n) := by
      unfold finiteProbability
      rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm).integral_comp']
      congr 1
      funext p
      simp only [Function.comp_def,terminal,MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv,Fin.sum_univ_succ,Fin.insertNth_zero,Equiv.coe_fn_mk,
        Fin.cons_succ,Fin.zero_succAbove,cast_eq,Fin.cons_zero]
      congr 1
      ring
    _ = _ := integral_prod _ Integrable.of_finite

theorem process_mixture (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ) (t : ℝ≥0)
    (F : ℂ → E) (hF : Integrable (fun ω => F (process z t ω)) (probability μ)) :
    (∫ ω, F (process z t ω) ∂probability μ) =
      ∫ n, (∫ ξ, F (terminal z n ξ) ∂finiteProbability μ n) ∂poissonMeasure t := by
  rw [probability,integral_prod _ hF]
  have hp (n : ℕ) : (∫ η, F (position z n η) ∂marks μ) =
      ∫ ξ, F (terminal z n ξ) ∂finiteProbability μ n := by
    simpa only [zero_add] using position_integral μ z n F 0
  simp only [process,hp]
  have hm : StronglyMeasurable (fun n : ℕ =>
      ∫ ξ, F (terminal z n ξ) ∂finiteProbability μ n) := StronglyMeasurable.of_discrete
  have he := integral_map (μ := ExponentialHoldingSequence.probability)
    (RenewalCompensatedMartingale.count_preserving t).measurable.aemeasurable
    hm.aestronglyMeasurable
  rw [(RenewalCompensatedMartingale.count_preserving t).map_eq] at he
  exact he.symm

end OperatorDerivativeRewrite.Foundation.FiniteMarkedRenewalMarginals
