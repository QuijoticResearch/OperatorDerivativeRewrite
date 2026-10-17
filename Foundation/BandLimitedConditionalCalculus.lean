import Foundation.BandLimitedHeatLimit
import Foundation.MarkedOperatorConditional

/-! Actual conditional transitions on the genuinely integrable unbounded Fourier domain. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BandLimitedConditionalCalculus
open BandLimitedComplexExtension
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedConditionalPolynomial MarkedPastReconstruction
open MarkedOperatorConditional

def propagate (a : ℝ) (r : ℝ≥0) (φ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  φ ξ*Complex.exp ((r : ℂ)*MarkedHolomorphicExponential.symbol a ξ)

theorem propagate_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) (r : ℝ≥0) : Integrable (propagate a r φ) (band R) := by
  have hc : Continuous (fun ξ : ℝ =>
      Complex.exp ((r : ℂ)*MarkedHolomorphicExponential.symbol a ξ)) := by
    simp_rw [ComplexRootNormTransform.symbol_real]
    fun_prop
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (-(R : ℝ)) (R : ℝ))).exists_bound_of_continuousOn
    hc.continuousOn
  apply hφ.mul_bdd (c := C) hc.aestronglyMeasurable
  filter_upwards [frequency_bound R] with ξ hξ
  exact hC ξ (abs_le.mp hξ)

theorem propagate_zero (a : ℝ) (φ : ℝ → ℂ) : propagate a 0 φ = φ := by
  funext ξ
  simp [propagate]

theorem propagate_add (a : ℝ) (r q : ℝ≥0) (φ : ℝ → ℂ) :
    propagate a r (propagate a q φ) = propagate a (r+q) φ := by
  funext ξ
  simp only [propagate, NNReal.coe_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

theorem transition_integral (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) (r : ℝ≥0) (z : ℂ) :
    (∫ y, extension R φ (z+y) ∂ComplexRootPoissonLaw.law r a) =
      extension R (propagate a r φ) z := by
  simp_rw [BandLimitedHeatLimit.starting_argument]
  rw [BandLimitedProcessExpectation.compound_mean R _ (integrand_integrable R φ hφ z) r a]
  unfold extension propagate
  apply integral_congr_ae
  filter_upwards with ξ
  ring

theorem conditional_transition (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[fun ω => extension R φ (process a t ω) | history a s] =ᵐ[probability]
      fun ω => extension R (propagate a (t-s) φ) (process a s ω) := by
  let F : PastPath s × ℂ → ℂ := fun p => extension R φ (p.1 ⟨s,by simp⟩+p.2)
  have hm : Measurable F := (extension_continuous R φ hφ).measurable.comp
    (((measurable_pi_apply (⟨s,by simp⟩ : Set.Iic s)).comp measurable_fst).add measurable_snd)
  have hfun : (fun ω => F (pastPath a s ω,increment a s t ω)) =
      (fun ω => extension R φ (process a t ω)) := by
    funext ω
    dsimp only [F,pastPath,increment,process]
    congr 1
    abel
  have hi : Integrable (fun ω => F (pastPath a s ω,increment a s t ω)) probability := by
    rw [hfun]
    exact process_integrable R φ hφ t a
  have he := IndependentInnovationConditioning.conditional_integral probability
    (pastPath a s) (increment a s t) (pastPath_measurable a s)
    (increment_measurable a s t) (past_increment_independent a s t hst)
    F hm.stronglyMeasurable hi
  rw [hfun,← history_eq_past,increment_law a s t hst] at he
  filter_upwards [he] with ω he
  rw [he]
  exact transition_integral R φ hφ a (t-s) (process a s ω)

def backward (R : ℝ≥0) (φ : ℝ → ℂ) (a : ℝ) (T t : ℝ≥0)
    (ω : StateSample) : ℂ :=
  extension R (propagate a (T-t) φ) (process a (min t T) ω)

theorem backward_adapted (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) (T : ℝ≥0) : StronglyAdapted (history a) (backward R φ a T) := by
  intro t
  have hp := (process_adapted a (min t T)).mono ((history a).mono (min_le_left t T))
  exact ((extension_continuous R _ (propagate_integrable R φ hφ a (T-t))).measurable.comp
    hp.measurable).stronglyMeasurable

theorem backward_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) (T t : ℝ≥0) : Integrable (backward R φ a T t) probability :=
  process_integrable R _ (propagate_integrable R φ hφ a (T-t)) (min t T) a

theorem terminal_condExp (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) (T t : ℝ≥0) :
    probability[fun ω => extension R φ (process a T ω) | history a t] =ᵐ[probability]
      backward R φ a T t := by
  by_cases ht : t ≤ T
  · have hb : backward R φ a T t =
        (fun ω => extension R (propagate a (T-t) φ) (process a t ω)) := by
      funext ω
      simp only [backward, min_eq_left ht]
    rw [hb]
    exact conditional_transition R φ hφ a t T ht
  · have hT : T ≤ t := le_of_not_ge ht
    have hp := (process_adapted a T).mono ((history a).mono hT)
    have hm := ((extension_continuous R φ hφ).measurable.comp hp.measurable).stronglyMeasurable
    have he := condExp_of_stronglyMeasurable (μ := probability) ((history a).le t)
      hm (process_integrable R φ hφ T a)
    have hb : backward R φ a T t = (fun ω => extension R φ (process a T ω)) := by
      funext ω
      simp only [backward, min_eq_right hT, tsub_eq_zero_of_le hT, propagate_zero]
    rw [hb]
    exact EventuallyEq.of_eq he

theorem backward_martingale (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) (T : ℝ≥0) : Martingale (backward R φ a T) (history a) probability :=
  (martingale_condExp (fun ω => extension R φ (process a T ω)) (history a) probability).congr
    (backward_adapted R φ hφ a T) (fun t => terminal_condExp R φ hφ a T t)

end OperatorDerivativeRewrite.Foundation.BandLimitedConditionalCalculus
