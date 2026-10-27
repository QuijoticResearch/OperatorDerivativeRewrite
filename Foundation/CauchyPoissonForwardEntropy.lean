import Foundation.CauchyPoissonDensitySmooth
import Mathlib.Analysis.Calculus.ParametricIntegral
/-! Actual positive-time forward relative entropy differentiation. Compact time intervals
away from zero justify logarithmic differentiation under the invariant-law integral.
No diffusion chain rule, jump-production identity or sharp entropy rate is asserted. -/
open Complex MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped Topology ContDiff
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonForwardEntropy
open CauchyPoissonDensitySmooth CauchyPoissonForwardDensity CauchyPoissonMarkovKernel

theorem density_derivative_continuous (q : ℝ) (hq : |q| < 1)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    ContinuousOn (deriv (densityCurve q hq μ)) (Ioi 0) := by
  have hc : ContDiffOn ℝ ∞ (densityCurve q hq μ) (Ioi 0) :=
    fun t ht => (densityCurve_smooth q t hq ht μ).contDiffWithinAt
  exact hc.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)

theorem density_real_derivative (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (w : Circle) :
    HasDerivAt (fun u => (densityCurve q hq μ u w).re)
      (deriv (densityCurve q hq μ) t w).re t := by
  have hd := (ContinuousMap.evalCLM ℝ w : C(Circle,ℂ) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt t
    (densityCurve_hasDerivAt q t hq ht μ)
  simpa only [Function.comp_def,ContinuousMap.evalCLM_apply,Complex.reCLM_apply] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd

theorem forward_entropy_derivative (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    HasDerivAt (fun u => ∫ w, klFun (densityCurve q hq μ u w).re ∂invariantLaw q)
      (∫ w, Real.log (densityCurve q hq μ t w).re *
        (deriv (densityCurve q hq μ) t w).re ∂invariantLaw q) t := by
  let := invariantLaw_probability q hq
  let J := Icc (t/2) (t+1)
  have hJ : J ⊆ Ioi 0 := by intro u hu; dsimp [J] at hu; change 0 < u; linarith [hu.1]
  have hc : ContinuousOn (densityCurve q hq μ) (Ioi 0) :=
    fun u hu => (densityCurve_hasDerivAt q u hq hu μ).continuousAt.continuousWithinAt
  have hdc := density_derivative_continuous q hq μ
  have hj : Continuous (fun p : J × Circle => densityCurve q hq μ p.1 p.2) := by
    apply Continuous.eval
    · exact (hc.mono hJ).domRestrict.comp continuous_fst
    · exact continuous_snd
  have hdj : Continuous (fun p : J × Circle => deriv (densityCurve q hq μ) p.1 p.2) := by
    apply Continuous.eval
    · exact (hdc.mono hJ).domRestrict.comp continuous_fst
    · exact continuous_snd
  have hp (u : ℝ) (hu : 0 < u) (w : Circle) : 0 < (densityCurve q hq μ u w).re := by
    rw [densityCurve_apply q u hq hu μ w,Complex.ofReal_re]
    exact density_positive q u hq hu μ w
  have hbcont : Continuous (fun p : J × Circle => ‖Real.log (densityCurve q hq μ p.1 p.2).re *
      (deriv (densityCurve q hq μ) p.1 p.2).re‖) :=
    (((Complex.continuous_re.comp hj).log (fun p => ne_of_gt (hp p.1 (hJ p.1.property) p.2))).mul
      (Complex.continuous_re.comp hdj)).norm
  obtain ⟨B,hB⟩ := isCompact_univ.bddAbove_image hbcont.continuousOn
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := invariantLaw q)
    (F := fun u w => klFun (densityCurve q hq μ u w).re) (F' := fun u w => Real.log (densityCurve q hq μ u w).re * (deriv (densityCurve q hq μ) u w).re) (x₀ := t) (s := J) (bound := fun _ => B) (Icc_mem_nhds (by linarith) (by linarith)) ?_ ?_ ?_ ?_
    (integrable_const _) ?_).2
  · exact Eventually.of_forall (fun u => (continuous_klFun.comp
      (Complex.continuous_re.comp (densityCurve q hq μ u).continuous)).aestronglyMeasurable)
  · exact (continuous_klFun.comp (Complex.continuous_re.comp (densityCurve q hq μ t).continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (((Complex.continuous_re.comp (densityCurve q hq μ t).continuous).log (fun w => ne_of_gt (hp t ht w))).mul
      (Complex.continuous_re.comp (deriv (densityCurve q hq μ) t).continuous)).aestronglyMeasurable
  · exact Eventually.of_forall (fun w u hu => hB ⟨(⟨u,hu⟩,w),mem_univ _,rfl⟩)
  · apply Eventually.of_forall
    intro w u hu
    simpa only [Function.comp_def] using (hasDerivAt_klFun (ne_of_gt (hp u (hJ hu) w))).comp u
      (density_real_derivative q u hq (hJ hu) μ w)


theorem entropy_actual_kl (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal =
      ∫ w, klFun (densityCurve q hq μ t w).re ∂invariantLaw q := by
  let := invariantLaw_probability q hq
  let := kernel_markov q t hq ht.le
  have hac : (kernel q t) ∘ₘ μ ≪ invariantLaw q := by
    rw [← forward_density q t hq ht μ]
    exact withDensity_absolutelyContinuous _ _
  rw [toReal_klDiv_eq_integral_klFun hac]
  apply integral_congr_ae
  filter_upwards [density_rnDeriv q t hq ht μ] with w hw
  rw [hw,ENNReal.toReal_ofReal (density_positive q t hq ht μ w).le,
    densityCurve_apply q t hq ht μ w,Complex.ofReal_re]

theorem actual_kl_derivative (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    HasDerivAt (fun u => (klDiv ((kernel q u) ∘ₘ μ) (invariantLaw q)).toReal)
      (∫ w, Real.log (densityCurve q hq μ t w).re *
        (deriv (densityCurve q hq μ) t w).re ∂invariantLaw q) t := by
  apply (forward_entropy_derivative q t hq ht μ).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact entropy_actual_kl q u hq hu μ

theorem forward_production_nonpos (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (∫ w, Real.log (densityCurve q hq μ t w).re *
      (deriv (densityCurve q hq μ) t w).re ∂invariantLaw q) ≤ 0 := by
  apply le_of_tendsto (actual_kl_derivative q t hq ht μ).tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with u hu
  change 0 < u at hu
  have hh := CauchyPoissonEntropy.entropy_time_monotone q t (t+u) hq ht.le (by linarith) μ
  have hr := ENNReal.toReal_mono (CauchyPoissonRegularization.positive_time_entropy_finite q t hq ht μ) hh
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hu.le) (sub_nonpos.mpr hr)

end OperatorDerivativeRewrite.Foundation.CauchyPoissonForwardEntropy
