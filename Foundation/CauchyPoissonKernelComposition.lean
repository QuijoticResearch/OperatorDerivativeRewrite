import Foundation.CauchyPoissonFlow
/-! Actual Poisson transition-density composition and invariant density for the
Cauchy disk flow. Complex-pole and circle-supported transition probability laws
are constructed. Measurable-kernel composition and Feller/closed-generator
claims remain separate obligations. Time zero is explicitly Dirac. -/
noncomputable section
open Complex Metric
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonKernelComposition
open CauchyPoissonFlow

theorem herglotz_flow_holomorphic (q l : ℝ) (hq : |q| < 1)
    (hl : 0 ≤ l) (hl1 : l < 1) (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    DiffContOnCl ℂ (fun w => herglotzRieszKernel 0 (flow q l w) ξ) (ball 0 1) := by
  apply DifferentiableOn.diffContOnCl
  intro w hw
  have hw1 : ‖w‖ ≤ 1 := by simpa using (closure_ball_subset_closedBall hw)
  have hd := denominator_ne_zero q l hq hl hl1.le w hw1
  have hf : DifferentiableAt ℂ (flow q l) w :=
    (show DifferentiableAt ℂ (numerator q l) w by unfold numerator; fun_prop).div
      (show DifferentiableAt ℂ (denominator q l) w by unfold denominator; fun_prop) hd
  have hn : ξ-flow q l w ≠ 0 := by
    intro he
    have heq := congrArg norm (sub_eq_zero.mp he)
    rw [hξ] at heq
    exact (ne_of_lt (flow_strict_disk q l hq hl hl1 w hw1)) heq.symm
  simp only [herglotzRieszKernel,sub_zero]
  apply DifferentiableAt.differentiableWithinAt
  exact (hf.const_add ξ).div (hf.const_sub ξ) hn

theorem poisson_density_average (q l : ℝ) (hq : |q| < 1)
    (hl : 0 ≤ l) (hl1 : l < 1) (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (v : ℂ) (hv : ‖v‖ < 1) :
    Real.circleAverage (fun w : ℂ => poissonKernel 0 v w *
      poissonKernel 0 (flow q l w) ξ) 0 1 = poissonKernel 0 (flow q l v) ξ := by
  have hf := herglotz_flow_holomorphic q l hq hl hl1 ξ hξ
  have hvb : v ∈ ball (0:ℂ) 1 := by simpa using hv
  have hva : v ∉ sphere (0:ℂ) |(1:ℝ)| := by simpa using (ne_of_lt hv)
  have hp : ContinuousOn (poissonKernel 0 v) (sphere (0:ℂ) |(1:ℝ)|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact continuous_re.continuousOn.comp (continuousOn_herglotzRieszKernel_sphere hva)
      (Set.mapsTo_univ _ _)
  have hi : CircleIntegrable (fun w : ℂ => poissonKernel 0 v w •
      herglotzRieszKernel 0 (flow q l w) ξ) 0 1 :=
    (hp.fun_smul (hf.continuousOn_ball.mono (by simp only [abs_one]; exact sphere_subset_closedBall))).circleIntegrable'
  have h := congrArg Complex.re (hf.circleAverage_poissonKernel_smul hvb)
  have hc := Complex.reCLM.circleAverage_comp_comm hi
  have ht := hc.trans h
  simpa only [poissonKernel_eq_re_herglotzRieszKernel,Function.comp_def,
    Complex.reCLM_apply,Pi.smul_apply,Complex.smul_re,smul_eq_mul] using ht

theorem density_composition (q l m : ℝ) (hq : |q| < 1)
    (hl : 0 ≤ l) (hl1 : l < 1) (hm : 0 ≤ m) (hm1 : m < 1)
    (z ξ : ℂ) (hz : ‖z‖ ≤ 1) (hξ : ‖ξ‖ = 1) :
    Real.circleAverage (fun w : ℂ => poissonKernel 0 (flow q m z) w *
      poissonKernel 0 (flow q l w) ξ) 0 1 = poissonKernel 0 (flow q (l*m) z) ξ := by
  rw [poisson_density_average q l hq hl hl1 ξ hξ _ (flow_strict_disk q m hq hm hm1 z hz),
    flow_composition q l m hq hl hl1.le hm hm1.le z hz]

theorem density_invariance (q l : ℝ) (hq : |q| < 1)
    (hl : 0 ≤ l) (hl1 : l < 1) (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    Real.circleAverage (fun w : ℂ => poissonKernel 0 (q:ℂ) w *
      poissonKernel 0 (flow q l w) ξ) 0 1 = poissonKernel 0 (q:ℂ) ξ := by
  rw [poisson_density_average q l hq hl hl1 ξ hξ _ (by simpa using hq),
    flow_fixed q l hq hl hl1.le]

theorem poisson_positive (v ξ : ℂ) (hv : ‖v‖ < 1) (hξ : ‖ξ‖ = 1) :
    0 < poissonKernel 0 v ξ := by
  have hd : ξ-v ≠ 0 := by
    intro he
    have hh := congrArg norm (sub_eq_zero.mp he)
    rw [hξ] at hh
    exact (ne_of_lt hv) hh.symm
  unfold poissonKernel
  simp only [sub_zero,hξ,one_pow]
  apply div_pos _ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hd))
  nlinarith [norm_nonneg v]

theorem poisson_mass (v : ℂ) (hv : ‖v‖ < 1) :
    Real.circleAverage (poissonKernel 0 v) 0 1 = 1 := by
  have hf : DiffContOnCl ℂ (fun _ : ℂ => (1:ℂ)) (ball 0 1) := diffContOnCl_const
  have h := congrArg Complex.re (hf.circleAverage_poissonKernel_smul (by simpa using hv))
  simp only [Real.circleAverage_def] at h ⊢
  simpa [Complex.real_smul,intervalIntegral.integral_ofReal] using h

def transitionWeight (q t : ℝ) (z ξ : ℂ) : ℝ := poissonKernel 0 (evolution q t z) ξ

theorem transition_positive (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (z ξ : ℂ) (hz : ‖z‖ ≤ 1) (hξ : ‖ξ‖ = 1) : 0 < transitionWeight q t z ξ :=
  poisson_positive _ _ (evolution_strict_disk q t hq ht z hz) hξ

theorem transition_mass (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : Real.circleAverage (transitionWeight q t z) 0 1 = 1 :=
  poisson_mass _ (evolution_strict_disk q t hq ht z hz)

theorem transition_composition (q s t : ℝ) (hq : |q| < 1) (hs : 0 < s) (ht : 0 < t)
    (z ξ : ℂ) (hz : ‖z‖ ≤ 1) (hξ : ‖ξ‖ = 1) :
    Real.circleAverage (fun w : ℂ => transitionWeight q s z w * transitionWeight q t w ξ) 0 1 =
      transitionWeight q (s+t) z ξ := by
  have hlt : decay q t < 1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (rate_pos q hq)) ht)
  change Real.circleAverage (fun w : ℂ => poissonKernel 0 (evolution q s z) w *
    poissonKernel 0 (flow q (decay q t) w) ξ) 0 1 = _
  rw [poisson_density_average q _ hq (decay_range q t hq ht.le).1 hlt ξ hξ _
    (evolution_strict_disk q s hq hs z hz)]
  change poissonKernel 0 (evolution q t (evolution q s z)) ξ = _
  rw [← evolution_add q t s hq ht.le hs.le z hz,add_comm t s]
  rfl

open MeasureTheory

def poleWeight (v : ℂ) (θ : ℝ) : ℝ := (2*Real.pi)⁻¹ * poissonKernel 0 v (circleMap 0 1 θ)
def poleLaw (v : ℂ) : Measure ℝ :=
  (volume.restrict (Set.Ioc 0 (2*Real.pi))).withDensity (fun θ => ENNReal.ofReal (poleWeight v θ))

theorem poleWeight_continuous (v : ℂ) (hv : ‖v‖ < 1) : Continuous (poleWeight v) := by
  unfold poleWeight poissonKernel
  apply Continuous.const_mul
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro θ
  apply pow_ne_zero 2
  apply norm_ne_zero_iff.mpr
  simp only [sub_zero]
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  simp only [norm_circleMap_zero,abs_one] at hh
  exact (ne_of_lt hv) hh.symm

theorem poleWeight_positive (v : ℂ) (hv : ‖v‖ < 1) (θ : ℝ) : 0 < poleWeight v θ :=
  mul_pos (by positivity) (poisson_positive v _ hv (by simp))

theorem poleWeight_integrable (v : ℂ) (hv : ‖v‖ < 1) :
    Integrable (poleWeight v) (volume.restrict (Set.Ioc 0 (2*Real.pi))) :=
  (poleWeight_continuous v hv).intervalIntegrable 0 (2*Real.pi) |>.1

theorem poleWeight_mass (v : ℂ) (hv : ‖v‖ < 1) :
    (∫ θ in Set.Ioc 0 (2*Real.pi), poleWeight v θ) = 1 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  simp only [poleWeight]
  rw [intervalIntegral.integral_const_mul]
  exact poisson_mass v hv

theorem poleLaw_probability (v : ℂ) (hv : ‖v‖ < 1) : IsProbabilityMeasure (poleLaw v) := by
  constructor
  rw [poleLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (poleWeight_integrable v hv)
      (Filter.Eventually.of_forall (fun θ => (poleWeight_positive v hv θ).le)),poleWeight_mass v hv]
  simp

theorem poleLaw_real (q : ℝ) : poleLaw (q:ℂ) = CauchyPoissonCoreInvariant.law q := rfl

def transitionLaw (q t θ : ℝ) : Measure ℝ :=
  if t=0 then Measure.dirac θ else poleLaw (evolution q t (circleMap 0 1 θ))

theorem transitionLaw_probability (q t θ : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) :
    IsProbabilityMeasure (transitionLaw q t θ) := by
  unfold transitionLaw
  split_ifs with h
  · infer_instance
  · exact poleLaw_probability _ (evolution_strict_disk q t hq (lt_of_le_of_ne ht (Ne.symm h)) _ (by simp))

theorem transitionLaw_zero (q θ : ℝ) : transitionLaw q 0 θ = Measure.dirac θ := by
  simp [transitionLaw]

def circleTransitionLaw (q t : ℝ) (z : ℂ) : Measure ℂ :=
  if t=0 then Measure.dirac z else
    Measure.map (circleMap (0:ℂ) 1) (poleLaw (evolution q t z))

theorem circleTransitionLaw_probability (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : IsProbabilityMeasure (circleTransitionLaw q t z) := by
  unfold circleTransitionLaw
  split_ifs with h
  · infer_instance
  · let := poleLaw_probability _ (evolution_strict_disk q t hq (lt_of_le_of_ne ht (Ne.symm h)) z hz)
    infer_instance

theorem circleTransitionLaw_zero (q : ℝ) (z : ℂ) : circleTransitionLaw q 0 z = Measure.dirac z := by
  simp [circleTransitionLaw]

theorem circleTransitionLaw_on_circle (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t)
    (z : ℂ) (hz : ‖z‖ = 1) : circleTransitionLaw q t z (sphere (0:ℂ) 1) = 1 := by
  unfold circleTransitionLaw
  split_ifs with h
  · apply Measure.dirac_apply_of_mem
    simpa using hz
  · let := poleLaw_probability _ (evolution_strict_disk q t hq (lt_of_le_of_ne ht (Ne.symm h)) z hz.le)
    rw [Measure.map_apply (by fun_prop) isClosed_sphere.measurableSet]
    have he : (circleMap (0:ℂ) 1) ⁻¹' sphere (0:ℂ) 1 = Set.univ := by
      ext θ
      simp
    rw [he,measure_univ]

end OperatorDerivativeRewrite.Foundation.CauchyPoissonKernelComposition
