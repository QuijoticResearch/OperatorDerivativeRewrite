import Foundation.RiemannQuarticRealSaddle
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Lindelof
/-! Nondegeneracy of actual real saddles outside a countable set of times.
The exact saddle-time map is analytic and nonconstant on the positive axis.
Its critical points are discrete and its critical values are countable.
No assertion removes the exceptional times or establishes uniform contours. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleTimes
open RiemannQuarticKernel RiemannQuarticDomain RiemannThetaComplexKernel RiemannQuarticRealSaddle

def saddleTime (u : ℝ) : ℝ := -(deriv kernel u/kernel u)/(4*u^3)

theorem kernel_analyticAt (u : ℝ) : AnalyticAt ℝ kernel u := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have h := (kernelComplex_analyticAt (u : ℂ) he).re_ofReal
  convert h using 1
  funext x
  rw [kernelComplex_real]
  simp

theorem saddleTime_analyticAt (u : ℝ) (hu : 0 < u) :
    AnalyticAt ℝ saddleTime u := by
  exact (((kernel_analyticAt u).deriv.div (kernel_analyticAt u)
    (ne_of_gt (kernel_pos u hu.le))).neg).div
    (analyticAt_const.mul (analyticAt_id.pow 3)) (by positivity)

theorem max_saddleTime (t u : ℝ) (hu : 0 < u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) : saddleTime u=t := by
  have hs := max_real_stationary t u hu hm
  rw [← (kernel_hasDerivAt u).deriv] at hs
  unfold saddleTime
  apply (div_eq_iff (by positivity : (4 : ℝ)*u^3 ≠ 0)).mpr
  nlinarith

theorem saddleTime_not_constant :
    ¬ ∃ c : ℝ, ∀ u ∈ Ioi (0 : ℝ), saddleTime u=c := by
  rintro ⟨c,hc⟩
  obtain ⟨t,ht,hgt⟩ := ((eventually_exists_real_saddle 0 le_rfl).and
    (eventually_gt_atTop c)).exists
  obtain ⟨u,hu,hm,hs⟩ := ht
  have he := max_saddleTime t u hu hm
  have hc' := hc u hu
  linarith

theorem saddleTime_deriv_not_zero :
    ¬ EqOn (deriv saddleTime) 0 (Ioi (0 : ℝ)) := by
  intro h
  apply saddleTime_not_constant
  exact isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun u hu => (saddleTime_analyticAt u hu).differentiableAt.differentiableWithinAt) h

theorem critical_points_countable :
    {u : ℝ | 0 < u ∧ deriv saddleTime u=0}.Countable := by
  have ha : AnalyticOnNhd ℝ (deriv saddleTime) (Ioi (0 : ℝ)) :=
    fun u hu => (saddleTime_analyticAt u hu).deriv
  have hn := (ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Ioi).resolve_left
    saddleTime_deriv_not_zero
  have hd : IsDiscrete ({u : ℝ | deriv saddleTime u=0} ∩ Ioi (0 : ℝ)) := by
    apply isDiscrete_of_codiscreteWithin
    change ∀ᶠ u in codiscreteWithin (Ioi (0 : ℝ)), ¬ deriv saddleTime u=0
    exact hn
  have hc := (IsLindelof.of_coe : IsLindelof ({u : ℝ | deriv saddleTime u=0} ∩ Ioi (0 : ℝ))).countable_of_isDiscrete hd
  convert hc using 1
  apply Set.ext
  intro u
  simp only [mem_setOf_eq,mem_inter_iff,mem_Ioi,and_comm]

def exceptionalTimes : Set ℝ := saddleTime '' {u : ℝ | 0 < u ∧ deriv saddleTime u=0}

theorem exceptionalTimes_countable : exceptionalTimes.Countable :=
  critical_points_countable.image saddleTime

theorem nonexceptional_max (t u : ℝ) (ht : t ∉ exceptionalTimes) (hu : 0 < u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) : deriv saddleTime u ≠ 0 := by
  intro hz
  apply ht
  exact ⟨u,⟨hu,hz⟩,max_saddleTime t u hu hm⟩

def phaseSlope (t u : ℝ) : ℝ := 4*t*u^3+deriv kernel u/kernel u

theorem phaseSlope_factor (t u : ℝ) (hu : 0 < u) :
    phaseSlope t u=4*(t-saddleTime u)*u^3 := by
  unfold phaseSlope saddleTime
  field_simp
  ring

theorem phaseSlope_hasDerivAt (t u : ℝ) (hu : 0 < u) (hs : saddleTime u=t) :
    HasDerivAt (phaseSlope t) (-4*u^3*deriv saddleTime u) u := by
  have hT := (saddleTime_analyticAt u hu).differentiableAt.hasDerivAt
  have h := (((hasDerivAt_const u t).sub hT).const_mul 4).mul ((hasDerivAt_id u).pow 3)
  have he : phaseSlope t =ᶠ[nhds u] (fun w => 4*(t-saddleTime w)*w^3) := by
    filter_upwards [Ioi_mem_nhds hu] with w hw
    exact phaseSlope_factor t w hw
  convert h.congr_of_eventuallyEq he using 1
  dsimp only [Pi.sub_apply,Pi.pow_apply,id_eq]
  simp only [hs,sub_self,mul_zero,zero_mul,zero_add]
  ring

theorem nonexceptional_max_nondegenerate (t u : ℝ) (ht : t ∉ exceptionalTimes)
    (hu : 0 < u) (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) :
    deriv (phaseSlope t) u ≠ 0 := by
  rw [(phaseSlope_hasDerivAt t u hu (max_saddleTime t u hu hm)).deriv]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 (ne_of_gt hu)))
    (nonexceptional_max t u ht hu hm)

theorem eventually_nondegenerate_saddles (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t in atTop, t ∉ exceptionalTimes → ∃ u : ℝ, R < u ∧
      IsMaxOn (weighted 0 t 0) (Ici 0) u ∧
      phaseSlope t u=0 ∧ deriv (phaseSlope t) u ≠ 0 := by
  filter_upwards [maxima_escape R hR] with t ht hn
  obtain ⟨u,hu,hm⟩ := exists_global_max t
  have hRu := ht u hu hm
  have hu0 := lt_of_le_of_lt hR hRu
  refine ⟨u,hRu,hm,?_,nonexceptional_max_nondegenerate t u hn hu0 hm⟩
  unfold phaseSlope
  rw [(kernel_hasDerivAt u).deriv]
  exact max_real_stationary t u hu0 hm
end OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleTimes
