import Foundation.CauchyPoissonDualObstruction
/-! Time-averaged actual law functionals admit bounded transposed generator
values and strongly continuous forward orbits. No strong time derivative,
measure-valued average construction or density-domain identification is asserted. -/
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonDualAverage
open CauchyPoissonForwardDual CauchyPoissonGeneratorDomain CauchyPoissonCoreGenerator
open CauchyPoissonFeller CauchyPoissonOrbitRegularization

def averageDual (q : ℝ) (hq : |q| < 1) (T : ℝ)
    (φ : C(Circle,ℂ) →L[ℂ] ℂ) : C(Circle,ℂ) →L[ℂ] ℂ :=
  T⁻¹ • φ.comp (integralOperator q hq T)

theorem averageDual_apply (q : ℝ) (hq : |q| < 1) (T : ℝ)
    (φ : C(Circle,ℂ) →L[ℂ] ℂ) (f : C(Circle,ℂ)) :
    averageDual q hq T φ f = T⁻¹ • ∫ s in (0:ℝ)..T, φ (orbit q hq f s) := by
  change T⁻¹ • φ (∫ s in (0:ℝ)..T, orbit q hq f s) = _
  rw [φ.intervalIntegral_comp_comm ((orbit_continuous q hq f).intervalIntegrable 0 T)]

theorem average_adjoint_pairing (q : ℝ) (hq : |q| < 1) (T : ℝ) (hT : 0 ≤ T)
    (φ : C(Circle,ℂ) →L[ℂ] ℂ) (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) :
    averageDual q hq T φ g = (T⁻¹ • (dualOrbit q hq φ T - φ)) f := by
  have hh := tangent_integrated q hq f g ((generator_graph_iff q hq f g).mp h) T hT
  change T⁻¹ • φ (∫ s in (0:ℝ)..T, orbit q hq g s) = T⁻¹ • (φ (orbit q hq f T)-φ f)
  rw [← hh,map_sub]

theorem average_actual_law (q : ℝ) (hq : |q| < 1) (T : ℝ) (hT : 0 ≤ T)
    (μ : Measure Circle) [IsProbabilityMeasure μ] (f : C(Circle,ℂ)) :
    averageDual q hq T (lawFunctional μ) f =
      T⁻¹ • ∫ s in (0:ℝ)..T, ∫ z, f z ∂(CauchyPoissonMarkovKernel.kernel q s) ∘ₘ μ := by
  rw [averageDual_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hT] at hs
  exact (actual_law_duality q s hq hs.1 μ f).symm

theorem average_weak_limit (q : ℝ) (hq : |q| < 1)
    (φ : C(Circle,ℂ) →L[ℂ] ℂ) (f : C(Circle,ℂ)) :
    Tendsto (fun T => averageDual q hq T φ f) (𝓝[Ioi 0] 0) (𝓝 (φ f)) := by
  have h := φ.continuous.tendsto f |>.comp (average_tendsto q hq f)
  have he : (fun T => averageDual q hq T φ f) =
      fun T => φ (T⁻¹ • integralOperator q hq T f) := by
    funext T
    change T⁻¹ • φ (integralOperator q hq T f) = φ (T⁻¹ • integralOperator q hq T f)
    exact ((φ.restrictScalars ℝ).map_smul T⁻¹ _).symm
  rw [he]
  exact h

theorem integral_commutes (q : ℝ) (hq : |q| < 1) (T t : ℝ) (hT : 0 ≤ T) (ht : 0 ≤ t)
    (f : C(Circle,ℂ)) :
    integralOperator q hq T (orbit q hq f t) = orbit q hq (integralOperator q hq T f) t := by
  change (∫ s in (0:ℝ)..T, orbit q hq (orbit q hq f t) s) =
    operator q (max t 0) hq _ (∫ s in (0:ℝ)..T, orbit q hq f s)
  rw [← (operator q (max t 0) hq _).intervalIntegral_comp_comm
    ((orbit_continuous q hq f).intervalIntegrable 0 T)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 := (uIcc_of_le hT ▸ hs).1
  change operator q (max s 0) hq _ (orbit q hq f t) = operator q (max t 0) hq _ (orbit q hq f s)
  simp only [max_eq_left hs0,max_eq_left ht]
  rw [← orbit_add q hq f s t hs0 ht,← orbit_add q hq f t s ht hs0,add_comm s t]

theorem integrated_shift_bound (q : ℝ) (hq : |q| < 1) (T t : ℝ) (hT : 0 ≤ T) (ht : 0 ≤ t)
    (f : C(Circle,ℂ)) :
    ‖integralOperator q hq T (orbit q hq f t)-integralOperator q hq T f‖ ≤ 2*t*‖f‖ := by
  rw [integral_commutes q hq T t hT ht,shifted_integral q hq f T hT t ht]
  change ‖(∫ s in t..T+t, orbit q hq f s)-(∫ s in (0:ℝ)..T, orbit q hq f s)‖ ≤ _
  have hc := orbit_continuous q hq f
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t (T+t))
  have hb := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 T) (hc.intervalIntegrable T (T+t))
  have he : (∫ s in t..T+t, orbit q hq f s)-(∫ s in (0:ℝ)..T, orbit q hq f s) =
      (∫ s in T..T+t, orbit q hq f s)-(∫ s in (0:ℝ)..t, orbit q hq f s) := by
    rw [← hb] at ha
    linear_combination ha
  rw [he]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := T) (b := T+t) (fun s _ => orbit_contraction q hq f s)
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (fun s _ => orbit_contraction q hq f s)
  simp only [add_sub_cancel_left,sub_zero,abs_of_nonneg ht] at h1 h2
  exact (norm_sub_le _ _).trans (by nlinarith)


theorem average_strong_bound (q : ℝ) (hq : |q| < 1) (T : ℝ) (hT : 0 < T)
    (φ : C(Circle,ℂ) →L[ℂ] ℂ) (t : ℝ) (ht : 0 ≤ t) :
    ‖dualOrbit q hq (averageDual q hq T φ) t - averageDual q hq T φ‖ ≤
      2*t*T⁻¹*‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖T⁻¹ • φ (integralOperator q hq T (orbit q hq f t)) -
    T⁻¹ • φ (integralOperator q hq T f)‖ ≤ _
  rw [← smul_sub,← map_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hT)]
  calc
    _ ≤ T⁻¹ * (‖φ‖ * (2*t*‖f‖)) := mul_le_mul_of_nonneg_left
      ((φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (integrated_shift_bound q hq T t hT.le ht f) (norm_nonneg _))) (inv_nonneg.mpr hT.le)
    _ = _ := by ring

theorem average_strong_right (q : ℝ) (hq : |q| < 1) (T : ℝ) (hT : 0 < T)
    (φ : C(Circle,ℂ) →L[ℂ] ℂ) :
    Tendsto (fun t => dualOrbit q hq (averageDual q hq T φ) t)
      (𝓝[Ioi 0] 0) (𝓝 (averageDual q hq T φ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : ∀ᶠ t in 𝓝[Ioi (0:ℝ)] 0,
      ‖dualOrbit q hq (averageDual q hq T φ) t - averageDual q hq T φ‖ ≤
        2*t*T⁻¹*‖φ‖ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact average_strong_bound q hq T hT φ t ht.le
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hb
  have hc : Continuous (fun t : ℝ => 2*t*T⁻¹*‖φ‖) := by fun_prop
  simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

end OperatorDerivativeRewrite.Foundation.CauchyPoissonDualAverage
