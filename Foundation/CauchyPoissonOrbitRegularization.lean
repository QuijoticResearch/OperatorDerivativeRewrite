import Foundation.CauchyPoissonDomainDensity
open Complex MeasureTheory Filter Set
open scoped Topology
open OperatorDerivativeRewrite.Foundation
open CauchyPoissonFeller CauchyPoissonCoreGenerator CauchyPoissonGeneratorDomain
/-! Actual orbit-integral regularization for the closed Circle generator.
Normalized averages converge in the graph topology on its full domain.
This does not assert finite Fourier graph-core equality or resolvent surjectivity. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonOrbitRegularization

theorem shifted_integral (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) (T : ℝ) (hT : 0 ≤ T)
    (t : ℝ) (ht : 0 ≤ t) :
    orbit q hq (integralOperator q hq T f) t = ∫ s in t..T+t, orbit q hq f s := by
  change operator q (max t 0) hq _ (∫ s in (0:ℝ)..T, orbit q hq f s) = _
  simp only [max_eq_left ht]
  rw [← (operator q t hq ht).intervalIntegral_comp_comm ((orbit_continuous q hq f).intervalIntegrable 0 T)]
  have he := intervalIntegral.integral_comp_add_right (orbit q hq f) (a := 0) (b := T) t
  simp only [zero_add] at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := (uIcc_of_le hT ▸ hs).1
  change operator q t hq ht (orbit q hq f s) = orbit q hq f (s+t)
  rw [← orbit_add q hq f t s ht hs0,add_comm]


theorem integrated_graph (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) (T : ℝ) (hT : 0 ≤ T) :
    (integralOperator q hq T f,orbit q hq f T-f) ∈ (generator q hq).graph := by
  rw [generator_graph_iff]
  have hc := orbit_continuous q hq f
  have hd (a : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 a) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hdT : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, orbit q hq f s) (orbit q hq f T) (T+0) := by simpa using hd T
  have hshift : HasDerivAt (fun t : ℝ => T+t) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add T
  have hT' := hdT.scomp 0 hshift
  have h := hT'.sub (hd 0)
  simp only [add_zero,one_smul,orbit_zero] at h
  have hl := h.tendsto_slope_zero_right
  simp only [Pi.sub_apply,Function.comp_apply,zero_add,add_zero,intervalIntegral.integral_same,sub_zero] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change t⁻¹ • ((∫ s in (0:ℝ)..T+t, orbit q hq f s)-
    (∫ s in (0:ℝ)..t, orbit q hq f s)-(∫ s in (0:ℝ)..T, orbit q hq f s)) =
    t⁻¹ • (orbit q hq (integralOperator q hq T f) t-integralOperator q hq T f)
  rw [shifted_integral q hq f T hT t ht.le]
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t (T+t))
  rw [← hi]
  congr 1
  change _ = _ - (∫ s in (0:ℝ)..T, orbit q hq f s)
  abel


theorem average_graph (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) (T : ℝ) (hT : 0 ≤ T) :
    (T⁻¹ • integralOperator q hq T f,T⁻¹ • (orbit q hq f T-f)) ∈ (generator q hq).graph := by
  exact ((generator q hq).graph.restrictScalars ℝ).smul_mem T⁻¹ (integrated_graph q hq f T hT)

theorem average_tendsto (q : ℝ) (hq : |q| < 1) (f : C(Circle,ℂ)) :
    Tendsto (fun T : ℝ => T⁻¹ • integralOperator q hq T f) (𝓝[Ioi 0] 0) (𝓝 f) := by
  have hc := orbit_continuous q hq f
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h := hd.tendsto_slope_zero_right
  change Tendsto (fun T : ℝ => T⁻¹ • (∫ s in (0:ℝ)..T, orbit q hq f s)) _ _
  simpa only [zero_add,intervalIntegral.integral_same,sub_zero,orbit_zero] using h

theorem graph_average_tendsto (q : ℝ) (hq : |q| < 1) (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) :
    Tendsto (fun T : ℝ => (T⁻¹ • integralOperator q hq T f,T⁻¹ • (orbit q hq f T-f)))
      (𝓝[Ioi 0] 0) (𝓝 (f,g)) := by
  exact (average_tendsto q hq f).prodMk_nhds ((generator_graph_iff q hq f g).mp h)

end OperatorDerivativeRewrite.Foundation.CauchyPoissonOrbitRegularization
