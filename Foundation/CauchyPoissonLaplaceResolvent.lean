import Foundation.CauchyPoissonSmoothedCore
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open Complex MeasureTheory Filter Set
open scoped Topology
/-! Actual positive Laplace resolvent for the closed Circle generator.
Weighted finite orbit integrals have an exact graph identity; exponential
tails and closedness give surjectivity and the full-domain inverse formula. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonLaplaceResolvent
open CauchyPoissonFeller CauchyPoissonCoreGenerator CauchyPoissonGeneratorDomain

def weightedOrbit (q : ℝ) (hq : |q| < 1) (r : ℝ) (f : C(Circle,ℂ)) (t : ℝ) : C(Circle,ℂ) :=
  Real.exp (-r*t) • orbit q hq f t

theorem weightedOrbit_continuous (q : ℝ) (hq : |q| < 1) (r : ℝ) (f : C(Circle,ℂ)) :
    Continuous (weightedOrbit q hq r f) := by
  exact (show Continuous (fun t : ℝ => Real.exp (-r*t)) by fun_prop).smul (orbit_continuous q hq f)

def finiteLaplace (q : ℝ) (hq : |q| < 1) (r : ℝ) (f : C(Circle,ℂ)) (T : ℝ) : C(Circle,ℂ) :=
  ∫ s in (0:ℝ)..T, weightedOrbit q hq r f s

theorem shifted_weighted_integral (q : ℝ) (hq : |q| < 1) (r : ℝ) (f : C(Circle,ℂ))
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : 0 ≤ t) :
    orbit q hq (finiteLaplace q hq r f T) t =
      Real.exp (r*t) • (∫ s in t..T+t, weightedOrbit q hq r f s) := by
  change operator q (max t 0) hq _ (∫ s in (0:ℝ)..T, weightedOrbit q hq r f s) = _
  simp only [max_eq_left ht]
  rw [← (operator q t hq ht).intervalIntegral_comp_comm ((weightedOrbit_continuous q hq r f).intervalIntegrable 0 T)]
  have he := intervalIntegral.integral_comp_add_right (weightedOrbit q hq r f) (a := 0) (b := T) t
  simp only [zero_add] at he
  rw [← he,← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := (uIcc_of_le hT ▸ hs).1
  change (operator q t hq ht).restrictScalars ℝ (Real.exp (-r*s) • orbit q hq f s) =
    Real.exp (r*t) • (Real.exp (-r*(s+t)) • orbit q hq f (s+t))
  rw [map_smul,smul_smul]
  have he' : Real.exp (r*t)*Real.exp (-r*(s+t)) = Real.exp (-r*s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he']
  congr 1
  change operator q t hq ht (orbit q hq f s) = orbit q hq f (s+t)
  rw [← orbit_add q hq f t s ht hs0,add_comm]

theorem finiteLaplace_graph (q : ℝ) (hq : |q| < 1) (r : ℝ) (f : C(Circle,ℂ))
    (T : ℝ) (hT : 0 ≤ T) :
    (finiteLaplace q hq r f T,r • finiteLaplace q hq r f T+weightedOrbit q hq r f T-f) ∈
      (generator q hq).graph := by
  rw [generator_graph_iff]
  have hc := weightedOrbit_continuous q hq r f
  have hd (a : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 a) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hdT : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, weightedOrbit q hq r f s)
      (weightedOrbit q hq r f T) (T+0) := by simpa using hd T
  have hshift : HasDerivAt (fun t : ℝ => T+t) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add T
  have he : HasDerivAt (fun t : ℝ => Real.exp (r*t)) r 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul r).exp
  have h := he.smul ((hdT.scomp 0 hshift).sub (hd 0))
  have h' : HasDerivAt (fun t : ℝ => Real.exp (r*t) •
      ((∫ s in (0:ℝ)..T+t, weightedOrbit q hq r f s)-(∫ s in (0:ℝ)..t, weightedOrbit q hq r f s)))
      (r • finiteLaplace q hq r f T+weightedOrbit q hq r f T-f) 0 := by
    convert h using 1
    · rfl
    · simp only [Pi.sub_apply,Function.comp_apply,add_zero,mul_zero,Real.exp_zero,one_smul,
        intervalIntegral.integral_same,sub_zero,finiteLaplace,weightedOrbit,orbit_zero,
        neg_mul,neg_zero]
      abel
  have hl := h'.tendsto_slope_zero_right
  simp only [zero_add,add_zero,mul_zero,Real.exp_zero,one_smul,intervalIntegral.integral_same,sub_zero] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [shifted_weighted_integral q hq r f T hT t ht.le]
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 t) (hc.intervalIntegrable t (T+t))
  rw [← hi]
  congr 2
  abel


theorem weightedOrbit_norm (q : ℝ) (hq : |q| < 1) (r : ℝ) (f : C(Circle,ℂ)) (t : ℝ) :
    ‖weightedOrbit q hq r f t‖ ≤ Real.exp (-r*t)*‖f‖ := by
  rw [weightedOrbit,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (orbit_contraction q hq f t) (Real.exp_pos _).le

theorem weightedOrbit_integrable (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f : C(Circle,ℂ)) :
    IntegrableOn (weightedOrbit q hq r f) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (a := -r) (neg_neg_of_pos hr) 0).mul_const ‖f‖).mono'
    (weightedOrbit_continuous q hq r f).aestronglyMeasurable
  exact Filter.Eventually.of_forall (weightedOrbit_norm q hq r f)

def laplace (q : ℝ) (hq : |q| < 1) (r : ℝ) (f : C(Circle,ℂ)) : C(Circle,ℂ) :=
  ∫ s in Ioi (0:ℝ), weightedOrbit q hq r f s

theorem finiteLaplace_tendsto (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f : C(Circle,ℂ)) :
    Tendsto (finiteLaplace q hq r f) atTop (𝓝 (laplace q hq r f)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (weightedOrbit_integrable q hq r hr f) tendsto_id


theorem weightedOrbit_tendsto_zero (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f : C(Circle,ℂ)) :
    Tendsto (weightedOrbit q hq r f) atTop (𝓝 0) := by
  apply squeeze_zero_norm (weightedOrbit_norm q hq r f)
  have he := Real.tendsto_exp_atBot.comp
    (tendsto_const_nhds.neg_mul_atTop (neg_neg_of_pos hr) (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
  simpa using he.mul_const ‖f‖

theorem laplace_graph (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f : C(Circle,ℂ)) :
    (laplace q hq r f,r • laplace q hq r f-f) ∈ (generator q hq).graph := by
  have hc : IsClosed ((generator q hq).graph : Set (C(Circle,ℂ) × C(Circle,ℂ))) := by
    rw [generator_graph]
    exact graph_closed q hq
  have hl := finiteLaplace_tendsto q hq r hr f
  have hg := ((hl.const_smul r).add (weightedOrbit_tendsto_zero q hq r hr f)).sub_const f
  simp only [add_zero] at hg
  apply hc.mem_of_tendsto (hl.prodMk_nhds hg)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  exact finiteLaplace_graph q hq r f T hT

theorem laplace_bound (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f : C(Circle,ℂ)) :
    ‖laplace q hq r f‖ ≤ r⁻¹*‖f‖ := by
  have h := graph_resolvent_bound q hq _ _ (laplace_graph q hq r hr f) r hr
  rw [sub_sub_cancel] at h
  have hh : ‖laplace q hq r f‖ ≤ ‖f‖/r := (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using h)
  simpa only [div_eq_mul_inv,mul_comm] using hh

theorem positive_resolvent_onto (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f : C(Circle,ℂ)) :
    ∃ u g : C(Circle,ℂ), (u,g) ∈ (generator q hq).graph ∧ r • u-g=f := by
  refine ⟨laplace q hq r f,r • laplace q hq r f-f,laplace_graph q hq r hr f, ?_⟩
  abel

theorem laplace_add (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f g : C(Circle,ℂ)) :
    laplace q hq r (f+g)=laplace q hq r f+laplace q hq r g := by
  have he : weightedOrbit q hq r (f+g) = fun t => weightedOrbit q hq r f t+weightedOrbit q hq r g t := by
    funext t
    simp only [weightedOrbit,orbit,map_add,smul_add]
  rw [laplace,he,integral_add (weightedOrbit_integrable q hq r hr f) (weightedOrbit_integrable q hq r hr g)]
  rfl

theorem laplace_smul (q : ℝ) (hq : |q| < 1) (r : ℝ) (c : ℂ) (f : C(Circle,ℂ)) :
    laplace q hq r (c • f)=c • laplace q hq r f := by
  unfold laplace weightedOrbit orbit
  simp only [map_smul,smul_comm (Real.exp _) c]
  exact integral_smul c _

def resolvent (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) : C(Circle,ℂ) →L[ℂ] C(Circle,ℂ) :=
  LinearMap.mkContinuous
    { toFun := laplace q hq r
      map_add' := laplace_add q hq r hr
      map_smul' := fun c f => laplace_smul q hq r c f }
    r⁻¹ (laplace_bound q hq r hr)


theorem resolvent_graph (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f : C(Circle,ℂ)) :
    (resolvent q hq r hr f,r • resolvent q hq r hr f-f) ∈ (generator q hq).graph :=
  laplace_graph q hq r hr f

theorem resolvent_norm (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) :
    ‖resolvent q hq r hr‖ ≤ r⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hr.le)
  exact laplace_bound q hq r hr

theorem graph_left_inverse (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f g : C(Circle,ℂ))
    (h : (f,g) ∈ (generator q hq).graph) : resolvent q hq r hr (r • f-g)=f := by
  let u := resolvent q hq r hr (r • f-g)
  have hh := (generator q hq).graph.sub_mem h (resolvent_graph q hq r hr (r • f-g))
  have hb := graph_resolvent_bound q hq (f-u) (g-(r • u-(r • f-g))) hh r hr
  have he : r • (f-u)-(g-(r • u-(r • f-g)))=0 := by
    simp only [smul_sub]
    abel
  rw [he,norm_zero] at hb
  have hz : ‖f-u‖=0 := by nlinarith [norm_nonneg (f-u)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem graph_iff_resolvent (q : ℝ) (hq : |q| < 1) (r : ℝ) (hr : 0 < r) (f g : C(Circle,ℂ)) :
    (f,g) ∈ (generator q hq).graph ↔ resolvent q hq r hr (r • f-g)=f := by
  constructor
  · exact graph_left_inverse q hq r hr f g
  · intro h
    have hg := resolvent_graph q hq r hr (r • f-g)
    rw [h,sub_sub_cancel] at hg
    exact hg

end OperatorDerivativeRewrite.Foundation.CauchyPoissonLaplaceResolvent
