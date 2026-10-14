import Foundation.GaussianPhysicalDisplacement
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Strongly continuous Gaussian displacement stays uniformly away from identity in operator norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianDisplacementNormDiscontinuity
open GaussianCore GaussianPhysicalDisplacement GaussianDisplacementFromPoisson GaussianDisplacementGroup
open PoissonTiltSourceGauge PoissonTiltHellingerGeometry

def intervalProbe (d : ℝ) : GaussianL2 :=
  indicatorConstLp 2 measurableSet_Ioo (measure_ne_top γ (Ioo 0 d)) (1 : ℝ)

theorem intervalProbe_coeFn (d : ℝ) : intervalProbe d =ᵐ[γ] (Ioo 0 d).indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

theorem gaussian_interval_ne_zero (d : ℝ) (hd : 0<d) : γ (Ioo 0 d)≠0 := by
  intro hz
  have ha : (volume : Measure ℝ)≪γ := gaussianReal_absolutelyContinuous' 0 (by norm_num)
  have hv := ha hz
  rw [Real.volume_Ioo,sub_zero] at hv
  exact (ENNReal.ofReal_pos.mpr hd).ne' hv

theorem intervalProbe_norm_pos (d : ℝ) (hd : 0<d) : 0<‖intervalProbe d‖ := by
  rw [intervalProbe,norm_indicatorConstLp (by norm_num) (by norm_num),norm_one,one_mul]
  exact Real.rpow_pos_of_pos (ENNReal.toReal_pos (gaussian_interval_ne_zero d hd) (measure_ne_top γ _)) _

theorem translated_probe_orthogonal (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (hd : 0<displacement rate θ) :
    inner ℝ (gaussianDisplacement rate hr θ (intervalProbe (displacement rate θ)))
      (intervalProbe (displacement rate θ))=0 := by
  let d := displacement rate θ
  rw [L2_inner_eq_integral]
  calc
    _=∫ x : ℝ, (0 : ℝ) ∂γ := by
      apply integral_congr_ae
      filter_upwards [displacement_physical_formula rate hr θ (intervalProbe d),intervalProbe_coeFn d,
        shift_ae d (intervalProbe_coeFn d)] with x hu hf hs
      rw [hu,hf,hs]
      simp only [Real.inner_apply]
      by_cases hx : x∈Ioo 0 d
      · have hg : x-2*d∉Ioo 0 d := by intro hg; dsimp [d] at *; linarith [hx.2,hg.1]
        simp [hx,hg]
      · simp [hx]
    _=0 := by simp

theorem positive_displacement_opNorm_lower (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (hd : 0<displacement rate θ) :
    Real.sqrt 2≤‖(gaussianDisplacement rate hr θ).toLinearIsometry.toContinuousLinearMap-
      ContinuousLinearMap.id ℝ GaussianL2‖ := by
  let U := gaussianDisplacement rate hr θ
  let f := intervalProbe (displacement rate θ)
  let T := U.toLinearIsometry.toContinuousLinearMap-ContinuousLinearMap.id ℝ GaussianL2
  have hf : 0<‖f‖ := intervalProbe_norm_pos _ hd
  have hi : inner ℝ (U f) f=0 := translated_probe_orthogonal rate hr θ hd
  have he : ‖U f-f‖^2=2*‖f‖^2 := by rw [norm_sub_sq_real,U.norm_map,hi]; ring
  have hb := T.le_opNorm f
  change ‖U f-f‖≤‖T‖*‖f‖ at hb
  have hs := pow_le_pow_left₀ (norm_nonneg (U f-f)) hb 2
  rw [mul_pow,he] at hs
  have hsq : 0<‖f‖^2 := sq_pos_of_ne_zero (ne_of_gt hf)
  have hm : 2≤‖T‖^2 := (mul_le_mul_iff_left₀ hsq).mp (by simpa only [mul_comm] using hs)
  have hroot := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  change Real.sqrt 2≤‖T‖
  nlinarith [Real.sqrt_nonneg 2,norm_nonneg T]

theorem positive_tilt_displacement (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ) (hθ : 0<θ) :
    0<displacement rate θ := by
  rw [displacement,← sqrtRate_eq_sqrt_tilted rate θ,sqrtRate]
  have hp : 0<Real.sqrt (rate : ℝ) := Real.sqrt_pos.mpr hr
  have he : 1<Real.exp (θ/2) := Real.one_lt_exp_iff.mpr (by linarith)
  nlinarith

theorem displacement_not_opNorm_continuousAt_zero (rate : ℝ≥0) (hr : 0<rate) :
    ¬ ContinuousAt (fun θ : ℝ => (gaussianDisplacement rate hr θ).toLinearIsometry.toContinuousLinearMap) 0 := by
  intro hc
  let q : ℕ → ℝ := fun n => 1/(n+1 : ℝ)
  have hq : Tendsto q atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hzero : (gaussianDisplacement rate hr 0).toLinearIsometry.toContinuousLinearMap=
      ContinuousLinearMap.id ℝ GaussianL2 := by
    apply ContinuousLinearMap.ext
    intro f
    change gaussianDisplacement rate hr 0 f=f
    rw [zero_displacement_identity rate hr 0 (by
      rw [displacement,← sqrtRate_eq_sqrt_tilted rate 0,sqrtRate]
      simp)]
    rfl
  have ht := hc.tendsto.comp hq
  have hn : Tendsto (fun n => ‖(gaussianDisplacement rate hr (q n)).toLinearIsometry.toContinuousLinearMap-
      ContinuousLinearMap.id ℝ GaussianL2‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,hzero,sub_self,norm_zero] using
      (ht.sub_const ((gaussianDisplacement rate hr 0).toLinearIsometry.toContinuousLinearMap)).norm
  obtain ⟨n,hn⟩ := (hn.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))).exists
  have hp : 0<q n := by dsimp [q]; positivity
  have hl := positive_displacement_opNorm_lower rate hr (q n) (positive_tilt_displacement rate hr _ hp)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  nlinarith [Real.sqrt_nonneg 2]

end OperatorDerivativeRewrite.Foundation.GaussianDisplacementNormDiscontinuity
