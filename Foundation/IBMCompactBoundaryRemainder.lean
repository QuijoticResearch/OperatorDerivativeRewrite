import Foundation.IBMCompactSourceAverage

/-! The actual bounded variance-slope boundary remainder vanishes in
ordinary clock L2 over the entire positive-width family. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactBoundaryRemainder
open InfiniteGaussian IBMConstructedSources IBMContinuousScenery IBMCompactSourceAverage
open IBMCompactVarianceGeometry IBMDilatedVarianceGeometry IBMDilatedMollifier
set_option backward.isDefEq.respectTransparency false
variable {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)

def slopeFactor (ρ : ℝ → ℝ) (r : ℝ) : ℝ := ((deriv (wholeLineVariance ρ) r)^2-1)/4
def residual (ρ : ℝ → ℝ) (r : ℝ) : ℝ := slopeFactor ρ r*sourceAverage hφ ρ r

theorem residual_continuous {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) :
    Continuous (residual hφ ρ) :=
  (((((variance_C2 hc hρ).continuous_deriv (by norm_num)).pow 2).sub continuous_const).div_const 4).mul
    (sourceAverage_continuous hφ hc (hρ.of_le (by norm_num)))

theorem slopeFactor_bound {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) (r : ℝ) : ‖slopeFactor ρ r‖ ≤ 1/4 := by
  have h := slope_bound hc hρ hpos hmass r
  rw [Real.norm_eq_abs] at h
  have hb := abs_le.mp h
  rw [slopeFactor,Real.norm_eq_abs,abs_le]
  constructor <;> nlinarith [sq_nonneg (deriv (wholeLineVariance ρ) r)]

theorem residual_bound {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (r : ℝ) :
    ‖residual hφ ρ r‖ ≤ M/4 := by
  rw [residual,norm_mul]
  exact (mul_le_mul (slopeFactor_bound hc hρ hpos hmass r) (sourceAverage_bound hφ hM ρ r)
    (norm_nonneg _) (by norm_num)).trans_eq (by ring)

theorem residual_tendsto_nonzero {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0)) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : Continuous ρ) (hmass : (∫ z, ρ z) = 1)
    {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (r : ℝ) (hr : r ≠ 0) :
    Tendsto (fun i => residual hφ (dilate ρ (ε i)) r) l (𝓝 0) := by
  have he : (BrownianSignIntegral.signum r)^2 = 1 := by
    rcases lt_or_gt_of_ne hr with hn | hp
    · simp [BrownianSignIntegral.signum,hn,not_lt_of_gt hn]
    · simp [BrownianSignIntegral.signum,hp]
  have hf : Tendsto (fun i => slopeFactor (dilate ρ (ε i)) r) l (𝓝 0) := by
    have h := ((slope_tendsto_nonzero hε hlim hc hρ hmass r hr).pow 2).sub_const 1 |>.div_const 4
    simpa only [slopeFactor,he,sub_self,zero_div] using h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
    (by simpa only [norm_zero,zero_mul] using hf.norm.mul_const M)
  rw [residual,norm_mul]
  exact mul_le_mul_of_nonneg_left (sourceAverage_bound hφ hM _ r) (norm_nonneg _)

def pathIntegral (ρ : ℝ → ℝ) (T : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), residual hφ ρ |clockPath ω t.toNNReal|

theorem integrand_continuous {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (ω : SampleSpace) : Continuous (fun t : ℝ => residual hφ ρ |clockPath ω t.toNNReal|) :=
  (residual_continuous hφ hc hρ).comp
    (continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal))

theorem pathIntegral_stronglyMeasurable {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (T : ℝ≥0) : StronglyMeasurable (pathIntegral hφ ρ T) := by
  have he : Measurable (fun z : ℝ × SampleSpace => |clockPath z.2 z.1.toNNReal|) :=
    continuous_abs.measurable.comp (continuous_eval.measurable.comp
      ((clockPath_measurable.comp measurable_snd).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_fst)))
  have hm := (residual_continuous hφ hc hρ).measurable.comp he
  change StronglyMeasurable (fun ω => ∫ t in 0..(T : ℝ), _)
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact hm.stronglyMeasurable.integral_prod_left'

theorem pathIntegral_bound {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) {M : ℝ}
    (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) (ω : SampleSpace) : ‖pathIntegral hφ ρ T ω‖ ≤ (M/4)*T := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (T : ℝ))
    (fun t _ => residual_bound hφ hc hρ hpos hmass hM |clockPath ω t.toNNReal|)
  simpa only [sub_zero,abs_of_nonneg T.coe_nonneg,pathIntegral] using h

theorem pathIntegral_memLp {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) {M : ℝ}
    (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) : MemLp (pathIntegral hφ ρ T) 2 gaussianProduct :=
  MemLp.of_bound (pathIntegral_stronglyMeasurable hφ hc hρ T).aestronglyMeasurable ((M/4)*T)
    (Eventually.of_forall fun ω => pathIntegral_bound hφ hc hρ.continuous hpos hmass hM T ω)

def integralClass {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) {M : ℝ}
    (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) : GaussianL2 :=
  (pathIntegral_memLp hφ hc hρ hpos hmass hM T).toLp _

theorem integralClass_continuum_tendsto {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) {M : ℝ}
    (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) :
    Tendsto (fun ε : {x : ℝ // 0 < x} => integralClass hφ (dilate_compact hc ε.property.ne')
      (dilate_contDiff hρ ε.val) (dilate_nonneg hpos ε.property)
      ((dilate_integral ρ ε.property).trans hmass) hM T)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0)) (𝓝 0) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro ε hε
  have hlim := tendsto_comap_iff.mp hε
  let κ n := dilate ρ (ε n).val
  have hκc n := dilate_compact hc (ε n).property.ne'
  have hκ n := dilate_contDiff hρ (ε n).val
  have hp n := dilate_nonneg hpos (ε n).property
  have hm n := (dilate_integral ρ (ε n).property).trans hmass
  have ht : ∀ᵐ ω ∂gaussianProduct, Tendsto (fun n => pathIntegral hφ (κ n) T ω) atTop (𝓝 0) := by
    filter_upwards [BrownianZeroOccupation.zero_time_ae T] with ω hω
    have h := tendsto_integral_of_dominated_convergence (fun _ : ℝ => M/4)
      (μ := volume.restrict (Ioc 0 (T : ℝ)))
      (F := fun n t => residual hφ (κ n) |clockPath ω t.toNNReal|) (f := fun _ => (0 : ℝ))
      (fun n => (integrand_continuous hφ (hκc n) (hκ n) ω).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun t =>
        residual_bound hφ (hκc n) (hκ n).continuous (hp n) (hm n) hM _) ?_
    · simpa only [pathIntegral,intervalIntegral.integral_of_le T.coe_nonneg,integral_zero] using h
    · exact hω.mono fun t ht => residual_tendsto_nonzero hφ (fun n => (ε n).property)
        hlim hc hρ.continuous hmass hM _ (abs_ne_zero.mpr ht)
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (((M/4)*T : ℝ) • gaussianOne)
  · intro n
    filter_upwards [(pathIntegral_memLp hφ (hκc n) (hκ n) (hp n) (hm n) hM T).coeFn_toLp,
      Lp.coeFn_smul (((M/4)*T : ℝ)) gaussianOne,gaussianOne_coeFn] with ω hf hs ho
    change integralClass hφ (hκc n) (hκ n) (hp n) (hm n) hM T ω = _ at hf
    simp only [Function.comp_def,hf,hs,Pi.smul_apply,smul_eq_mul,ho,mul_one,Real.norm_eq_abs]
    exact (pathIntegral_bound hφ (hκc n) (hκ n).continuous (hp n) (hm n) hM T ω).trans (le_abs_self _)
  · filter_upwards [Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hz
    simp only [hz,Pi.zero_apply,norm_zero]
    exact norm_nonneg _
  · filter_upwards [ht,ae_all_iff.mpr (fun n =>
      (pathIntegral_memLp hφ (hκc n) (hκ n) (hp n) (hm n) hM T).coeFn_toLp),
      Lp.coeFn_zero ℝ 2 gaussianProduct] with ω ht hn hz
    change ∀ n, integralClass hφ (hκc n) (hκ n) (hp n) (hm n) hM T ω =
      pathIntegral hφ (κ n) T ω at hn
    simpa only [Function.comp_def,hn,hz,Pi.zero_apply] using ht

end OperatorDerivativeRewrite.Foundation.IBMCompactBoundaryRemainder
