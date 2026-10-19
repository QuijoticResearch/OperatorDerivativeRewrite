import Foundation.IBMCompactSourceAverage

/-! Actual scenery-weighted boundary time integrals, with their ordinary L2
continuum limit. The error is controlled by the same constructed occupation mass. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactWeightedBoundary
open InfiniteGaussian IBMConstructedSources IBMCompactSourceAverage IBMCompactClockMass
open IBMDilatedMollifier IBMDilatedClockMassLimit
set_option backward.isDefEq.respectTransparency false
variable {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)

def errorPath (ρ : ℝ → ℝ) (T : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), ρ |clockPath ω t.toNNReal| *
    (sourceAverage hφ ρ |clockPath ω t.toNNReal|-φ 0)

theorem error_integrand_continuous {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (ω : SampleSpace) :
    Continuous (fun t : ℝ => ρ |clockPath ω t.toNNReal| *
      (sourceAverage hφ ρ |clockPath ω t.toNNReal|-φ 0)) := by
  have ht := continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal)
  exact (hρ.continuous.comp ht).mul
    (((sourceAverage_continuous hφ hc (hρ.of_le (by norm_num))).comp ht).sub continuous_const)

theorem errorPath_stronglyMeasurable {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (T : ℝ≥0) : StronglyMeasurable (errorPath hφ ρ T) := by
  have he : Measurable (fun z : ℝ × SampleSpace => |clockPath z.2 z.1.toNNReal|) :=
    continuous_abs.measurable.comp (continuous_eval.measurable.comp
      ((clockPath_measurable.comp measurable_snd).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_fst)))
  have hm : Measurable (fun z : ℝ × SampleSpace => ρ |clockPath z.2 z.1.toNNReal| *
      (sourceAverage hφ ρ |clockPath z.2 z.1.toNNReal|-φ 0)) := (hρ.continuous.measurable.comp he).mul
    (((sourceAverage_continuous hφ hc (hρ.of_le (by norm_num))).measurable.comp he).sub measurable_const)
  change StronglyMeasurable (fun ω => ∫ t in 0..(T : ℝ), _)
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact hm.stronglyMeasurable.integral_prod_left'

theorem weighted_error_bound {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R) (r : ℝ) :
    ‖ρ |r| * (sourceAverage hφ ρ |r|-φ 0)‖ ≤ (K : ℝ)*Real.sqrt (2*R)*ρ |r| := by
  by_cases hz : ρ |r| = 0
  · simp [hz]
  have hr : ‖sourceAverage hφ ρ |r|-φ 0‖ ≤ (K : ℝ)*Real.sqrt (2*R) :=
    sourceAverage_layer_error hφ hc hρ hpos hmass hR hs |r| (hs _ hz)
  rw [norm_mul,Real.norm_of_nonneg (hpos _)]
  exact (mul_le_mul_of_nonneg_left hr (hpos _)).trans_eq (mul_comm _ _)

theorem errorPath_bound {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R) (T : ℝ≥0) (ω : SampleSpace) :
    ‖errorPath hφ ρ T ω‖ ≤ (K : ℝ)*Real.sqrt (2*R)*
      (∫ t in 0..(T : ℝ), ρ |clockPath ω t.toNNReal|) := by
  rw [errorPath,intervalIntegral.integral_of_le T.coe_nonneg,
    intervalIntegral.integral_of_le T.coe_nonneg,← integral_const_mul]
  apply norm_integral_le_of_norm_le
  · exact (continuous_const.mul (hρ.continuous.comp (continuous_abs.comp
      ((clockPath ω).continuous.comp continuous_real_toNNReal)))).integrableOn_Ioc
  · exact Eventually.of_forall fun t => weighted_error_bound hφ hc hρ hpos hmass hR hs _

theorem errorPath_memLp {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1)
    (heven : ∀ z, ρ (-z) = ρ z) (T : ℝ≥0) : MemLp (errorPath hφ ρ T) 2 gaussianProduct := by
  obtain ⟨R0,hR0⟩ := hc.isBounded.exists_norm_le
  let R := max R0 0
  have hs (z : ℝ) (hz : ρ z ≠ 0) : |z| ≤ R := by
    have hb : |z| ≤ R0 := by simpa only [Real.norm_eq_abs] using hR0 z (subset_tsupport ρ hz)
    exact hb.trans (le_max_left _ _)
  apply (Lp.memLp (clockMass hc hρ hmass T)).of_le_mul
    (errorPath_stronglyMeasurable hφ hc hρ T).aestronglyMeasurable
  filter_upwards [clockMass_reflected_ae hc hρ hmass heven T] with ω hm
  rw [hm]
  exact (errorPath_bound hφ hc hρ hpos hmass (le_max_right _ _) hs T ω).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

def errorClass {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) (heven : ∀ z, ρ (-z) = ρ z)
    (T : ℝ≥0) : GaussianL2 := (errorPath_memLp hφ hc hρ hpos hmass heven T).toLp _

theorem errorClass_norm {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) (heven : ∀ z, ρ (-z) = ρ z)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R) (T : ℝ≥0) :
    ‖errorClass hφ hc hρ hpos hmass heven T‖ ≤
      (K : ℝ)*Real.sqrt (2*R)*‖clockMass hc hρ hmass T‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(errorPath_memLp hφ hc hρ hpos hmass heven T).coeFn_toLp,
    clockMass_reflected_ae hc hρ hmass heven T] with ω he hm
  change errorClass hφ hc hρ hpos hmass heven T ω = _ at he
  rw [he,hm]
  exact (errorPath_bound hφ hc hρ hpos hmass hR hs T ω).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

def weightedPath (ρ : ℝ → ℝ) (T : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), ρ |clockPath ω t.toNNReal| * sourceAverage hφ ρ |clockPath ω t.toNNReal|

theorem weightedPath_decomposition {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (T : ℝ≥0) (ω : SampleSpace) :
    weightedPath hφ ρ T ω = φ 0*(∫ t in 0..(T : ℝ), ρ |clockPath ω t.toNNReal|)+errorPath hφ ρ T ω := by
  have ht := continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal)
  have hfirst : Continuous (fun t : ℝ => φ 0*ρ |clockPath ω t.toNNReal|) :=
    continuous_const.mul (hρ.continuous.comp ht)
  have he : (fun t : ℝ => ρ |clockPath ω t.toNNReal| * sourceAverage hφ ρ |clockPath ω t.toNNReal|) =
      (fun t => φ 0*ρ |clockPath ω t.toNNReal|)+
        (fun t => ρ |clockPath ω t.toNNReal| * (sourceAverage hφ ρ |clockPath ω t.toNNReal|-φ 0)) := by
    funext t
    simp only [Pi.add_apply]
    ring
  rw [weightedPath,he]
  change (∫ t in 0..(T : ℝ), φ 0*ρ |clockPath ω t.toNNReal| +
    ρ |clockPath ω t.toNNReal| * (sourceAverage hφ ρ |clockPath ω t.toNNReal|-φ 0)) = _
  rw [intervalIntegral.integral_add (hfirst.intervalIntegrable 0 T)
    ((error_integrand_continuous hφ hc hρ ω).intervalIntegrable 0 T),intervalIntegral.integral_const_mul]
  rfl

def weightedClass {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) (heven : ∀ z, ρ (-z) = ρ z)
    (T : ℝ≥0) : GaussianL2 := φ 0 • clockMass hc hρ hmass T+errorClass hφ hc hρ hpos hmass heven T

theorem weightedClass_ae {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) (heven : ∀ z, ρ (-z) = ρ z) (T : ℝ≥0) :
    weightedClass hφ hc hρ hpos hmass heven T =ᵐ[gaussianProduct] weightedPath hφ ρ T := by
  filter_upwards [Lp.coeFn_add (φ 0 • clockMass hc hρ hmass T) (errorClass hφ hc hρ hpos hmass heven T),
    Lp.coeFn_smul (φ 0) (clockMass hc hρ hmass T),clockMass_reflected_ae hc hρ hmass heven T,
    (errorPath_memLp hφ hc hρ hpos hmass heven T).coeFn_toLp] with ω ha hs hm he
  change errorClass hφ hc hρ hpos hmass heven T ω = _ at he
  rw [weightedClass,ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hm,he,weightedPath_decomposition hφ hc hρ]

theorem errorClass_continuum_tendsto {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) (heven : ∀ z, ρ (-z) = ρ z) (T : ℝ≥0) :
    Tendsto (fun ε : {x : ℝ // 0 < x} => errorClass hφ (dilate_compact hc ε.property.ne')
      (dilate_contDiff hρ ε.val) (dilate_nonneg hpos ε.property)
      ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0)) (𝓝 0) := by
  obtain ⟨R0,hR0⟩ := hc.isBounded.exists_norm_le
  let R := max R0 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs (z : ℝ) (hz : ρ z ≠ 0) : |z| ≤ R := by
    have hb : |z| ≤ R0 := by simpa only [Real.norm_eq_abs] using hR0 z (subset_tsupport ρ hz)
    exact hb.trans (le_max_left _ _)
  have heps : Tendsto (fun ε : {x : ℝ // 0 < x} => ε.val) (comap (fun ε => ε.val) (𝓝 0)) (𝓝 0) :=
    tendsto_comap
  have hscalar : Tendsto (fun ε : {x : ℝ // 0 < x} => (K : ℝ)*Real.sqrt (2*(ε.val*R)))
      (comap (fun ε => ε.val) (𝓝 0)) (𝓝 0) := by
    simpa only [Function.comp_def,zero_mul,mul_zero,Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp ((heps.mul_const R).const_mul 2)).const_mul (K : ℝ)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun ε => errorClass_norm hφ _ _ _ _ _
    (mul_nonneg ε.property.le hR) (fun z hz => dilate_support hs ε.property hz) T)
  simpa only [zero_mul] using hscalar.mul (clockMass_continuum_tendsto hc hρ hpos hmass T).norm

theorem weightedClass_continuum_tendsto {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) (heven : ∀ z, ρ (-z) = ρ z) (T : ℝ≥0) :
    Tendsto (fun ε : {x : ℝ // 0 < x} => weightedClass hφ (dilate_compact hc ε.property.ne')
      (dilate_contDiff hρ ε.val) (dilate_nonneg hpos ε.property)
      ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0)) (𝓝 (φ 0 • BrownianTanakaResidual.mass T)) := by
  have h := ((clockMass_continuum_tendsto hc hρ hpos hmass T).const_smul (φ 0)).add
    (errorClass_continuum_tendsto hφ hc hρ hpos hmass heven T)
  simpa only [weightedClass,add_zero] using h

end OperatorDerivativeRewrite.Foundation.IBMCompactWeightedBoundary
