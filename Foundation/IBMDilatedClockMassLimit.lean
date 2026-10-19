import Foundation.IBMCompactClockMass

/-! Ordinary random L2 convergence of actual continuum kernel occupation mass.
No spatial local-time density is postulated. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMDilatedClockMassLimit
open InfiniteGaussian IBMContinuousScenery IBMCompactVarianceGeometry IBMDilatedVarianceGeometry
open IBMCompactClockMass IBMDilatedMollifier GaussianLipschitzIntegrands GaussianPredictableFull
open GaussianBoundedApproximation GaussianTimeProductL2 BrownianClockWeightedEnergy
open BrownianTanakaApproximation
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem clockMass_sequence_tendsto {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => clockMass (dilate_compact hc (hε n).ne') (dilate_contDiff hρ (ε n))
      ((dilate_integral ρ (hε n)).trans hmass) T) atTop (𝓝 (BrownianTanakaResidual.mass T)) := by
  let κ n := dilate ρ (ε n)
  have hκc n : HasCompactSupport (κ n) := dilate_compact hc (hε n).ne'
  have hκ n : ContDiff ℝ 2 (κ n) := dilate_contDiff hρ (ε n)
  have hp n : ∀ x, 0 ≤ κ n x := dilate_nonneg hpos (hε n)
  have hm n : (∫ x, κ n x) = 1 := (dilate_integral ρ (hε n)).trans hmass
  let lip n := variance_lipschitz (hκc n) (hκ n) (hp n) (hm n)
  have hnz : ∀ᵐ z ∂timeProbability, z ∈ PredictableRealL2.horizon T → sigma z ≠ 0 :=
    (ae_restrict_iff' (PredictableRealL2.horizon_measurable T)).mp (sigma_nonzero T)
  have hfield : Tendsto (fun n => field (hκc n) (hκ n) (hm n) T) atTop
      (𝓝 (BrownianSignIntegral.predictableField T)) := by
    apply tendsto_subtype_rng.mpr
    apply BochnerL2Dominated.tendsto_of_ae_norm_bound
    · intro n
      filter_upwards [integrand_joint (derivativeLip (hκc n) (hκ n) (hm n)) T,
        BrownianSignIntegral.field_coeFn T,hnz] with z hf hs hz
      change ‖(field (hκc n) (hκ n) (hm n) T : TimeProbabilityL2) z‖ ≤ ‖BrownianSignIntegral.field T z‖
      change (field (hκc n) (hκ n) (hm n) T : TimeProbabilityL2) z = _ at hf
      rw [hf,hs]
      by_cases ht : z ∈ PredictableRealL2.horizon T
      · rw [indicator_of_mem ht,indicator_of_mem ht]
        have he : ‖BrownianSignIntegral.signum (sigma z)‖ = 1 := by
          rcases lt_or_gt_of_ne (hz ht) with hn | hp
          · simp [BrownianSignIntegral.signum,hn,not_lt_of_gt hn]
          · simp [BrownianSignIntegral.signum,hp]
        rw [he]
        exact slope_bound (hκc n) (hκ n).continuous (hp n) (hm n) _
      · simp [ht]
    · filter_upwards [ae_all_iff.mpr (fun n => integrand_joint (derivativeLip (hκc n) (hκ n) (hm n)) T),
        BrownianSignIntegral.field_coeFn T,hnz] with z hf hs hz
      change Tendsto (fun n => (field (hκc n) (hκ n) (hm n) T : TimeProbabilityL2) z) atTop
        (𝓝 (BrownianSignIntegral.field T z))
      change ∀ n, (field (hκc n) (hκ n) (hm n) T : TimeProbabilityL2) z =
        (PredictableRealL2.horizon T).indicator (fun z => deriv (wholeLineVariance (κ n)) (sigma z)) z at hf
      simp only [hf,hs]
      by_cases ht : z ∈ PredictableRealL2.horizon T
      · simp only [indicator_of_mem ht]
        exact slope_tendsto_nonzero hε hlim hc hρ.continuous hmass (sigma z) (hz ht)
      · simp only [indicator_of_notMem ht]
        exact tendsto_const_nhds
  have hterminal : Tendsto (fun n => valueL2 (lip n) T-wholeLineVariance (κ n) 0 • gaussianOne)
      atTop (𝓝 (BrownianTanakaApproximation.absoluteValue T)) := by
    apply BochnerL2Approximation.tendsto_of_dominated _ _ (BrownianTanakaApproximation.absoluteValue T)
    · intro n
      filter_upwards [valueL2_coeFn (lip n) T,Lp.coeFn_sub (valueL2 (lip n) T)
        (wholeLineVariance (κ n) 0 • gaussianOne),Lp.coeFn_smul (wholeLineVariance (κ n) 0) gaussianOne,
        gaussianOne_coeFn,absoluteValue_coeFn T,IBMConstructedSources.clockPath_coordinate_ae T]
        with ω hv hd hs ho ha hb
      rw [hd,Pi.sub_apply,hv,hs,Pi.smul_apply,ho,ha]
      simp only [smul_eq_mul,mul_one,Real.norm_eq_abs,abs_abs]
      rw [hb]
      simpa only [sub_zero,NNReal.coe_one,one_mul,Real.norm_eq_abs] using
        (lip n).norm_sub_le (GaussianTimeProcess.process T ω) 0
    · exact ae_of_all _ fun _ => le_rfl
    · filter_upwards [ae_all_iff.mpr (fun n => valueL2_coeFn (lip n) T),
        ae_all_iff.mpr (fun n => Lp.coeFn_sub (valueL2 (lip n) T) (wholeLineVariance (κ n) 0 • gaussianOne)),
        ae_all_iff.mpr (fun n => Lp.coeFn_smul (wholeLineVariance (κ n) 0) gaussianOne),
        gaussianOne_coeFn,absoluteValue_coeFn T,IBMConstructedSources.clockPath_coordinate_ae T]
        with ω hv hd hs ho ha hb
      simp only [hd,Pi.sub_apply,hv,hs,Pi.smul_apply,ho,ha,smul_eq_mul,mul_one]
      rw [hb]
      have ht := (variance_tendsto hε hlim hc hρ.continuous hpos hmass (GaussianTimeProcess.process T ω)).sub
        (variance_tendsto hε hlim hc hρ.continuous hpos hmass 0)
      simpa only [abs_zero,sub_zero] using ht
  have hi := itoIntegral.continuous.tendsto (BrownianSignIntegral.predictableField T) |>.comp hfield
  have h := hterminal.sub hi
  simpa only [Function.comp_def,← clockMass_identity (hκc _) (hκ _) (hp _) (hm _),
    BrownianTanakaResidual.mass,BrownianSignIntegral.terminal] using h

/-- Every positive continuum width and every admissible profile, with ordinary
clock L2 topology. For even profiles clockMass_reflected_ae gives abs(Y) itself. -/
theorem clockMass_continuum_tendsto {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) :
    Tendsto (fun ε : {x : ℝ // 0 < x} => clockMass (dilate_compact hc ε.property.ne')
      (dilate_contDiff hρ ε.val) ((dilate_integral ρ ε.property).trans hmass) T)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0)) (𝓝 (BrownianTanakaResidual.mass T)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro ε hε
  exact clockMass_sequence_tendsto hc hρ hpos hmass (fun n => (ε n).property)
    (tendsto_comap_iff.mp hε) T

theorem reflected_pathIntegral_memLp {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ x, ρ x) = 1) (heven : ∀ x, ρ (-x) = ρ x) (T : ℝ≥0) :
    MemLp (fun ω => ∫ t in 0..(T : ℝ),
      ρ |IBMConstructedSources.clockPath ω t.toNNReal|) 2 gaussianProduct :=
  (Lp.memLp (clockMass hc hρ hmass T)).ae_eq (clockMass_reflected_ae hc hρ hmass heven T)

/-- The literal reflected occupation integral converges in ordinary clock L2
to the already constructed Tanaka mass, for the whole positive-width family. -/
theorem reflected_pathIntegral_continuum_tendsto {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1)
    (heven : ∀ x, ρ (-x) = ρ x) (T : ℝ≥0) :
    Tendsto (fun ε : {x : ℝ // 0 < x} =>
      (reflected_pathIntegral_memLp (dilate_compact hc ε.property.ne') (dilate_contDiff hρ ε.val)
        ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T).toLp _)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0)) (𝓝 (BrownianTanakaResidual.mass T)) := by
  have he (ε : {x : ℝ // 0 < x}) :
      (reflected_pathIntegral_memLp (dilate_compact hc ε.property.ne') (dilate_contDiff hρ ε.val)
        ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T).toLp _ =
      clockMass (dilate_compact hc ε.property.ne') (dilate_contDiff hρ ε.val)
        ((dilate_integral ρ ε.property).trans hmass) T := by
    apply Lp.ext
    exact (reflected_pathIntegral_memLp (dilate_compact hc ε.property.ne') (dilate_contDiff hρ ε.val)
      ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T).coeFn_toLp.trans
        (clockMass_reflected_ae (dilate_compact hc ε.property.ne') (dilate_contDiff hρ ε.val)
          ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T).symm
  simpa only [he] using clockMass_continuum_tendsto hc hρ hpos hmass T

end OperatorDerivativeRewrite.Foundation.IBMDilatedClockMassLimit
