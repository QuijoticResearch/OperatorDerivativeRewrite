import Foundation.IBMDilatedVarianceGeometry
import Foundation.IBMBoundaryClockLimit

/-! Actual compact-kernel clock occupation mass, constructed from the real
Gaussian variance curvature and identified with its literal time integral. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactClockMass
open InfiniteGaussian IBMContinuousScenery IBMCompactVarianceGeometry IBMDilatedVarianceGeometry
open GaussianLipschitzIntegrands GaussianPredictableFull GaussianBoundedApproximation
open GaussianTimeProductL2 GaussianProductDerivative BrownianClockWeightedEnergy
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem exists_curvature_bound {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : Continuous ρ) (hmass : (∫ x, ρ x) = 1) :
    ∃ K : ℝ≥0, ∀ x, ‖deriv (deriv (wholeLineVariance ρ)) x‖₊ ≤ K := by
  obtain ⟨M,hM⟩ := hc.isCompact.exists_bound_of_continuousOn hρ.continuousOn
  refine ⟨⟨2*max M 0,by positivity⟩,fun x => ?_⟩
  change ‖deriv (deriv (wholeLineVariance ρ)) x‖ ≤ 2*max M 0
  rw [variance_second hc hρ hmass,norm_mul,Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  by_cases hx : ρ x = 0
  · simp only [hx,norm_zero]; exact le_max_right _ _
  · exact (hM x (subset_tsupport _ hx)).trans (le_max_left _ _)

def curvatureBound {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : Continuous ρ) (hmass : (∫ x, ρ x) = 1) : ℝ≥0 :=
  (exists_curvature_bound hc hρ hmass).choose

theorem curvature_bound {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : Continuous ρ) (hmass : (∫ x, ρ x) = 1) (x : ℝ) :
    ‖deriv (deriv (wholeLineVariance ρ)) x‖₊ ≤ curvatureBound hc hρ hmass :=
  (exists_curvature_bound hc hρ hmass).choose_spec x

def derivativeLip {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ x, ρ x) = 1) :
    LipschitzWith (curvatureBound hc hρ.continuous hmass) (deriv (wholeLineVariance ρ)) :=
  GaussianC2Ito.derivativeLip (wholeLineVariance ρ) (variance_C2 hc hρ)
    (curvatureBound hc hρ.continuous hmass) (curvature_bound hc hρ.continuous hmass)

def field {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) : fullPredictable :=
  integrand (derivativeLip hc hρ hmass) T

def curvatureValue {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ x, ρ x) = 1) (t : ℝ≥0) : GaussianL2 :=
  GaussianC2Ito.curvatureValue (wholeLineVariance ρ) (variance_C2 hc hρ)
    (curvatureBound hc hρ.continuous hmass) (curvature_bound hc hρ.continuous hmass) t

def clockMass {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) : GaussianL2 :=
  (1/2 : ℝ) • ∫ t in 0..(T : ℝ), curvatureValue hc hρ hmass t.toNNReal

theorem clockMass_identity {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) :
    clockMass hc hρ hmass T = valueL2 (variance_lipschitz hc hρ hpos hmass) T-
      wholeLineVariance ρ 0 • gaussianOne-itoIntegral (field hc hρ hmass T) := by
  have h := GaussianC2Ito.c2_ito (wholeLineVariance ρ) (variance_C2 hc hρ) 1
    (curvatureBound hc hρ.continuous hmass)
    (fun x => show ‖deriv (wholeLineVariance ρ) x‖ ≤ (1 : ℝ) from
      slope_bound hc hρ.continuous hpos hmass x)
    (curvature_bound hc hρ.continuous hmass) T
  rw [GaussianSmoothIto.valueL2_zero] at h
  change valueL2 (variance_lipschitz hc hρ hpos hmass) T-wholeLineVariance ρ 0 • gaussianOne =
    itoIntegral (field hc hρ hmass T)+clockMass hc hρ hmass T at h
  linear_combination (norm := module) -h

/-- Unreflected occupation mass; evenness is needed only to replace Y by abs(Y). -/
theorem clockMass_ae {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) :
    clockMass hc hρ hmass T =ᵐ[gaussianProduct] fun ω =>
      ∫ t in 0..(T : ℝ), ρ (IBMConstructedSources.clockPath ω t.toNNReal) := by
  have hcont := (GaussianC2TimeWeighted.curvature_continuous (wholeLineVariance ρ) (variance_C2 hc hρ)
    (curvatureBound hc hρ.continuous hmass) (curvature_bound hc hρ.continuous hmass)).comp
      continuous_real_toNNReal
  change Continuous (fun t : ℝ => curvatureValue hc hρ hmass t.toNNReal) at hcont
  have hm : Measurable (fun z : ℝ × SampleSpace => 2*ρ (IBMConstructedSources.clockPath z.2 z.1.toNNReal)) := by
    exact measurable_const.mul (hρ.continuous.measurable.comp
      (continuous_eval.measurable.comp ((IBMConstructedSources.clockPath_measurable.comp measurable_snd).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_fst))))
  have hv (t : ℝ) : curvatureValue hc hρ hmass t.toNNReal =ᵐ[gaussianProduct]
      fun ω => 2*ρ (IBMConstructedSources.clockPath ω t.toNNReal) := by
    filter_upwards [GaussianC2Ito.curvatureValue_coeFn (wholeLineVariance ρ) (variance_C2 hc hρ)
      (curvatureBound hc hρ.continuous hmass) (curvature_bound hc hρ.continuous hmass) t.toNNReal,
      IBMConstructedSources.clockPath_coordinate_ae t.toNNReal] with ω hv hb
    change curvatureValue hc hρ hmass t.toNNReal ω = _ at hv
    rw [hv,variance_second hc hρ.continuous hmass,hb]
  have h := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := gaussianProduct)
    (fun t : ℝ => curvatureValue hc hρ hmass t.toNNReal) ((hcont.intervalIntegrable 0 T).1)
    (fun z : ℝ × SampleSpace => 2*ρ (IBMConstructedSources.clockPath z.2 z.1.toNNReal))
    hm.stronglyMeasurable.aestronglyMeasurable (Eventually.of_forall hv)
  change ((1/2 : ℝ) • ∫ t in 0..(T : ℝ), curvatureValue hc hρ hmass t.toNNReal) =ᵐ[gaussianProduct] _
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  filter_upwards [h,Lp.coeFn_smul (1/2 : ℝ)
    (∫ t in Ioc 0 (T : ℝ), curvatureValue hc hρ hmass t.toNNReal)] with ω hf hs
  rw [hs,Pi.smul_apply,smul_eq_mul,hf,integral_const_mul]
  ring

theorem clockMass_reflected_ae {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ x, ρ x) = 1) (heven : ∀ x, ρ (-x) = ρ x) (T : ℝ≥0) :
    clockMass hc hρ hmass T =ᵐ[gaussianProduct] fun ω =>
      ∫ t in 0..(T : ℝ), ρ |IBMConstructedSources.clockPath ω t.toNNReal| := by
  have he (x : ℝ) : ρ |x| = ρ x := by
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg hx,heven]
  simpa only [he] using clockMass_ae hc hρ hmass T

end OperatorDerivativeRewrite.Foundation.IBMCompactClockMass
