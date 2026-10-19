import Foundation.IBMCompactWeightedBoundary
import Foundation.IBMCompactBoundaryRemainder

/-! Literal original Gaussian curvature residual and its full continuum
ordinary clock-L2 boundary-layer limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactOriginalBoundary
open InfiniteGaussian IBMContinuousScenery IBMCorrectionStein IBMCompactKernelSchwartz
open IBMCompactSourceAverage IBMDilatedVarianceGeometry IBMDilatedMollifier IBMConstructedSources
set_option backward.isDefEq.respectTransparency false

def originalResidual (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  correction g a (coefficient ρ r) (coefficient (deriv ρ) r) (coefficient (deriv (deriv ρ)) r)-
    (1/4 : ℝ)*(∫ ω, shiftedJet g a 4 (wholeLineScenery ρ r ω) ∂gaussianProduct)

theorem originalResidual_literal (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ) (r : ℝ) :
    originalResidual g a ρ r =
      (∫ ω, shiftedJet g a 2 (wholeLineScenery ρ r ω)*(wholeLineScenery (deriv ρ) r ω)^2+
        shiftedJet g a 1 (wholeLineScenery ρ r ω)*wholeLineScenery (deriv (deriv ρ)) r ω
        ∂gaussianProduct)-(1/4 : ℝ)*∫ ω, shiftedJet g a 4 (wholeLineScenery ρ r ω) ∂gaussianProduct := by
  simp only [originalResidual,correction,coefficient_embedding]

/-- The original curvature expectation is identified by the generic verified
Gaussian Stein identity and the actual global covariance bracket. -/
theorem originalResidual_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ x, ρ x) = 1) (r : ℝ) :
    originalResidual g a ρ r = ρ r*sourceAverage (shiftedJet_lipschitz g a 2) ρ r+
      IBMCompactBoundaryRemainder.residual (shiftedJet_lipschitz g a 4) ρ r := by
  have hb : ‖coefficient (deriv ρ) r‖^2+
      inner ℝ (coefficient ρ r) (coefficient (deriv (deriv ρ)) r) = ρ r := by
    simpa only [← coefficient_embedding,LinearIsometry.norm_map,LinearIsometry.inner_map_map] using
      covariance_bracket hc hρ hmass r
  have hd := wholeLineVariance_deriv ρ hc (hρ.of_le (by norm_num)) r
  simp only [← coefficient_embedding,LinearIsometry.inner_map_map] at hd
  rw [originalResidual,correction_identity,hb]
  simp only [coefficient_embedding]
  rw [← sourceAverage_eq_integral (shiftedJet_lipschitz g a 2),
    ← sourceAverage_eq_integral (shiftedJet_lipschitz g a 4)]
  rw [IBMCompactBoundaryRemainder.residual,IBMCompactBoundaryRemainder.slopeFactor,hd]
  ring

def originalPathIntegral (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ)
    (T : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), originalResidual g a ρ |clockPath ω t.toNNReal|

theorem originalPathIntegral_decomposition (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ x, ρ x) = 1)
    (T : ℝ≥0) (ω : SampleSpace) :
    originalPathIntegral g a ρ T ω =
      IBMCompactWeightedBoundary.weightedPath (shiftedJet_lipschitz g a 2) ρ T ω+
        IBMCompactBoundaryRemainder.pathIntegral (shiftedJet_lipschitz g a 4) ρ T ω := by
  unfold originalPathIntegral
  simp_rw [originalResidual_identity g a hc hρ hmass]
  have ht := continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal)
  apply intervalIntegral.integral_add
  · exact ((hρ.continuous.comp ht).mul
      ((sourceAverage_continuous (shiftedJet_lipschitz g a 2) hc
        (hρ.of_le (by norm_num))).comp ht)).intervalIntegrable 0 T
  · exact (IBMCompactBoundaryRemainder.integrand_continuous (shiftedJet_lipschitz g a 4)
      hc hρ ω).intervalIntegrable 0 T

def originalClass (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmass : (∫ x, ρ x) = 1) (heven : ∀ x, ρ (-x) = ρ x) (T : ℝ≥0) : GaussianL2 :=
  IBMCompactWeightedBoundary.weightedClass (shiftedJet_lipschitz g a 2) hc hρ hpos hmass heven T+
    IBMCompactBoundaryRemainder.integralClass (shiftedJet_lipschitz g a 4) hc hρ hpos hmass
      (shiftedJet_bound g a 4) T

theorem originalClass_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmass : (∫ x, ρ x) = 1) (heven : ∀ x, ρ (-x) = ρ x) (T : ℝ≥0) :
    originalClass g a hc hρ hpos hmass heven T =ᵐ[gaussianProduct] originalPathIntegral g a ρ T := by
  filter_upwards [Lp.coeFn_add
    (IBMCompactWeightedBoundary.weightedClass (shiftedJet_lipschitz g a 2) hc hρ hpos hmass heven T)
    (IBMCompactBoundaryRemainder.integralClass (shiftedJet_lipschitz g a 4) hc hρ hpos hmass (shiftedJet_bound g a 4) T),
    IBMCompactWeightedBoundary.weightedClass_ae (shiftedJet_lipschitz g a 2) hc hρ hpos hmass heven T,
    (IBMCompactBoundaryRemainder.pathIntegral_memLp (shiftedJet_lipschitz g a 4) hc hρ hpos hmass
      (shiftedJet_bound g a 4) T).coeFn_toLp] with ω ha hw hr
  change IBMCompactBoundaryRemainder.integralClass (shiftedJet_lipschitz g a 4) hc hρ hpos hmass
    (shiftedJet_bound g a 4) T ω = _ at hr
  rw [originalClass,ha,Pi.add_apply,hw,hr,originalPathIntegral_decomposition g a hc hρ hmass]

theorem originalPathIntegral_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmass : (∫ x, ρ x) = 1) (heven : ∀ x, ρ (-x) = ρ x) (T : ℝ≥0) :
    MemLp (originalPathIntegral g a ρ T) 2 gaussianProduct :=
  (Lp.memLp (originalClass g a hc hρ hpos hmass heven T)).ae_eq
    (originalClass_ae g a hc hρ hpos hmass heven T)

theorem originalClass_continuum_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmass : (∫ x, ρ x) = 1) (heven : ∀ x, ρ (-x) = ρ x) (T : ℝ≥0) :
    Tendsto (fun ε : {x : ℝ // 0 < x} => originalClass g a (dilate_compact hc ε.property.ne')
      (dilate_contDiff hρ ε.val) (dilate_nonneg hpos ε.property)
      ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0))
      (𝓝 (jet g 2 a • BrownianTanakaResidual.mass T)) := by
  have h := (IBMCompactWeightedBoundary.weightedClass_continuum_tendsto
    (shiftedJet_lipschitz g a 2) hc hρ hpos hmass heven T).add
      (IBMCompactBoundaryRemainder.integralClass_continuum_tendsto
        (shiftedJet_lipschitz g a 4) hc hρ hpos hmass (shiftedJet_bound g a 4) T)
  simpa only [originalClass,add_zero,shiftedJet,add_zero] using h

/-- F2's literal original boundary-layer random functional, in ordinary
clock L2, for EVERY admissible profile and the whole positive-width filter. -/
theorem originalPathIntegral_continuum_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmass : (∫ x, ρ x) = 1) (heven : ∀ x, ρ (-x) = ρ x) (T : ℝ≥0) :
    Tendsto (fun ε : {x : ℝ // 0 < x} =>
      (originalPathIntegral_memLp g a (dilate_compact hc ε.property.ne')
        (dilate_contDiff hρ ε.val) (dilate_nonneg hpos ε.property)
        ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T).toLp _)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0))
      (𝓝 (jet g 2 a • BrownianTanakaResidual.mass T)) := by
  have he (ε : {x : ℝ // 0 < x}) :
      (originalPathIntegral_memLp g a (dilate_compact hc ε.property.ne')
        (dilate_contDiff hρ ε.val) (dilate_nonneg hpos ε.property)
        ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T).toLp _ =
      originalClass g a (dilate_compact hc ε.property.ne') (dilate_contDiff hρ ε.val)
        (dilate_nonneg hpos ε.property) ((dilate_integral ρ ε.property).trans hmass)
        (dilate_even heven ε.val) T := by
    apply Lp.ext
    exact (originalPathIntegral_memLp g a (dilate_compact hc ε.property.ne')
      (dilate_contDiff hρ ε.val) (dilate_nonneg hpos ε.property)
      ((dilate_integral ρ ε.property).trans hmass) (dilate_even heven ε.val) T).coeFn_toLp.trans
        (originalClass_ae g a _ _ _ _ _ T).symm
  simpa only [he] using originalClass_continuum_tendsto g a hc hρ hpos hmass heven T

end OperatorDerivativeRewrite.Foundation.IBMCompactOriginalBoundary
