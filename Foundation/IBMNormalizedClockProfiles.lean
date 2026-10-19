import Foundation.IBMUniformMollifiedIncrements
import Foundation.GaussianObservedSecondRegularization
import Foundation.GaussianReflectedSecondBoundary
import Foundation.IBMSchwartzFullReflectedIto

/-! Actual normalized Gaussian clock profiles of the full nonlinear mollified
IBM endpoints, with an increment estimate uniform in the mollifier index. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNormalizedClockProfiles
open InfiniteGaussian IBMFullSchwartzTerminal IBMSchwartzSourceDerivative IBMCorrectionStein
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local irreducible] IBMConstructedSources.clockPath

def unitDirection (T : ℝ≥0) : CoefficientSpace :=
  (Real.sqrt (T : ℝ))⁻¹ • IBMClockAverageCandidate.direction T

theorem unitDirection_norm {T : ℝ≥0} (hT : 0 < T) : ‖unitDirection T‖ = 1 := by
  have hn : ‖IBMClockAverageCandidate.direction T‖ = Real.sqrt (T : ℝ) := by
    have hs : ‖IBMClockAverageCandidate.direction T‖ ^ 2 = (T : ℝ) := by
      simpa only [Real.toNNReal_coe] using IBMClockAverageCandidate.direction_norm_sq T
    exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt hs)
  rw [unitDirection, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), hn]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hT))

theorem clock_coordinate {T : ℝ≥0} (hT : 0 < T) :
    (fun ω => IBMConstructedSources.clockPath ω T) =ᵐ[gaussianProduct]
      fun ω => Real.sqrt (T : ℝ) * firstChaosEmbedding (unitDirection T) ω := by
  have hd : Real.sqrt (T : ℝ) • unitDirection T = IBMClockAverageCandidate.direction T := by
    have hz : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (show 0 < (T : ℝ) from hT))
    simp only [unitDirection, smul_smul, mul_inv_cancel₀ hz, one_smul]
  have hw : firstChaosEmbedding (IBMClockAverageCandidate.direction T) = GaussianTimeProcess.wienerL2 T := by
    change GaussianTimeProcess.wienerL2 (T : ℝ).toNNReal = _
    rw [Real.toNNReal_coe]
  have he : GaussianTimeProcess.wienerL2 T = Real.sqrt (T : ℝ) • firstChaosEmbedding (unitDirection T) := by
    rw [← hw, ← hd, map_smul]
  filter_upwards [IBMConstructedSources.clockPath_coordinate_ae T,
    Lp.coeFn_smul (Real.sqrt (T : ℝ)) (firstChaosEmbedding (unitDirection T))] with ω hc hs
  change IBMConstructedSources.clockPath ω T = GaussianTimeProcess.wienerL2 T ω at hc
  rw [he, hs, Pi.smul_apply, smul_eq_mul] at hc
  exact hc

def profileValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) : GaussianL2 :=
  spatial g a n (Real.sqrt (T : ℝ) * |x|) - spatial g a n 0

theorem profileValue_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Continuous (profileValue g a n T) :=
  ((spatial_continuous g a n).comp (continuous_const.mul continuous_abs)).sub continuous_const

theorem profileValue_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    ‖profileValue g a n T x‖ ≤ 2 * SchwartzMap.seminorm ℝ 0 0 (jet g 0) := by
  have h1 : ‖spatial g a n (Real.sqrt (T : ℝ) * |x|)‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 0) :=
    observable_bound g a 0 _
  have h2 : ‖spatial g a n 0‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 0) := observable_bound g a 0 _
  exact (norm_sub_le _ _).trans (by linarith)

theorem profile_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (profileValue g a n T) 2 GaussianCore.γ :=
  MemLp.of_bound (profileValue_continuous g a n T).aestronglyMeasurable
    (2 * SchwartzMap.seminorm ℝ 0 0 (jet g 0)) (ae_of_all _ (profileValue_bound g a n T))

def profile (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : Lp GaussianL2 2 GaussianCore.γ :=
  (profile_memLp g a n T).toLp _

theorem profile_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    profile g a n T =ᵐ[GaussianCore.γ] profileValue g a n T := (profile_memLp g a n T).coeFn_toLp

def sampledProfile (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Lp GaussianL2 2 gaussianProduct :=
  (Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding (unitDirection T))
    (IBMClockObservationGraph.observation_measurePreserving _ (unitDirection_norm hT))) (profile g a n T)

/-- This identifies the normalized profile with the ALREADY constructed full
source-random IBM endpoint, retaining every source chaos. -/
theorem sampledProfile_eq_endpoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) :
    sampledProfile g a n T hT = IBMSchwartzFullReflectedIto.endpointClass g a n T := by
  apply Lp.ext
  have hm := IBMClockObservationGraph.observation_measurePreserving _ (unitDirection_norm hT)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp (profile_ae g a n T)
  filter_upwards [Lp.coeFn_compMeasurePreserving (profile g a n T) hm, hp,
    IBMSchwartzFullReflectedIto.endpointClass_ae g a n T, clock_coordinate hT] with ω hs hp he hc
  change sampledProfile g a n T hT ω = _ at hs
  dsimp only [Function.comp_def] at hs hp
  rw [hs, hp, he, hc, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl

def slopeBound (g : SchwartzMap ℝ ℝ) : ℝ :=
  (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 (jet g 0)) : ℝ)

def absoluteMoment : ℝ := ∫ x : ℝ, |x| ∂GaussianCore.γ

/-- The squared profile norm is O(sqrt(T)), uniformly over all mollifiers. -/
theorem profile_uniform_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    ‖profile g a n T‖ ^ 2 ≤ slopeBound g ^ 2 * Real.sqrt (T : ℝ) * absoluteMoment := by
  rw [BochnerL2Dominated.norm_sq_integral]
  have hi := GaussianReflectedSecondBoundary.absolute_memLp.integrable (by simp : (1 : ℝ≥0∞) ≤ 2)
  have hb : ∀ᵐ x ∂GaussianCore.γ, ‖profile g a n T x‖ ^ 2 ≤
      slopeBound g ^ 2 * Real.sqrt (T : ℝ) * |x| := by
    filter_upwards [profile_ae g a n T] with x hx
    rw [hx]
    have hp := IBMUniformMollifiedIncrements.spatial_increment_norm g a n (Real.sqrt (T : ℝ) * |x|) 0
    have hpos : 0 ≤ Real.sqrt (T : ℝ) * |x| := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
    simp only [sub_zero, abs_of_nonneg hpos] at hp
    calc
      _ ≤ (slopeBound g * Real.sqrt (Real.sqrt (T : ℝ) * |x|)) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) hp
      _ = _ := by rw [mul_pow, Real.sq_sqrt hpos]; ring
  have hh := integral_mono_ae ((Lp.memLp (profile g a n T)).norm.integrable_sq)
    (hi.const_mul (slopeBound g ^ 2 * Real.sqrt (T : ℝ))) hb
  rw [integral_const_mul] at hh
  exact hh

theorem endpoint_uniform_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    {T : ℝ≥0} (hT : 0 < T) :
    ‖IBMSchwartzFullReflectedIto.endpointClass g a n T‖ ^ 2 ≤
      slopeBound g ^ 2 * Real.sqrt (T : ℝ) * absoluteMoment := by
  rw [← sampledProfile_eq_endpoint g a n hT]
  change ‖(Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding (unitDirection T))
    (IBMClockObservationGraph.observation_measurePreserving _ (unitDirection_norm hT))) (profile g a n T)‖ ^ 2 ≤ _
  rw [LinearIsometry.norm_map]
  exact profile_uniform_energy g a n T

theorem endpointLimit_uniform_energy (g : SchwartzMap ℝ ℝ) (a : ℝ)
    {T : ℝ≥0} (hT : 0 < T) :
    ‖IBMSchwartzFullReflectedIto.endpointLimitClass g a T‖ ^ 2 ≤
      slopeBound g ^ 2 * Real.sqrt (T : ℝ) * absoluteMoment :=
  le_of_tendsto ((IBMSchwartzFullReflectedIto.endpointClass_tendsto g a T).norm.pow 2)
    (Eventually.of_forall fun n => endpoint_uniform_energy g a n hT)

end OperatorDerivativeRewrite.Foundation.IBMNormalizedClockProfiles
