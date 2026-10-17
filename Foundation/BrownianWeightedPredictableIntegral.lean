import Foundation.BrownianClockWeightedEnergy
import Foundation.GaussianPredictableCutoff

/-! A concrete closed transported predictable domain and W-weighted stochastic integral. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianWeightedPredictableIntegral
open InfiniteGaussian GaussianTimeProductL2 GaussianPredictableFull GaussianPredictableCutoff
open BrownianClockWeightedEnergy

def ambient (T : ℝ≥0) : Lp ℝ 2 (energy T) →ₗᵢ[ℝ] TimeProbabilityL2 :=
  (L2ZeroExtensionIsometry (μ := timeProbability) (PredictableRealL2.horizon_measurable T)).comp
    (transport T).toLinearIsometry

def domain (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (energy T)) :=
  fullPredictable.comap (ambient T).toLinearMap

theorem domain_isClosed (T : ℝ≥0) : IsClosed (domain T : Set (Lp ℝ 2 (energy T))) :=
  fullPredictable_isClosed.preimage (ambient T).continuous

def embedding (T : ℝ≥0) : domain T →ₗᵢ[ℝ] fullPredictable where
  toFun u := ⟨ambient T u, u.property⟩
  map_add' u v := Subtype.ext (map_add (ambient T) u.val v.val)
  map_smul' r u := Subtype.ext (map_smul (ambient T) r u.val)
  norm_map' u := (ambient T).norm_map u.val

def integral (T : ℝ≥0) : domain T →ₗᵢ[ℝ] GaussianL2 := itoIntegral.comp (embedding T)

theorem integral_norm (T : ℝ≥0) (u : domain T) : ‖integral T u‖ = ‖u‖ :=
  (integral T).norm_map u

def rawPullback (T : ℝ≥0) (U : fullPredictable) : Lp ℝ 2 (energy T) :=
  (transport T).symm
    (LpToLpRestrictCLM _ ℝ ℝ timeProbability 2 (PredictableRealL2.horizon T)
      (U : TimeProbabilityL2))

theorem ambient_pullback (T : ℝ≥0) (U : fullPredictable) :
    ambient T (rawPullback T U) = cut T U := by
  change L2ZeroExtension (PredictableRealL2.horizon_measurable T)
    (transport T ((transport T).symm _)) = cut T U
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

def pullback (T : ℝ≥0) (U : fullPredictable) : domain T :=
  ⟨rawPullback T U, by
    change ambient T (rawPullback T U) ∈ fullPredictable
    rw [ambient_pullback]
    exact cut_mem T U⟩

theorem pullback_coeFn (T : ℝ≥0) (U : fullPredictable) :
    (pullback T U : Lp ℝ 2 (energy T)) =ᵐ[energy T]
      fun z => (U : TimeProbabilityL2) z / sigma z := by
  have hr := (energy_absolutelyContinuous T).ae_eq
    (LpToLpRestrictCLM_coeFn ℝ (PredictableRealL2.horizon T) (U : TimeProbabilityL2))
  have hi := inverse_coeFn T
    (LpToLpRestrictCLM _ ℝ ℝ timeProbability 2 (PredictableRealL2.horizon T)
      (U : TimeProbabilityL2))
  exact hi.trans (hr.mono (fun z hz => congrArg (fun x : ℝ => x / sigma z) hz))

theorem embedding_pullback (T : ℝ≥0) (U : fullPredictable) :
    embedding T (pullback T U) = predictableCut T U :=
  Subtype.ext (ambient_pullback T U)

theorem integral_pullback (T : ℝ≥0) (U : fullPredictable) :
    integral T (pullback T U) = itoIntegral (predictableCut T U) := by
  change itoIntegral (embedding T (pullback T U)) = _
  rw [embedding_pullback]

theorem integral_centered (T : ℝ≥0) (u : domain T) :
    (∫ ω, integral T u ω ∂gaussianProduct) = 0 :=
  itoIntegral_centered (embedding T u)

end OperatorDerivativeRewrite.Foundation.BrownianWeightedPredictableIntegral
