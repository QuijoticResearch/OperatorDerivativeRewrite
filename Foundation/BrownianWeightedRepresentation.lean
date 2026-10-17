import Foundation.BrownianWeightedSquareCoefficient

/-! Exact finite-horizon representation for the constructed Brownian-weighted integral. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianWeightedRepresentation
open InfiniteGaussian GaussianTimeProductL2 GaussianPredictableFull GaussianPredictableCutoff
open GaussianConditionalIto GaussianConditionalClarkOcone GaussianBrownianPRP
open GaussianPredictableAdjoint BrownianClockWeightedEnergy BrownianWeightedPredictableIntegral
open BrownianWeightedSquareAdjoint

theorem cut_ambient (T : ℝ≥0) (u : Lp ℝ 2 (energy T)) :
    cut T (ambient T u) = ambient T u := by
  apply Lp.ext
  have ha : ambient T u =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (transport T u) :=
    L2ZeroExtension_coeFn (PredictableRealL2.horizon_measurable T) _
  filter_upwards [cut_coeFn T (ambient T u), ha] with z hc ha
  rw [hc, ha]
  by_cases hz : z ∈ PredictableRealL2.horizon T <;> simp [hz, ha]

theorem embedding_supported (T : ℝ≥0) (u : domain T) :
    predictableCut T (embedding T u) = embedding T u :=
  Subtype.ext (cut_ambient T u.val)

theorem integral_mem_past (T : ℝ≥0) (u : domain T) : integral T u ∈ pastL2 T := by
  have h := integral_cut_mem_past T (embedding T u)
  rw [embedding_supported] at h
  exact h

theorem pullback_representation (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ pastL2 T) :
    integral T (pullback T (predictableAdjoint F)) =
      F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  rw [integral_pullback, past_representer_supported T F hF]
  exact brownian_representation F (past_mem_brownian T hF)

theorem adjoint_eq_pullback (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ pastL2 T) :
    adjoint T F = pullback T (predictableAdjoint F) := by
  have h := congrArg (adjoint T) (pullback_representation T F hF)
  rw [adjoint_integral, map_sub, map_smul, adjoint_one, smul_zero, sub_zero] at h
  exact h.symm

theorem representation (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ pastL2 T) :
    integral T (adjoint T F) = F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  rw [adjoint_eq_pullback T F hF]
  exact pullback_representation T F hF

theorem representation_unique (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ pastL2 T) :
    ∃! u : domain T,
      integral T u = F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  refine ⟨adjoint T F, representation T F hF, ?_⟩
  intro u hu
  exact (integral T).injective (hu.trans (representation T F hF).symm)

theorem range_iff (T : ℝ≥0) (F : GaussianL2) :
    F ∈ (integral T).toLinearMap.range ↔
      F ∈ pastL2 T ∧ (∫ ω, F ω ∂gaussianProduct) = 0 := by
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨integral_mem_past T u, integral_centered T u⟩
  · rintro ⟨hF,h0⟩
    refine ⟨adjoint T F, ?_⟩
    change integral T (adjoint T F) = F
    simpa only [h0, zero_smul, sub_zero] using representation T F hF

theorem norm_adjoint (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ pastL2 T) :
    ‖adjoint T F‖ = ‖F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne‖ := by
  rw [← representation T F hF, integral_norm]

end OperatorDerivativeRewrite.Foundation.BrownianWeightedRepresentation
