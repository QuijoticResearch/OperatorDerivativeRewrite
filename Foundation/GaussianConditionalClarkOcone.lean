import Foundation.GaussianConditionalIto

/-! Full raw conditional representation, with the actual future-time cutoff. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianConditionalClarkOcone
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianPredictableCutoff GaussianPredictableAdjoint
open GaussianConditionalIto GaussianBrownianGeneratedSpace GaussianBrownianPRP

theorem natural_le_brownian (T : ℝ≥0) : naturalFiltration T ≤ brownianSigma := by
  rw [naturalFiltration, Filtration.natural_eq_comap process process_stronglyMeasurable T]
  apply Measurable.comap_le
  letI : MeasurableSpace SampleSpace := brownianSigma
  exact Measurable.of_eval fun t : Iic T => process_brownian_measurable t

theorem past_mem_brownian (T : ℝ≥0) {F : GaussianL2} (hF : F ∈ pastL2 T) : F ∈ brownianL2 :=
  hF.mono (natural_le_brownian T)

theorem pastProjection_one (T : ℝ≥0) : pastProjection T gaussianOne = gaussianOne := by
  apply Submodule.starProjection_eq_self_iff.mpr
  exact stronglyMeasurable_const.aestronglyMeasurable.congr gaussianOne_coeFn.symm

theorem past_representation (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ brownianL2) :
    itoIntegral (predictableCut T (predictableAdjoint F)) =
      pastProjection T F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  rw [← pastProjection_integral, brownian_representation F hF, map_sub, map_smul,
    pastProjection_one]

/-- Conditional projection of the terminal functional becomes a genuine time truncation
of its unique predictable representer, not a substitution of a running derivative. -/
theorem predictableAdjoint_pastProjection (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ brownianL2) :
    predictableAdjoint (pastProjection T F) = predictableCut T (predictableAdjoint F) := by
  have h := congrArg predictableAdjoint (past_representation T F hF)
  rw [predictableAdjoint_integral, map_sub,
    GaussianQuadraticCylinders.predictableAdjoint_constant, sub_zero] at h
  exact h.symm

theorem conditional_representation (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ brownianL2) :
    F - pastProjection T F =
      itoIntegral (predictableAdjoint F - predictableCut T (predictableAdjoint F)) := by
  rw [map_sub, brownian_representation F hF, past_representation T F hF]
  module

/-- The same identity on the existing closed derivative domain, with no derivative
assumption on a separately supplied candidate. -/
theorem conditional_clark_ocone (T : ℝ≥0) (F : closedCylindricalDerivative.domain)
    (hF : (F : GaussianL2) ∈ brownianL2) :
    (F : GaussianL2) - pastProjection T F =
      itoIntegral (predictableProjection (closedCylindricalDerivative F) -
        predictableCut T (predictableProjection (closedCylindricalDerivative F))) := by
  rw [← predictableAdjoint_eq_projected_derivative]
  exact conditional_representation T F hF

theorem past_representer_supported (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ pastL2 T) :
    predictableCut T (predictableAdjoint F) = predictableAdjoint F := by
  have h := predictableAdjoint_pastProjection T F (past_mem_brownian T hF)
  have he : pastProjection T F = F := Submodule.starProjection_eq_self_iff.mpr hF
  rw [he] at h
  exact h.symm

theorem future_representer_coeFn (T : ℝ≥0) (U : fullPredictable) :
    (U - predictableCut T U : fullPredictable) =ᵐ[timeProbability]
      (Ioi (T : ℝ) ×ˢ (univ : Set SampleSpace)).indicator (U : TimeProbabilityL2) := by
  have hs := (mem_fullPredictable_iff _).mp U.property |>.2
  filter_upwards [Lp.coeFn_sub (U : TimeProbabilityL2) (cut T U), cut_coeFn T U, hs]
    with z hd hc hs
  change ((U : TimeProbabilityL2) - cut T U) z = _
  rw [hd]
  change (U : TimeProbabilityL2) z - cut T U z = _
  rw [hc]
  by_cases hz : z.1 ≤ T
  · by_cases h0 : 0 < z.1
    · have ht : z ∈ PredictableRealL2.horizon T := ⟨⟨h0, hz⟩, mem_univ _⟩
      simp [ht, hz, not_lt.mpr hz]
    · have hnot : z ∉ positiveTimes := fun hh => h0 hh.1
      have ht : z ∉ PredictableRealL2.horizon T := fun hh => h0 hh.1.1
      simp [hs hnot, ht, not_lt.mpr hz]
  · have ht : z ∉ PredictableRealL2.horizon T := fun hh => hz hh.1.2
    simp [ht, lt_of_not_ge hz]

theorem conditional_representer_unique (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ brownianL2) :
    ∃! U : fullPredictable, itoIntegral U = F - pastProjection T F := by
  refine ⟨predictableAdjoint F - predictableCut T (predictableAdjoint F),
    (conditional_representation T F hF).symm, ?_⟩
  intro U hU
  exact itoIntegral.injective (hU.trans (conditional_representation T F hF))

theorem conditional_variance_identity (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ brownianL2) :
    ‖F - pastProjection T F‖ ^ 2 =
      ‖predictableAdjoint F - predictableCut T (predictableAdjoint F)‖ ^ 2 := by
  rw [conditional_representation T F hF, itoIntegral.norm_map]

theorem finite_horizon_representation (T : ℝ≥0) (F : GaussianL2) (hF : F ∈ pastL2 T) :
    ∃! U : fullPredictable,
      itoIntegral U = F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne ∧ predictableCut T U = U := by
  refine ⟨predictableAdjoint F,
    ⟨brownian_representation F (past_mem_brownian T hF), past_representer_supported T F hF⟩, ?_⟩
  intro U hU
  exact itoIntegral.injective (hU.1.trans (brownian_representation F (past_mem_brownian T hF)).symm)

/-- The actual conditional projections converge to every raw Brownian-generated L2 class. -/
theorem pastProjection_tendsto (F : GaussianL2) (hF : F ∈ brownianL2) :
    Tendsto (fun n : ℕ => pastProjection (n : ℝ≥0) F) atTop (𝓝 F) := by
  have ht := GaussianContinuousRigidity.integralExtension.continuous.tendsto
    (predictableAdjoint F : TimeProbabilityL2) |>.comp (cut_tendsto (predictableAdjoint F))
  have he (n : ℕ) : GaussianContinuousRigidity.integralExtension
      (cut (n : ℝ≥0) (predictableAdjoint F)) =
      pastProjection (n : ℝ≥0) F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
    change GaussianContinuousRigidity.integralExtension
      (predictableCut (n : ℝ≥0) (predictableAdjoint F)) = _
    rw [GaussianContinuousRigidity.integralExtension_eq, past_representation _ F hF]
  simp only [Function.comp_def, he, GaussianContinuousRigidity.integralExtension_eq,
    brownian_representation F hF] at ht
  have ha := ht.add (tendsto_const_nhds
    (x := (∫ ω, F ω ∂gaussianProduct) • gaussianOne))
  simpa only [sub_add_cancel] using ha

end OperatorDerivativeRewrite.Foundation.GaussianConditionalClarkOcone
