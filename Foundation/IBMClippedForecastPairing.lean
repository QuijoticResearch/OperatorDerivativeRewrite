import Foundation.IBMBoundedGermFactors

/-! Actual joint-probability pairings with bounded clipped-past observables. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClippedForecastPairing
open InfiniteGaussian IBMConstructedSources IBMTimeAveragedObservable
open IBMClippedSceneryForecast IBMBoundedGermFactors IBMDeterministicRangeObstruction
set_option backward.isDefEq.respectTransparency false

theorem ibm_memLp (t : ℝ≥0) : MemLp (ibmValue t) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (observed t)).ae_eq (observed_ae t)

theorem past_pairing (t δ s : ℝ≥0) (g : (Iic s → ℝ) → ℝ)
    (hg : Measurable g) (C : ℝ) (hb : ∀ p, |g p| ≤ C) :
    (∫ ω, ibmValue t ω * GaussianPredictableStep.pastCoefficient
      (actualValue δ) s g ω ∂IBMSourceLaws.jointMeasure) =
    ∫ ω, actualValue δ t ω * GaussianPredictableStep.pastCoefficient
      (actualValue δ) s g ω ∂IBMSourceLaws.jointMeasure := by
  let a := GaussianPredictableStep.pastCoefficient (actualValue δ) s g
  have hm : Measurable a := hg.comp (Measurable.of_eval fun r => actual_measurable δ r)
  have hbound : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a ω‖ ≤ C :=
    ae_of_all _ fun ω => hb _
  have hiA := ((ibm_memLp t).integrable (by norm_num)).mul_bdd
    hm.aestronglyMeasurable hbound
  have hiB := ((actual_memLp δ t).integrable (by norm_num)).mul_bdd
    hm.aestronglyMeasurable hbound
  change (∫ ω, ibmValue t ω * a ω ∂IBMSourceLaws.jointMeasure) =
    ∫ ω, actualValue δ t ω * a ω ∂IBMSourceLaws.jointMeasure
  rw [IBMSourceLaws.jointMeasure, integral_prod_symm _ hiA, integral_prod_symm _ hiB]
  apply integral_congr_ae
  filter_upwards [hiA.prod_left_ae, IBMUnmollifiedSourceDerivative.actual_section_domain t,
    actual_section_prediction t δ] with ωY hia hdom hpred
  have hma := past_functional_spatial_measurable δ s g hg ωY
  have hce := condExp_mul_of_stronglyMeasurable_right hma.stronglyMeasurable
    hia (hdom.choose.integrable (by norm_num))
  calc
    (∫ ωX, ibmValue t (ωX,ωY) * a (ωX,ωY) ∂gaussianProduct) =
        ∫ ωX, gaussianProduct[fun ωX => ibmValue t (ωX,ωY) * a (ωX,ωY) |
          IBMSpatialSceneryForecast.history δ] ωX ∂gaussianProduct :=
      (integral_condExp (IBMSpatialSceneryForecast.history.le δ)).symm
    _ = ∫ ωX, actualValue δ t (ωX,ωY) * a (ωX,ωY) ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [hce, hpred] with ωX he hp
      exact he.trans (congrArg (fun x => x * a (ωX,ωY)) hp)

theorem germ_pairing (t δ : ℝ≥0) (hδ : 0 < δ) (f : JointL2)
    (hf : f ∈ IBMIntrinsicRightGerm.rightPast 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |f ω| ≤ C) :
    inner ℝ (observed t) f = inner ℝ (forecast t δ) f := by
  let τ := IBMIntrinsicRightApproach.approach 0
  obtain ⟨g, hg, hgb, hge⟩ := bounded_germ_factors f hf C hC hb τ
    (IBMIntrinsicRightApproach.approach_positive 0)
  have hτ := IBMIntrinsicRightApproach.approach_tendsto 0
  have ha := localized_pairing_tendsto δ hδ τ hτ g hg C hgb f hge
    (ibmValue t) ((ibm_memLp t).integrable (by norm_num))
  have hc := localized_pairing_tendsto δ hδ τ hτ g hg C hgb f hge
    (actualValue δ t) ((actual_memLp δ t).integrable (by norm_num))
  have he : (∫ ω, ibmValue t ω * f ω ∂IBMSourceLaws.jointMeasure) =
      ∫ ω, actualValue δ t ω * f ω ∂IBMSourceLaws.jointMeasure := by
    apply tendsto_nhds_unique ha
    exact hc.congr' (Eventually.of_forall fun n => (past_pairing t δ (τ n) (g n) (hg n) C
      (hgb n)).symm)
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ ω, inner ℝ (observed t ω) (f ω) ∂IBMSourceLaws.jointMeasure) =
        ∫ ω, ibmValue t ω * f ω ∂IBMSourceLaws.jointMeasure := by
      apply integral_congr_ae
      filter_upwards [observed_ae t] with ω ho
      simp only [Real.inner_apply, ho]
    _ = ∫ ω, actualValue δ t ω * f ω ∂IBMSourceLaws.jointMeasure := he
    _ = ∫ ω, inner ℝ (forecast t δ ω) (f ω) ∂IBMSourceLaws.jointMeasure := by
      apply integral_congr_ae
      filter_upwards [forecast_actual_ae t δ] with ω ho
      simp only [Real.inner_apply, ho]

theorem bounded_germ_orthogonal (t : ℝ≥0) (f : JointL2)
    (hf : f ∈ IBMIntrinsicRightGerm.rightPast 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |f ω| ≤ C) :
    inner ℝ (observed t) f = 0 := by
  let δ := IBMIntrinsicRightApproach.approach 0
  have hl : Tendsto (fun n => inner ℝ (forecast t (δ n)) f) atTop
      (𝓝 (inner ℝ (0 : JointL2) f)) := (forecast_tendsto_zero t δ
    (IBMIntrinsicRightApproach.approach_tendsto 0)).inner
      (tendsto_const_nhds (x := f))
  have hz : Tendsto (fun n => inner ℝ (forecast t (δ n)) f) atTop (𝓝 0) := by
    simpa only [inner_zero_left] using hl
  have hc : Tendsto (fun _ : ℕ => inner ℝ (observed t) f) atTop (𝓝 0) :=
    hz.congr' (Eventually.of_forall fun n =>
      (germ_pairing t (δ n) (IBMIntrinsicRightApproach.approach_positive 0 n) f hf C hC hb).symm)
  exact tendsto_nhds_unique tendsto_const_nhds hc

end OperatorDerivativeRewrite.Foundation.IBMClippedForecastPairing
