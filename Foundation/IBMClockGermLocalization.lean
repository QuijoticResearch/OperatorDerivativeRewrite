import Foundation.IBMClippedSceneryForecast

/-! Actual shrinking-past agreement with a fixed clipped scenery process.
One source event and path continuity give simultaneous time agreement. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockGermLocalization
open InfiniteGaussian IBMConstructedSources IBMClippedSceneryForecast
set_option backward.isDefEq.respectTransparency false

theorem clock_zero_ae : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, clockPath ω.2 0 = 0 := by
  have hz := (clockPath_coordinate_ae 0).trans GaussianTimeProcess.process_zero_ae
  exact (measurePreserving_snd (μ := gaussianProduct)
    (ν := gaussianProduct)).quasiMeasurePreserving.ae hz

theorem clock_uniformly_small (δ : ℝ≥0) (hδ : 0 < δ)
    (τ : ℕ → ℝ≥0) (hτ : Tendsto τ atTop (𝓝 0)) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ∀ᶠ n in atTop,
      ∀ r ≤ τ n, |clockPath ω.2 r| ≤ (δ : ℝ) := by
  filter_upwards [clock_zero_ae] with ω hzero
  obtain ⟨η, hη, hb⟩ := Metric.continuousAt_iff.mp
    (show ContinuousAt (clockPath ω.2) 0 from (clockPath ω.2).continuous.continuousAt)
      (δ : ℝ) (by exact_mod_cast hδ)
  have ht : Tendsto (fun n => (τ n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).comp hτ
  filter_upwards [ht.eventually (eventually_lt_nhds hη)] with n hn
  intro r hr
  have hd : dist r 0 < η := by
    rw [NNReal.dist_eq]
    simpa only [NNReal.coe_zero, sub_zero, abs_of_nonneg r.coe_nonneg] using
      ((show (r : ℝ) ≤ τ n from hr).trans_lt hn)
  have hc := hb hd
  simpa only [hzero, Real.dist_eq, sub_zero] using hc.le

theorem eventually_past_agreement (δ : ℝ≥0) (hδ : 0 < δ)
    (τ : ℕ → ℝ≥0) (hτ : Tendsto τ atTop (𝓝 0)) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ∀ᶠ n in atTop,
      ∀ r ≤ τ n, actualValue δ r ω = ibmValue r ω := by
  filter_upwards [clock_uniformly_small δ hδ τ hτ] with ω hω
  filter_upwards [hω] with n hn
  exact actual_past_eq δ (τ n) ω hn

theorem past_functional_eventually_eq (δ : ℝ≥0) (hδ : 0 < δ)
    (τ : ℕ → ℝ≥0) (hτ : Tendsto τ atTop (𝓝 0))
    (g : (n : ℕ) → (Iic (τ n) → ℝ) → ℝ) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ∀ᶠ n in atTop,
      GaussianPredictableStep.pastCoefficient (actualValue δ) (τ n) (g n) ω =
        GaussianPredictableStep.pastCoefficient ibmValue (τ n) (g n) ω := by
  filter_upwards [eventually_past_agreement δ hδ τ hτ] with ω hω
  filter_upwards [hω] with n hn
  exact congrArg (g n) (funext fun r => hn r r.property)

theorem past_functional_tendsto (δ : ℝ≥0) (hδ : 0 < δ)
    (τ : ℕ → ℝ≥0) (hτ : Tendsto τ atTop (𝓝 0))
    (g : (n : ℕ) → (Iic (τ n) → ℝ) → ℝ) (f : IBMSourceLaws.JointSample → ℝ)
    (hf : ∀ n, GaussianPredictableStep.pastCoefficient ibmValue (τ n) (g n)
      =ᵐ[IBMSourceLaws.jointMeasure] f) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, Tendsto
      (fun n => GaussianPredictableStep.pastCoefficient (actualValue δ) (τ n) (g n) ω)
        atTop (𝓝 (f ω)) := by
  filter_upwards [past_functional_eventually_eq δ hδ τ hτ g, ae_all_iff.mpr hf] with ω he hfω
  have hh : ∀ᶠ n in atTop,
      GaussianPredictableStep.pastCoefficient (actualValue δ) (τ n) (g n) ω = f ω :=
    he.mono fun n hn => hn.trans (hfω n)
  exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hh)

end OperatorDerivativeRewrite.Foundation.IBMClockGermLocalization
