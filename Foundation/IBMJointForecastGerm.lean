import Foundation.IBMTerminalSelfRepresentation
import Foundation.IBMJointSceneryForecast
import Foundation.IBMObservedInitialGerm
import Foundation.FiniteMeasureL2Dominated

/-! Bounded actual IBM germ observables are fixed by every positive spatial
forecast. This permits nonlinear source-centered tests without claiming that
all germ observables are constant. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMJointForecastGerm
open InfiniteGaussian IBMIntrinsicOperators IBMTimeAveragedObservable IBMJointSceneryForecast
open IBMClippedSceneryForecast IBMBoundedGermFactors IBMIntrinsicRightGerm

attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

variable (δ s : ℝ≥0) (g : (Iic s → ℝ) → ℝ) (hg : Measurable g)
  (C : ℝ) (hb : ∀ p, |g p| ≤ C)

def clippedClass : JointL2 :=
  (MemLp.of_bound
    (hg.comp (Measurable.of_eval fun r => actual_measurable δ r)).aestronglyMeasurable C
    (ae_of_all _ fun _ => hb _)).toLp _

theorem clipped_actual : clippedClass δ s g hg C hb =ᵐ[IBMSourceLaws.jointMeasure]
    GaussianPredictableStep.pastCoefficient (actualValue δ) s g := MemLp.coeFn_toLp _

theorem source_sections (F : JointL2) : ∀ᵐ Y ∂gaussianProduct,
    sourceUnitary F Y =ᵐ[gaussianProduct] fun X => F (X,Y) := by
  have hu := ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct F)
  have hs := ae_ae_of_ae_prod (ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct F)
  filter_upwards [hu,hs] with Y hu hs
  exact hu.trans hs

theorem clipped_fixed : IBMJointSceneryForecast.forecast δ (clippedClass δ s g hg C hb) =
    clippedClass δ s g hg C hb := by
  apply (forecast_fixed_iff _ _).mpr
  have ha := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (clipped_actual δ s g hg C hb))
  filter_upwards [source_sections (clippedClass δ s g hg C hb),ha] with Y hs ha
  exact (past_functional_spatial_measurable δ s g hg Y).aestronglyMeasurable.congr
    (hs.trans ha).symm

omit s g hg C hb in
theorem bounded_germ_fixed (hδ : 0 < δ) (F : JointL2)
    (hF : F ∈ rightPast 0) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ p ∂IBMSourceLaws.jointMeasure, |F p| ≤ C) :
    IBMJointSceneryForecast.forecast δ F = F := by
  let τ := IBMIntrinsicRightApproach.approach 0
  obtain ⟨g,hg,hgb,hge⟩ := bounded_germ_factors F hF C hC hb τ
    (IBMIntrinsicRightApproach.approach_positive 0)
  let f (n : ℕ) := clippedClass δ (τ n) (g n) (hg n) C (hgb n)
  have ht : Tendsto f atTop (𝓝 F) := by
    apply FiniteMeasureL2Dominated.tendsto_of_constant_bound _ _ C hC
    · intro n
      filter_upwards [clipped_actual δ (τ n) (g n) (hg n) C (hgb n)] with p hp
      rw [hp,Real.norm_eq_abs]
      exact hgb n _
    · simpa only [Real.norm_eq_abs] using hb
    · have he := IBMClockGermLocalization.past_functional_tendsto δ hδ τ
        (IBMIntrinsicRightApproach.approach_tendsto 0) g F hge
      filter_upwards [he,ae_all_iff.mpr (fun n =>
        clipped_actual δ (τ n) (g n) (hg n) C (hgb n))] with p hp hq
      simpa only [f,hq] using hp
  have hp := (forecast_continuous δ).tendsto F |>.comp ht
  have he : (fun n => IBMJointSceneryForecast.forecast δ (f n)) = f := by
    funext n
    exact clipped_fixed δ (τ n) (g n) (hg n) C (hgb n)
  change Tendsto (fun n => IBMJointSceneryForecast.forecast δ (f n)) _ _ at hp
  rw [he] at hp
  exact tendsto_nhds_unique hp ht

omit s g hg C hb in
theorem bounded_germ_pairing (hδ : 0 < δ) (F G : JointL2)
    (hG : G ∈ rightPast 0) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ p ∂IBMSourceLaws.jointMeasure, |G p| ≤ C) :
    inner ℝ F G = inner ℝ (IBMJointSceneryForecast.forecast δ F) G := by
  rw [forecast_inner,bounded_germ_fixed δ hδ G hG C hC hb]

omit δ s g hg C hb in
theorem bounded_germ_limit_pairing (F : JointL2)
    (δ : ℕ → ℝ≥0) (hδ : ∀ n, 0 < δ n)
    (ht : Tendsto (fun n => IBMJointSceneryForecast.forecast (δ n) F) atTop
      (𝓝 (sourceMean F))) (G : JointL2) (hG : G ∈ rightPast 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ p ∂IBMSourceLaws.jointMeasure, |G p| ≤ C) :
    inner ℝ F G = inner ℝ (sourceMean F) G := by
  have hh : Tendsto (fun n => inner ℝ (IBMJointSceneryForecast.forecast (δ n) F) G)
      atTop (𝓝 (inner ℝ (sourceMean F) G)) := ht.inner (tendsto_const_nhds (x := G))
  have he : (fun n => inner ℝ (IBMJointSceneryForecast.forecast (δ n) F) G) =
      fun _ : ℕ => inner ℝ F G := by
    funext n
    exact (bounded_germ_pairing (δ n) (hδ n) F G hG C hC hb).symm
  rw [he] at hh
  exact tendsto_nhds_unique tendsto_const_nhds hh


omit δ s g hg C hb in
theorem initial_zero_of_bounded_pairings (F : JointL2)
    (hp : ∀ (G : JointL2), G ∈ rightPast 0 → ∀ (C : ℝ), 0 ≤ C →
      (∀ᵐ p ∂IBMSourceLaws.jointMeasure, |G p| ≤ C) → inner ℝ F G = 0) :
    IBMObservedTerminalMartingale.channelClass F 0 = 0 := by
  have hz (A : Set IBMSourceLaws.JointSample)
      (hA : MeasurableSet[IBMRightGermFiltration.germFiltration 0] A) :
      (∫ p in A, F p ∂IBMSourceLaws.jointMeasure) = 0 := by
    have hAm := IBMRightGermFiltration.germFiltration.le 0 A hA
    have hi : MemLp (A.indicator (fun _ => (1 : ℝ))) 2 IBMSourceLaws.jointMeasure :=
      (memLp_const (1 : ℝ)).indicator hAm
    let G : JointL2 := hi.toLp _
    have hGa : G =ᵐ[IBMSourceLaws.jointMeasure] A.indicator (fun _ => (1 : ℝ)) :=
      hi.coeFn_toLp
    have hm : StronglyMeasurable[IBMRightGermFiltration.germFiltration 0]
        (A.indicator (fun _ => (1 : ℝ))) := stronglyMeasurable_const.indicator hA
    have hG : G ∈ rightPast 0 := by
      rw [← IBMRightGermFiltration.germPast_eq 0]
      exact hm.aestronglyMeasurable.congr hGa.symm
    have hbG : ∀ᵐ p ∂IBMSourceLaws.jointMeasure, |G p| ≤ 1 := by
      filter_upwards [hGa] with p hp
      rw [hp]
      by_cases ha : p ∈ A <;> simp [Set.indicator,ha]
    have he := hp G hG 1 (by norm_num) hbG
    rw [L2.inner_def] at he
    rw [← integral_indicator hAm]
    convert he using 1
    apply integral_congr_ae
    filter_upwards [hGa] with p hp
    rw [Real.inner_apply,hp]
    by_cases ha : p ∈ A <;> simp [Set.indicator,ha]
  have hc : IBMSourceLaws.jointMeasure[F | IBMRightGermFiltration.germFiltration 0]
      =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
    symm
    apply ae_eq_condExp_of_forall_setIntegral_eq (IBMRightGermFiltration.germFiltration.le 0)
      ((Lp.memLp F).integrable (by norm_num))
    · intro A _ _
      exact (integrable_zero IBMSourceLaws.JointSample ℝ
        IBMSourceLaws.jointMeasure).integrableOn
    · intro A hA _
      simpa only [integral_zero] using (hz A hA).symm
    · exact stronglyMeasurable_const.aestronglyMeasurable
  apply Lp.ext
  exact (IBMRightGermFiltration.projection_ae 0 F).trans
    (hc.trans (Lp.coeFn_zero _ _ _).symm)

omit δ s g hg C hb in
theorem initial_centered_channel_zero (F : JointL2) (δ : ℕ → ℝ≥0)
    (hδ : ∀ n, 0 < δ n)
    (ht : Tendsto (fun n => IBMJointSceneryForecast.forecast (δ n) F) atTop
      (𝓝 (sourceMean F))) :
    IBMObservedTerminalMartingale.channelClass (F-sourceMean F) 0 = 0 := by
  apply initial_zero_of_bounded_pairings
  intro G hG C hC hb
  rw [inner_sub_left,bounded_germ_limit_pairing F δ hδ ht G hG C hC hb,sub_self]

omit δ s g hg C hb in
theorem ridge_initial_centered_channel_zero {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (r : ι → ℝ≥0) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    IBMObservedTerminalMartingale.channelClass
      (IBMFiniteRidgeObservation.jointClass a r hc hA -
        IBMNativeSourceRecovery.sourceVacuum (IBMFiniteRidgeObservation.jointClass a r hc hA))
      0 = 0 := by
  rw [← sourceMean_eq_sourceVacuum]
  exact initial_centered_channel_zero _ (IBMIntrinsicRightApproach.approach 0)
    (IBMIntrinsicRightApproach.approach_positive 0)
    (ridge_forecast_tendsto a r hc hA _ (IBMIntrinsicRightApproach.approach_tendsto 0))


omit δ s g hg C hb in
theorem ridge_initial_channel_eq_vacuum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (r : ι → ℝ≥0) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    IBMObservedTerminalMartingale.channelClass
      (IBMFiniteRidgeObservation.jointClass a r hc hA) 0 =
      IBMObservedTerminalMartingale.channelClass
        (IBMNativeSourceRecovery.sourceVacuum (IBMFiniteRidgeObservation.jointClass a r hc hA))
        0 := by
  have hz := ridge_initial_centered_channel_zero a r hc hA
  change (rightPast 0).starProjection (_-_) = 0 at hz
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

omit δ s g hg C hb in
theorem ridge_target_indexed_reconstruction {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (r : ι → ℝ≥0) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    let F := IBMFiniteRidgeObservation.jointClass a r hc hA
    IBMFullPredictableIntegral.integral F
      ((IBMFullPredictableIntegral.integral F).toContinuousLinearMap.adjoint F) =
        F-IBMObservedTerminalMartingale.channelClass (IBMNativeSourceRecovery.sourceVacuum F) 0 := by
  dsimp only
  rw [← ridge_initial_channel_eq_vacuum a r hc hA]
  exact IBMTerminalSelfRepresentation.target_indexed_reconstruction
    (IBMFiniteRidgeObservation.observation a r hc hA)

end OperatorDerivativeRewrite.Foundation.IBMJointForecastGerm
