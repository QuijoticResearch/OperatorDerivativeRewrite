import Foundation.IBMCompactPredictableSlices

/-! The full continuum regularized stochastic limit, independent of the
positive compact profile, in the ORIGINAL native predictable time-L2 domain. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMDilatedPredictableLimit
open InfiniteGaussian GaussianClockValueOperators GaussianPredictableSourceSlices
open IBMCompactPredictableSlices IBMCompactClockRecovery IBMDilatedMollifier
open GaussianSourceClockIto
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def fieldAt (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) (ε : {x : ℝ // 0 < x}) : Domain T :=
  stochasticField g a (dilate_compact hc ε.property.ne') (dilate_contDiff hρ ε.val) T

def correctionAt (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) (ε : {x : ℝ // 0 < x}) : Field :=
  correction g a (dilate_compact hc ε.property.ne') (dilate_contDiff hρ ε.val) T

/-- Reuse the previously constructed unmollified predictable limit, once
and for all profiles, instead of choosing a separate process for each profile. -/
def fieldLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : Domain T :=
  Classical.choose (IBMRegularizedTimeLimit.exists_predictable_limit g a T)

theorem fieldLimit_slices (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    sourceCurry (zeroExtend T (fieldLimit g a T)) = IBMRegularizedTimeLimit.limitClass g a T :=
  (Classical.choose_spec (IBMRegularizedTimeLimit.exists_predictable_limit g a T)).2

theorem slices_sequence_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1)
    (ε : ℕ → {x : ℝ // 0 < x}) (hlim : Tendsto (fun n => (ε n).val) atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => sourceCurry (zeroExtend T (fieldAt g a hc hρ T (ε n)))) atTop
      (𝓝 (IBMRegularizedTimeLimit.limitClass g a T)) := by
  let f := fun n => sourceCurry (zeroExtend T (fieldAt g a hc hρ T (ε n)))
  let q := IBMRegularizedTimeLimit.limitClass g a T
  have hq : q =ᵐ[volume] IBMRegularizedTimeLimit.limitValue g a T :=
    (IBMRegularizedTimeLimit.limitValue_memLp g a T).coeFn_toLp
  have hqb : ∀ᵐ t ∂volume, ‖q t‖^2 ≤ IBMRegularizedTimeLimit.majorant g T t := by
    filter_upwards [hq,IBMRegularizedTimeLimit.limitValue_energy g a T] with t hq hb
    rwa [hq]
  have hfbound (n : ℕ) : ∀ᵐ t ∂volume, ‖f n t‖^2 ≤ IBMRegularizedTimeLimit.majorant g T t :=
    predictable_slice_uniform_energy g a (dilate_compact hc (ε n).property.ne')
      (dilate_contDiff hρ (ε n).val) (dilate_nonneg hpos (ε n).property)
      ((dilate_integral ρ (ε n).property).trans hmass) T
  have ht : ∀ᵐ t ∂volume, Tendsto (fun n => f n t) atTop
      (𝓝 (IBMRegularizedTimeLimit.limitValue g a T t)) := by
    filter_upwards [ae_all_iff.mpr (fun n => stochasticField_slices g a
      (dilate_compact hc (ε n).property.ne') (dilate_contDiff hρ (ε n).val) T)] with t hn
    change ∀ n, f n t = _ at hn
    simp only [hn,IBMRegularizedTimeLimit.limitValue]
    by_cases hs : t ∈ Ioc (0 : ℝ) (T : ℝ)
    · simp only [indicator_of_mem hs]
      exact (recoveredSlope_continuum_tendsto g a hc hρ hpos hmass t.toNNReal).comp
        (tendsto_comap_iff.mpr hlim)
    · simp only [indicator_of_notMem hs]
      exact tendsto_const_nhds
  have hi := tendsto_integral_of_dominated_convergence
    (fun t => 4*IBMRegularizedTimeLimit.majorant g T t)
    (F := fun n t => ‖f n t-q t‖^2) (f := fun _ => (0 : ℝ))
    (fun n => ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable q)).norm.pow 2)
    ((IBMRegularizedTimeLimit.majorant_integrable g T).const_mul 4) (fun n => ?_) ?_
  · have he (n : ℕ) : ‖f n-q‖^2 = ∫ t, ‖f n t-q t‖^2 := by
      rw [BochnerL2Dominated.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (f n) q] with t ht
      simp only [ht,Pi.sub_apply]
    simp only [integral_zero] at hi
    have hn : Tendsto (fun n => ‖f n-q‖^2) atTop (𝓝 0) := by simpa only [he] using hi
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hs
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hs
  · filter_upwards [hfbound n,hqb] with t hf hb
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hh := norm_sub_le (f n t) (q t)
    nlinarith [norm_nonneg (f n t-q t),norm_nonneg (f n t),norm_nonneg (q t),
      sq_nonneg (‖f n t‖-‖q t‖)]
  · filter_upwards [ht,hq] with t ht hq
    rw [← hq] at ht
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using
      ((ht.sub (tendsto_const_nhds (x := q t))).norm.pow 2)

/-- Strong convergence in the ORIGINAL predictable time-clock-source L2
space, for every positive width sequence and the same actual limit. -/
theorem field_sequence_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1)
    (ε : ℕ → {x : ℝ // 0 < x}) (hlim : Tendsto (fun n => (ε n).val) atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun n => fieldAt g a hc hρ T (ε n)) atTop (𝓝 (fieldLimit g a T)) := by
  let J := sourceCurry.toLinearIsometry.comp (zeroExtend T)
  apply J.isometry.tendsto_nhds_iff.mpr
  change Tendsto (fun n => sourceCurry (zeroExtend T (fieldAt g a hc hρ T (ε n)))) atTop
    (𝓝 (sourceCurry (zeroExtend T (fieldLimit g a T))))
  rw [fieldLimit_slices]
  exact slices_sequence_tendsto g a hc hρ hpos hmass ε hlim T

theorem field_continuum_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) :
    Tendsto (fieldAt g a hc hρ T)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0)) (𝓝 (fieldLimit g a T)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro ε hε
  exact field_sequence_tendsto g a hc hρ hpos hmass ε (tendsto_comap_iff.mp hε) T

def correctionLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : Field :=
  IBMRegularizedStochasticIdentity.smoothing (IBMSchwartzFullReflectedIto.endpointLimitClass g a T)-
    GaussianSourceClockIto.integral T (fieldLimit g a T)

/-- The ACTUAL boundary-plus-curvature corrections converge in the same
injective common dual topology, for all widths and all admissible profiles. -/
theorem correction_continuum_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) :
    Tendsto (correctionAt g a hc hρ T)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0)) (𝓝 (correctionLimit g a T)) := by
  change Tendsto (fun ε : {x : ℝ // 0 < x} => correctionAt g a hc hρ T ε) _ _
  have hh := (IBMRegularizedStochasticIdentity.smoothing.continuous.tendsto _ |>.comp
    (IBMDilatedEndpointLimit.endpoint_continuum_tendsto g a hc hρ hpos hmass T)).sub
      ((GaussianSourceClockIto.integral T).continuous.tendsto _ |>.comp
        (field_continuum_tendsto g a hc hρ hpos hmass T))
  simpa only [Function.comp_def,finite_stochastic_identity,add_sub_cancel_left,
    fieldAt,correctionAt,correctionLimit] using hh

/-- Actual full-source stochastic reconstruction; the theorem above proves
that the named correction is the limit of the original raw correction family. -/
theorem stochastic_reconstruction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    IBMRegularizedStochasticIdentity.smoothing (IBMSchwartzFullReflectedIto.endpointLimitClass g a T) =
      GaussianSourceClockIto.integral T (fieldLimit g a T)+correctionLimit g a T := by
  simp only [correctionLimit]
  abel

end OperatorDerivativeRewrite.Foundation.IBMDilatedPredictableLimit
