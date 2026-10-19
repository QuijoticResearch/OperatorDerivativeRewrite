import Foundation.IBMRegularizedPredictableSlices
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Strong time-L2 convergence of the ACTUAL regularized predictable IBM
fields, with an explicitly integrable singular time-zero majorant. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRegularizedTimeLimit
open InfiniteGaussian GaussianClockValueOperators GaussianPredictableSourceSlices
open IBMRegularizedPredictableSlices IBMRegularizedStochasticIdentity IBMNormalizedClockProfiles
open IBMClockRegularizedSlope GaussianSourceClockIto
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance (T : ℝ≥0) : CompleteSpace (Domain T) :=
  (isClosed_aestronglyMeasurable
    (PredictableRealL2.predictable_le GaussianTimeProcess.naturalFiltration)).completeSpace_coe

def majorant (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) (T : ℝ)).indicator
    (fun t => slopeBound g ^ 2 * absoluteMoment / Real.sqrt t) t

theorem majorant_integrable (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) :
    Integrable (majorant g T) volume := by
  have hr : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) volume 0 (T : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hi : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) (Ioc (0 : ℝ) (T : ℝ)) volume := by
    rwa [intervalIntegrable_iff,uIoc_of_le T.coe_nonneg] at hr
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  apply IntegrableOn.congr_fun (hi.const_mul (slopeBound g ^ 2 * absoluteMoment))
    (fun t ht => ?_) measurableSet_Ioc
  rw [Real.rpow_neg ht.1.le,← Real.sqrt_eq_rpow]
  exact (div_eq_mul_inv _ _).symm

def limitValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (t : ℝ) : Field :=
  (Ioc (0 : ℝ) (T : ℝ)).indicator (fun t => recoveredSlopeLimit g a t.toNNReal) t

theorem limitValue_measurable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    AEStronglyMeasurable (limitValue g a T) volume :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => Lp.aestronglyMeasurable (sourceCurry (zeroExtend T (stochasticField g a n T))))
    (predictable_slices_tendsto g a T)

theorem limitValue_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ t ∂volume, ‖limitValue g a T t‖ ^ 2 ≤ majorant g T t := by
  filter_upwards [predictable_slices_tendsto g a T,
    ae_all_iff.mpr (fun n => predictable_slice_uniform_energy g a n T)] with t ht hb
  exact le_of_tendsto (ht.norm.pow 2) (Eventually.of_forall hb)

theorem limitValue_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    MemLp (limitValue g a T) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (limitValue_measurable g a T)).mpr
  apply (majorant_integrable g T).mono' ((limitValue_measurable g a T).norm.pow 2)
  filter_upwards [limitValue_energy g a T] with t ht
  change ‖‖limitValue g a T t‖ ^ 2‖ ≤ majorant g T t
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using ht

def limitClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : Lp Field 2 (volume : Measure ℝ) :=
  (limitValue_memLp g a T).toLp _

/-- Genuine strong time-clock-source L2 convergence, including time zero. -/
theorem slices_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => sourceCurry (zeroExtend T (stochasticField g a n T))) atTop
      (𝓝 (limitClass g a T)) := by
  let f := fun n => sourceCurry (zeroExtend T (stochasticField g a n T))
  let q := limitClass g a T
  have hq : q =ᵐ[volume] limitValue g a T := (limitValue_memLp g a T).coeFn_toLp
  have hqb : ∀ᵐ t ∂volume, ‖q t‖ ^ 2 ≤ majorant g T t := by
    filter_upwards [hq,limitValue_energy g a T] with t hq hb
    rwa [hq]
  have hi := tendsto_integral_of_dominated_convergence (fun t => 4 * majorant g T t)
    (F := fun n t => ‖f n t - q t‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun n => ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable q)).norm.pow 2)
    ((majorant_integrable g T).const_mul 4) (fun n => ?_) ?_
  · have he (n : ℕ) : ‖f n - q‖ ^ 2 = ∫ t, ‖f n t - q t‖ ^ 2 := by
      rw [BochnerL2Dominated.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (f n) q] with t ht
      simp only [ht,Pi.sub_apply]
    simp only [integral_zero] at hi
    have hn : Tendsto (fun n => ‖f n - q‖ ^ 2) atTop (𝓝 0) := by
      simpa only [he] using hi
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hs
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hs
  · filter_upwards [predictable_slice_uniform_energy g a n T,hqb] with t hf hb
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hh := norm_sub_le (f n t) (q t)
    change ‖f n t‖ ^ 2 ≤ majorant g T t at hf
    nlinarith [norm_nonneg (f n t - q t),norm_nonneg (f n t),norm_nonneg (q t),
      sq_nonneg (‖f n t‖ - ‖q t‖)]
  · filter_upwards [predictable_slices_tendsto g a T,hq] with t ht hq
    change Tendsto (fun n => f n t) atTop (𝓝 (limitValue g a T t)) at ht
    rw [← hq] at ht
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using
      ((ht.sub (tendsto_const_nhds (x := q t))).norm.pow 2)

/-- The limit belongs to the ORIGINAL independently specified predictable
domain, using closedness of the actual source/time-section isometry range. -/
theorem exists_predictable_limit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∃ u : Domain T, Tendsto (fun n => stochasticField g a n T) atTop (𝓝 u) ∧
      sourceCurry (zeroExtend T u) = limitClass g a T := by
  let J := sourceCurry.toLinearIsometry.comp (zeroExtend T)
  have hs := slices_tendsto g a T
  have hm : limitClass g a T ∈ Set.range J :=
    J.isometry.isClosedEmbedding.isClosed_range.mem_of_tendsto hs
      (Eventually.of_forall fun n => ⟨stochasticField g a n T,rfl⟩)
  obtain ⟨u,hu⟩ := hm
  refine ⟨u,?_,hu⟩
  apply J.isometry.tendsto_nhds_iff.mpr
  rwa [hu]

/-- The actual mollified boundary-plus-curvature corrections converge in
the SAME common injective clock-number topology, together with a genuine
predictable stochastic limit realizing the unmollified endpoint recovery. -/
theorem exists_stochastic_reconstruction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∃ (u : Domain T) (c : Field),
      Tendsto (fun n => stochasticField g a n T) atTop (𝓝 u) ∧
      Tendsto (fun n => correction g a n T) atTop (𝓝 c) ∧
      sourceCurry (zeroExtend T u) = limitClass g a T ∧
      smoothing (IBMSchwartzFullReflectedIto.endpointLimitClass g a T) =
        GaussianSourceClockIto.integral T u + c := by
  obtain ⟨u,hu,hq⟩ := exists_predictable_limit g a T
  refine ⟨u,smoothing (IBMSchwartzFullReflectedIto.endpointLimitClass g a T) -
    GaussianSourceClockIto.integral T u,hu,correction_tendsto_of_field g a T u hu,hq,?_⟩
  abel

end OperatorDerivativeRewrite.Foundation.IBMRegularizedTimeLimit
