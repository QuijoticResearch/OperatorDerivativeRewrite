import Foundation.FractionalNoisingTransfer
import Foundation.GaussianProjectedDerivativeClosure

/-! Exact endpoint-plus-time-L2 transfer bound and a genuine adapted Brownian
obstruction to controlling weighted noising by terminal error alone. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalNoisingTopology
open InfiniteGaussian GaussianTimeHilbert GaussianHilbertProcess FractionalNoisingTransfer
open GaussianTimeSpaceHermite GaussianHermiteTimeIntegral GaussianIntegratedProductCalibration
open GaussianPredictableFull GaussianPredictableAdjoint
attribute [local instance] timeHilbert_secondCountable
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem weighted_L2_bound (k l : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0)
    (hk : IntervalIntegrable (fun s => q s • k s) volume 0 T)
    (hl : IntervalIntegrable (fun s => q s • l s) volume 0 T)
    (hq : MemLp q 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (he : MemLp (fun s => k s-l s) 2 (volume.restrict (Ioc 0 (T : ℝ)))) :
    ‖weightedObservable k f q T-weightedObservable l f q T‖ ≤
      |f T| * ‖k T-l T‖ +
        (∫ s in Ioc 0 (T : ℝ), |q s|^2)^(1/2 : ℝ) *
          (∫ s in Ioc 0 (T : ℝ), ‖k s-l s‖^2)^(1/2 : ℝ) := by
  rw [weighted_realization k f q T hk, weighted_realization l f q T hl,
    ← map_sub, LinearIsometry.norm_map, weighted_sub k l f q T hk hl]
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun s : ℝ => abs_nonneg (q s)))
    (μ := volume.restrict (Ioc 0 (T : ℝ)))
    (Filter.Eventually.of_forall (fun s : ℝ => norm_nonneg (k s-l s)))
    (by simpa [Real.norm_eq_abs] using hq.norm) (by simpa using he.norm)
  simp only [Real.rpow_two] at hh
  calc
    ‖weightedVector (fun s => k s-l s) f q T‖ ≤
        ‖f T • (k T-l T)‖ + ‖∫ s in 0..(T : ℝ), q s • (k s-l s)‖ := norm_sub_le _ _
    _ ≤ |f T| * ‖k T-l T‖ +
        ∫ s in Ioc 0 (T : ℝ), |q s| * ‖k s-l s‖ := by
      rw [norm_smul,Real.norm_eq_abs,intervalIntegral.integral_of_le T.coe_nonneg]
      apply add_le_add (le_refl _)
      simpa only [norm_smul,Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun s => q s • (k s-l s)) :
          ‖∫ s in Ioc 0 (T : ℝ), q s • (k s-l s)‖ ≤ _)
    _ ≤ _ := add_le_add (le_refl _) hh

/-- The exact missing two-part topology: endpoint L2 plus time-integrated L2. -/
theorem weighted_L2_convergence (k : ℕ → ℝ → TimeHilbert) (l : ℝ → TimeHilbert)
    (f q : ℝ → ℝ) (T : ℝ≥0)
    (hk : ∀ n, IntervalIntegrable (fun s => q s • k n s) volume 0 T)
    (hl : IntervalIntegrable (fun s => q s • l s) volume 0 T)
    (hq : MemLp q 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (he : ∀ n, MemLp (fun s => k n s-l s) 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hend : Filter.Tendsto (fun n => ‖k n T-l T‖) Filter.atTop (nhds 0))
    (htime : Filter.Tendsto (fun n => (∫ s in Ioc 0 (T : ℝ), ‖k n s-l s‖^2)^(1/2 : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => weightedObservable (k n) f q T) Filter.atTop
      (nhds (weightedObservable l f q T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => weighted_L2_bound (k n) l f q T (hk n) hl hq (he n))
  convert (tendsto_const_nhds.mul hend).add (tendsto_const_nhds.mul htime) using 1 <;> simp

/-- The deterministic kernel norm is the actual same-source Gaussian error norm. -/
theorem same_source_error (k l : ℝ → TimeHilbert) (T : ℝ≥0) :
    (∫ s in Ioc 0 (T : ℝ),
      ‖isonormalEmbedding TimeHilbert (k s)-isonormalEmbedding TimeHilbert (l s)‖^2) =
      ∫ s in Ioc 0 (T : ℝ), ‖k s-l s‖^2 := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    dsimp only
    rw [← map_sub,LinearIsometry.norm_map]

/-- A genuine adapted Gaussian error on the original Brownian source. -/
def errorProcess (t : ℝ≥0) (ω : SampleSpace) : ℝ :=
  (1-(t : ℝ))*GaussianTimeProcess.process t ω

def errorL2 (t : ℝ≥0) : GaussianL2 := (1-(t : ℝ)) • GaussianTimeProcess.wienerL2 t

theorem error_coeFn (t : ℝ≥0) : errorL2 t =ᵐ[gaussianProduct] errorProcess t := by
  filter_upwards [Lp.coeFn_smul (1-(t : ℝ)) (GaussianTimeProcess.wienerL2 t)] with ω hω
  change ((1-(t : ℝ)) • GaussianTimeProcess.wienerL2 t) ω =
    (1-(t : ℝ))*GaussianTimeProcess.wienerL2 t ω
  exact hω

theorem error_adapted : StronglyAdapted GaussianTimeProcess.naturalFiltration errorProcess := by
  intro t
  exact (GaussianTimeProcess.process_stronglyAdapted t).const_mul (1-(t : ℝ))

theorem error_gaussian : IsGaussianProcess errorProcess gaussianProduct := by
  convert (IsGaussianProcess.smul (fun t : ℝ≥0 => 1-(t : ℝ))
    GaussianTimeProcess.process_isGaussianProcess) using 1
  funext t ω
  rfl

theorem error_terminal : errorL2 1 = 0 := by simp [errorL2]

theorem error_energy (t : ℝ≥0) : ‖errorL2 t‖^2 = (1-(t : ℝ))^2 * t := by
  rw [errorL2,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,brownian_energy]

theorem error_integrable : IntervalIntegrable
    (fun s : ℝ => (1-s) • GaussianTimeProcess.wienerL2 s.toNNReal) volume 0 1 := by
  simpa only [brownianCore_one,NNReal.coe_one] using
    core_time_integrable (fun s : ℝ => 1-s) (continuous_const.sub continuous_id) 1 1

/-- Integration-by-parts weighted error for f(t)=t, E_0=E_1=0. -/
def weightedError : GaussianL2 :=
  -(∫ s in (0 : ℝ)..1, (1-s) • GaussianTimeProcess.wienerL2 s.toNNReal)

theorem weightedError_actual_integral : weightedError =
    itoIntegral (-integratedHermite (fun s : ℝ => 1-s) 0 1) := by
  rw [map_neg,integral_integratedHermite (fun s : ℝ => 1-s)
    (continuous_const.sub continuous_id) 0 1]
  simp only [Nat.cast_zero,zero_add,inv_one,one_smul,brownianCore_one,weightedError,NNReal.coe_one]

theorem weightedError_pairing : inner ℝ (GaussianTimeProcess.wienerL2 1) weightedError = -1/6 := by
  let L : GaussianL2 →L[ℝ] ℝ := innerSL ℝ (GaussianTimeProcess.wienerL2 1)
  have hm := L.intervalIntegral_comp_comm error_integrable
  change (∫ s in (0 : ℝ)..1,
    inner ℝ (GaussianTimeProcess.wienerL2 1) ((1-s) • GaussianTimeProcess.wienerL2 s.toNNReal)) =
      inner ℝ (GaussianTimeProcess.wienerL2 1)
        (∫ s in (0 : ℝ)..1, (1-s) • GaussianTimeProcess.wienerL2 s.toNNReal) at hm
  rw [weightedError,inner_neg_right,← hm]
  have he : (∫ s in (0 : ℝ)..1,
      inner ℝ (GaussianTimeProcess.wienerL2 1) ((1-s) • GaussianTimeProcess.wienerL2 s.toNNReal)) =
      ∫ s in (0 : ℝ)..1, (1-s)*s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    change inner ℝ (GaussianTimeProcess.wienerL2 1) ((1-s) • GaussianTimeProcess.wienerL2 s.toNNReal) = (1-s)*s
    rw [real_inner_smul_right,GaussianTimeProcess.wienerL2,GaussianTimeProcess.wienerL2,
      LinearIsometry.inner_map_map,GaussianTimeHilbert.timeVector_inner,
      Real.coe_toNNReal s hs.1,NNReal.coe_one,min_eq_right hs.2]
  rw [he]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y^2/2-y^3/3) ((1-x)*x) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 2).sub
      (((hasDerivAt_id x).pow 3).div_const 3) using 1 <;>
      (try funext y) <;> simp only [id_eq,Pi.pow_apply,Pi.sub_apply] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (((continuous_const.sub continuous_id).mul continuous_id).intervalIntegrable _ _)]
  norm_num

theorem weightedError_ne_zero : weightedError ≠ 0 := by
  intro he
  have h := weightedError_pairing
  rw [he,inner_zero_right] at h
  norm_num at h

theorem weightedError_norm_lower : (1/6 : ℝ) ≤ ‖weightedError‖ := by
  have hc := abs_real_inner_le_norm (GaussianTimeProcess.wienerL2 1) weightedError
  have hn : ‖GaussianTimeProcess.wienerL2 1‖ = 1 := by
    have h : ‖GaussianTimeProcess.wienerL2 1‖^2 = (1 : ℝ) := by
      simpa only [NNReal.coe_one] using brownian_energy 1
    nlinarith [norm_nonneg (GaussianTimeProcess.wienerL2 1)]
  rw [weightedError_pairing,hn,one_mul] at hc
  norm_num at hc
  exact hc

theorem no_terminal_only_bound (C : ℝ) : ¬ ‖weightedError‖ ≤ C * ‖errorL2 1‖ := by
  rw [error_terminal,norm_zero,mul_zero]
  intro he
  exact weightedError_ne_zero (norm_eq_zero.mp (le_antisymm he (norm_nonneg _)))

end OperatorDerivativeRewrite.Foundation.FractionalNoisingTopology
