import Foundation.GaussianHermiteRepresentation
import Foundation.GaussianQuadraticIto

/-! Identification of the constructed all-order Hermite integrand by actual
Gaussian L2 slices; no path-continuity version or stochastic limit is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianHermiteIntegrand
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteStochasticSums
open GaussianHermiteRepresentation GaussianBrownianQuadraticVariation GaussianPredictableFull
open GaussianTimeProductL2 GaussianProductDerivative GaussianTimeHilbert

theorem brownianCore_continuous (n : ℕ) : Continuous (fun t : ℝ≥0 => (brownianCore t n : GaussianL2)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : Continuous (fun s : ℝ≥0 => ‖(brownianCore s n : GaussianL2) - brownianCore t n‖ ^ 2) := by
    simp_rw [norm_sub_sq_real, brownianCore_norm_sq, brownianCore_inner]
    simp only [if_true]
    fun_prop
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (hc.continuousAt (x := t)).tendsto
  simp only [Function.comp_def, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hs

def stepValue (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (x : ℝ) : GaussianL2 :=
  ∑ i : Fin m, (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator
    (fun _ => (brownianCore (τ i.castSucc) n : GaussianL2)) x

theorem stepValue_on_interval (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ)
    (i : Fin m) (x : ℝ) (hx : x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)) :
    stepValue n τ x = brownianCore (τ i.castSucc) n := by
  rw [stepValue, Finset.sum_eq_single i, indicator_of_mem hx]
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    rcases lt_or_gt_of_ne hji with hjlt | hjgt
    · have hle : (τ j.succ : ℝ) ≤ τ i.castSucc := hτ (Fin.succ_le_castSucc_iff.mpr hjlt)
      linarith [hx.1, hj.2]
    · have hle : (τ i.succ : ℝ) ≤ τ j.castSucc := hτ (Fin.succ_le_castSucc_iff.mpr hjgt)
      linarith [hj.1, hx.2]
  · simp

theorem stepValue_outside (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ)
    (x : ℝ) (hx : x ∉ Ioc (τ 0 : ℝ) (τ (Fin.last m) : ℝ)) : stepValue n τ x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact hx ⟨lt_of_le_of_lt (hτ (Fin.zero_le _)) hi.1, hi.2.trans (hτ (Fin.le_last _))⟩

def horizonValue (n : ℕ) (T : ℝ≥0) (x : ℝ) : GaussianL2 :=
  (Ioc 0 (T : ℝ)).indicator (fun s => (brownianCore s.toNNReal n : GaussianL2)) x

theorem stepValue_tendsto (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    Tendsto (fun N => stepValue n (uniformTime T N) x) atTop (𝓝 (horizonValue n T x)) := by
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · choose i hi using fun N => GaussianQuadraticIto.uniformTime_covers T N x hx
    have hb (N : ℕ) : ‖(uniformTime T N (i N).castSucc : ℝ) - x‖ ≤ (T : ℝ) / (N + 1) := by
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hi N).1.le)]
      have hs := uniformTime_step T N (i N)
      linarith [(hi N).2]
    have ht : Tendsto (fun N : ℕ => (T : ℝ) / (N + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hr := tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun N => norm_nonneg _) hb ht)
    have hnn := continuous_real_toNNReal.continuousAt.tendsto.comp hr
    simp only [Function.comp_def, Real.toNNReal_coe] at hnn
    have hc := (brownianCore_continuous n).continuousAt.tendsto.comp hnn
    rw [horizonValue, indicator_of_mem hx]
    convert hc using 1
    funext N
    exact stepValue_on_interval n _ (uniformTime_monotone T N) (i N) x (hi N)
  · have hz (N : ℕ) : stepValue n (uniformTime T N) x = 0 := by
      apply stepValue_outside n _ (uniformTime_monotone T N) x
      simpa only [(uniformTime_endpoints T N).1, (uniformTime_endpoints T N).2,
        NNReal.coe_zero] using hx
    simp only [hz, horizonValue, indicator_of_notMem hx]
    exact tendsto_const_nhds

theorem scalarCurry_stepSum (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) :
    scalarCurry (stepSum n τ : TimeProbabilityL2) =ᵐ[volume] stepValue n τ := by
  rw [stepSum_coe, partitionL2, map_sum]
  simp only [scalarCurry_productTensor]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin m =>
    BochnerClosedOperator.tensor volume (intervalVector (τ i.castSucc) (τ i.succ))
      (brownianCore (τ i.castSucc) n : GaussianL2)), ae_all_iff.mpr (fun i : Fin m =>
        BochnerClosedOperator.tensor_coeFn volume (intervalVector (τ i.castSucc) (τ i.succ))
          (brownianCore (τ i.castSucc) n : GaussianL2)), ae_all_iff.mpr (fun i : Fin m =>
            intervalVector_coeFn (τ i.castSucc) (τ i.succ))] with x hs ht hi
  rw [hs]
  simp only [Finset.sum_apply, stepValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i, hi i]
  by_cases hx : x ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) <;> simp [hx]

theorem hermiteIntegrand_slices (n : ℕ) (T : ℝ≥0) :
    scalarCurry (hermiteIntegrand n T : TimeProbabilityL2) =ᵐ[volume] horizonValue n T := by
  have ht := (scalarCurry.continuous.comp continuous_subtype_val).continuousAt.tendsto.comp
    (stepSum_tendsto n T)
  obtain ⟨ns, hns, hn⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have ha := ae_all_iff.mpr (fun N => scalarCurry_stepSum n (uniformTime T N))
  filter_upwards [hn, ha] with x hn ha
  have hstep := (stepValue_tendsto n T x).comp hns.tendsto_atTop
  change Tendsto (fun N => scalarCurry (stepSum n (uniformTime T (ns N)) : TimeProbabilityL2) x)
    atTop (𝓝 (scalarCurry (hermiteIntegrand n T : TimeProbabilityL2) x)) at hn
  simp only [ha] at hn
  exact tendsto_nhds_unique hn hstep

theorem brownian_hermite_stochastic_identity (n : ℕ) (T : ℝ≥0) :
    (fun ω => value (n + 1) (GaussianTimeProcess.process T ω) T) =ᵐ[gaussianProduct]
      fun ω => (n + 1 : ℝ) * itoIntegral (hermiteIntegrand n T) ω := by
  have he := hermite_representation n T
  filter_upwards [brownianCore_coeFn T (n + 1),
    Lp.coeFn_smul (n + 1 : ℝ) (itoIntegral (hermiteIntegrand n T))] with ω hc hs
  have hi := congrArg (fun f : GaussianL2 => f ω) he
  rw [hc, hs] at hi
  exact hi

theorem hermiteIntegrand_integrable_sq (n : ℕ) (T : ℝ≥0) :
    Integrable (fun z => ((hermiteIntegrand n T : TimeProbabilityL2) z) ^ 2)
      (volume.prod gaussianProduct) := (Lp.memLp _).integrable_sq

theorem hermiteIntegrand_zero_time (n : ℕ) : hermiteIntegrand n 0 = 0 := by
  have hn : (brownianCore 0 (n + 1) : GaussianL2) = 0 := by
    have h := brownianCore_norm_sq 0 (n + 1)
    simp only [NNReal.coe_zero, zero_pow (Nat.succ_ne_zero n), mul_zero] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (brownianCore 0 (n + 1) : GaussianL2)])
  simp [hermiteIntegrand, hn]

theorem integral_hermiteIntegrand_order_one (T : ℝ≥0) :
    itoIntegral (hermiteIntegrand 0 T) = GaussianTimeProcess.wienerL2 T := by
  rw [integral_hermiteIntegrand]
  norm_num
  apply Lp.ext
  simpa only [value_one, GaussianTimeProcess.process] using brownianCore_coeFn T 1

theorem hermiteIntegrand_order_two (T : ℝ≥0) :
    hermiteIntegrand 1 T = GaussianQuadraticRepresentation.quadraticIntegrand T := by
  have he : (brownianCore T 2 : GaussianL2) = GaussianQuadraticRepresentation.terminalSquare T := by
    apply Lp.ext
    exact (brownianCore_coeFn T 2).trans (by
      simpa only [value_two] using (GaussianQuadraticRepresentation.terminalSquare_coeFn T).symm)
  simp only [hermiteIntegrand, GaussianQuadraticRepresentation.quadraticIntegrand]
  norm_num
  rw [he]

end OperatorDerivativeRewrite.Foundation.GaussianHermiteIntegrand
