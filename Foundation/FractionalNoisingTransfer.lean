import Foundation.GaussianIntegratedProductCalibration
import Foundation.FractionalForcingKernel

/-! C1 deterministic noising through actual Gaussian Hilbert realizations,
with an explicit Brownian counterexample to confusing a Wiener transfer with
the ordinary L2 adjoint of the primitive Volterra operator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalNoisingTransfer
open InfiniteGaussian GaussianTimeHilbert GaussianHilbertProcess
open IntegratedBrownianStatePrediction
attribute [local instance] timeHilbert_secondCountable

/-- Integration-by-parts profile for a zero-initial kernel curve, with q=f'.
The algebra below states its actual domain explicitly and does not infer a
pathwise stochastic integral from a formal operator name. -/
def weightedVector (k : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0) : TimeHilbert :=
  f T • k T - ∫ s in 0..(T : ℝ), q s • k s

def weightedObservable (k : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0) : GaussianL2 :=
  f T • isonormalEmbedding TimeHilbert (k T) -
    ∫ s in 0..(T : ℝ), q s • isonormalEmbedding TimeHilbert (k s)

theorem weighted_realization (k : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0)
    (hi : IntervalIntegrable (fun s => q s • k s) volume 0 T) :
    weightedObservable k f q T = isonormalEmbedding TimeHilbert (weightedVector k f q T) := by
  let L := (isonormalEmbedding TimeHilbert).toContinuousLinearMap
  have he := L.intervalIntegral_comp_comm hi
  simp only [map_smul] at he
  change (∫ x in 0..(T : ℝ), q x • isonormalEmbedding TimeHilbert (k x)) =
    isonormalEmbedding TimeHilbert (∫ x in 0..(T : ℝ), q x • k x) at he
  rw [weightedObservable, he, weightedVector, map_sub, map_smul]

theorem weighted_norm (k : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0)
    (hi : IntervalIntegrable (fun s => q s • k s) volume 0 T) :
    ‖weightedObservable k f q T‖ = ‖weightedVector k f q T‖ := by
  rw [weighted_realization k f q T hi, LinearIsometry.norm_map]

theorem weighted_law (k : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0)
    (hi : IntervalIntegrable (fun s => q s • k s) volume 0 T) :
    gaussianProduct.map (weightedObservable k f q T) =
      gaussianReal 0 ⟨‖weightedVector k f q T‖^2, sq_nonneg _⟩ := by
  rw [weighted_realization k f q T hi]
  exact isonormal_law _

theorem weighted_closed_derivative (k : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0)
    (hi : IntervalIntegrable (fun s => q s • k s) volume 0 T) :
    (weightedObservable k f q T, GaussianContinuousRigidity.fieldEmbedding
      (GaussianTimeProductL2.productTensor (weightedVector k f q T) gaussianOne)) ∈
        closedCylindricalDerivative.graph := by
  rw [weighted_realization k f q T hi]
  exact GaussianDeterministicIntegral.firstChaos_closedDerivative_graph _

theorem weighted_constant (k : ℝ → TimeHilbert) (T : ℝ≥0) :
    weightedVector k (fun _ => 1) (fun _ => 0) T = k T := by
  simp [weightedVector]

theorem weighted_norm_bound (k : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0)
    (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hk : ∀ s ∈ Icc 0 (T : ℝ), ‖k s‖ ≤ ε)
    (hq : ∀ s ∈ Icc 0 (T : ℝ), |q s| ≤ M) :
    ‖weightedVector k f q T‖ ≤ (|f T| + M * T) * ε := by
  have hT : (T : ℝ) ∈ Icc 0 (T : ℝ) := ⟨T.coe_nonneg, le_rfl⟩
  have hb : ∀ s ∈ uIoc 0 (T : ℝ), ‖q s • k s‖ ≤ M * ε := by
    intro s hs
    rw [uIoc_of_le T.coe_nonneg] at hs
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hq s ⟨hs.1.le, hs.2⟩) (hk s ⟨hs.1.le, hs.2⟩)
      (norm_nonneg _) hM
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simp only [sub_zero, abs_of_nonneg T.coe_nonneg] at hi
  calc
    ‖weightedVector k f q T‖ ≤ ‖f T • k T‖ + ‖∫ s in 0..(T : ℝ), q s • k s‖ := norm_sub_le _ _
    _ ≤ |f T| * ε + (M * ε) * T := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left (hk T hT) (abs_nonneg _)) hi
    _ = _ := by ring

theorem weighted_sub (k l : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0)
    (hk : IntervalIntegrable (fun s => q s • k s) volume 0 T)
    (hl : IntervalIntegrable (fun s => q s • l s) volume 0 T) :
    weightedVector k f q T - weightedVector l f q T =
      weightedVector (fun s => k s-l s) f q T := by
  simp only [weightedVector, smul_sub]
  rw [intervalIntegral.integral_sub hk hl]
  abel

theorem weighted_error (k l : ℝ → TimeHilbert) (f q : ℝ → ℝ) (T : ℝ≥0)
    (hk : IntervalIntegrable (fun s => q s • k s) volume 0 T)
    (hl : IntervalIntegrable (fun s => q s • l s) volume 0 T)
    (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (he : ∀ s ∈ Icc 0 (T : ℝ), ‖k s-l s‖ ≤ ε)
    (hq : ∀ s ∈ Icc 0 (T : ℝ), |q s| ≤ M) :
    ‖weightedObservable k f q T-weightedObservable l f q T‖ ≤
      (|f T| + M * T) * ε := by
  rw [weighted_realization k f q T hk, weighted_realization l f q T hl,
    ← map_sub, LinearIsometry.norm_map, weighted_sub k l f q T hk hl]
  exact weighted_norm_bound _ f q T M ε hM hε he hq

/-- Uniform deterministic kernel control transfers to genuine observable L2
convergence. A terminal-only error bound is not substituted for this hypothesis. -/
theorem weighted_convergence (k : ℕ → ℝ → TimeHilbert) (l : ℝ → TimeHilbert)
    (f q : ℝ → ℝ) (T : ℝ≥0)
    (hk : ∀ n, IntervalIntegrable (fun s => q s • k n s) volume 0 T)
    (hl : IntervalIntegrable (fun s => q s • l s) volume 0 T)
    (M : ℝ) (hM : 0 ≤ M) (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (he : ∀ n s, s ∈ Icc 0 (T : ℝ) → ‖k n s-l s‖ ≤ ε n)
    (hq : ∀ s ∈ Icc 0 (T : ℝ), |q s| ≤ M)
    (hlim : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => weightedObservable (k n) f q T) Filter.atTop
      (nhds (weightedObservable l f q T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n =>
    weighted_error (k n) l f q T (hk n) hl M (ε n) hM (hε n) (he n) hq)
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul hlim : Filter.Tendsto
      (fun n => (|f T| + M * T) * ε n) Filter.atTop (nhds ((|f T| + M * T) * 0)))

/-- The actual Brownian Wiener-integral profile of 1_(0,T] is the indicator. -/
theorem brownian_transfer_constant (T : ℝ≥0) :
    GaussianPowerVolterra.vector 0 (by norm_num) T = timeVector T :=
  GaussianPowerVolterra.vector_exponent_zero T

/-- The ordinary Volterra L2-adjoint kernel on the constant test is a ramp. -/
theorem ordinary_adjoint_constant (T : ℝ≥0) :
    integratedVector T =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator
      (fun s => ∫ t in s..(T : ℝ), (1 : ℝ)) := by
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using
    integratedVector_coeFn T

theorem ramp_energy (T : ℝ≥0) : ‖integratedVector T‖^2 = (T : ℝ)^3 / 3 := by
  change ‖GaussianPowerVolterra.vector 1 (by norm_num) T‖^2 = _
  rw [GaussianPowerVolterra.vector_norm_sq,
    show (2 * (1 : ℝ) + 1) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

theorem ramp_indicator_pairing (T : ℝ≥0) :
    inner ℝ (integratedVector T) (timeVector T) = (T : ℝ)^2/2 := by
  rw [L2_inner_eq_integral]
  have he : (fun x => inner ℝ (integratedVector T x) (timeVector T x)) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun x => (T : ℝ)-x) := by
    filter_upwards [integratedVector_coeFn T, timeVector_coeFn T] with x hr hb
    rw [hr,hb]
    by_cases hx : x ∈ Ioc 0 (T : ℝ) <;> simp [hx,Real.inner_apply]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le T.coe_nonneg]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => (T : ℝ)*y-y^2/2) ((T : ℝ)-x) x := by
    convert ((hasDerivAt_id x).const_mul (T : ℝ)).sub
      (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
      (try funext y) <;> simp only [id_eq, Pi.pow_apply, Pi.sub_apply] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((continuous_const.sub continuous_id).intervalIntegrable _ _)]
  ring

theorem profile_error (T : ℝ≥0) :
    ‖integratedVector T-timeVector T‖^2 = (T : ℝ)^3/3-(T : ℝ)^2+T := by
  rw [norm_sub_sq_real, ramp_energy, timeVector_norm_sq, ramp_indicator_pairing]
  ring

theorem profile_error_lower (T : ℝ≥0) :
    (T : ℝ)/4 ≤ ‖integratedVector T-timeVector T‖^2 := by
  rw [profile_error]
  nlinarith [mul_nonneg T.coe_nonneg (sq_nonneg ((T : ℝ)-3/2))]

theorem profile_mismatch : integratedVector 1 ≠ timeVector 1 := by
  intro he
  have hn := congrArg (fun x : TimeHilbert => ‖x‖^2) he
  rw [ramp_energy, timeVector_norm_sq] at hn
  norm_num at hn

/-- This is an actual Gaussian random variable, not a formal kernel symbol. -/
def wrongTransfer (T : ℝ≥0) : GaussianL2 :=
  isonormalEmbedding TimeHilbert (integratedVector T)

theorem wrong_transfer_energy (T : ℝ≥0) : ‖wrongTransfer T‖^2 = (T : ℝ)^3 / 3 := by
  rw [wrongTransfer, LinearIsometry.norm_map, ramp_energy]

theorem brownian_energy (T : ℝ≥0) : ‖GaussianTimeProcess.wienerL2 T‖^2 = (T : ℝ) := by
  rw [GaussianTimeProcess.wienerL2, LinearIsometry.norm_map, timeVector_norm_sq]

theorem stochastic_error (T : ℝ≥0) :
    ‖wrongTransfer T-GaussianTimeProcess.wienerL2 T‖^2 = (T : ℝ)^3/3-(T : ℝ)^2+T := by
  rw [wrongTransfer, GaussianTimeProcess.wienerL2, ← map_sub, LinearIsometry.norm_map,
    profile_error]

theorem stochastic_error_lower (T : ℝ≥0) :
    (T : ℝ)/4 ≤ ‖wrongTransfer T-GaussianTimeProcess.wienerL2 T‖^2 := by
  rw [stochastic_error, ← profile_error]
  exact profile_error_lower T

theorem stochastic_mismatch_positive (T : ℝ≥0) (hT : 0 < T) :
    wrongTransfer T ≠ GaussianTimeProcess.wienerL2 T := by
  intro he
  have h := stochastic_error_lower T
  rw [he,sub_self,norm_zero] at h
  have ht : (0 : ℝ) < T := hT
  norm_num at h
  linarith

theorem stochastic_mismatch : wrongTransfer 1 ≠ GaussianTimeProcess.wienerL2 1 := by
  intro he
  have hn := congrArg (fun x : GaussianL2 => ‖x‖^2) he
  rw [wrong_transfer_energy, brownian_energy] at hn
  norm_num at hn

theorem stochastic_not_ae : ¬ wrongTransfer 1 =ᵐ[gaussianProduct] GaussianTimeProcess.wienerL2 1 := by
  intro he
  exact stochastic_mismatch (Lp.ext he)

/-- The mistaken replacement gives the time integral of Brownian motion. -/
theorem wrong_transfer_is_time_integral (T : ℝ≥0) :
    wrongTransfer T = ∫ s in 0..(T : ℝ), GaussianTimeProcess.wienerL2 s.toNNReal := by
  exact (GaussianIntegratedProductCalibration.bochner_brownian_eq_ramp T).symm

/-- Literal scalar pairing test of J*1=1 on the unit interval. -/
theorem primitive_pairing : (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, (1 : ℝ)) = 1/2 := by
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y^2/2) x x := by
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;> (try funext y) <;> simp only [id_eq, Pi.pow_apply] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (continuous_id.intervalIntegrable _ _)]
  norm_num

theorem ordinary_adjoint_not_identity :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t, (1 : ℝ)) ≠ ∫ t in (0 : ℝ)..1, (1 : ℝ) := by
  rw [primitive_pairing]
  norm_num

/-- If alpha is defined before the integrating factor, it must be rescaled. -/
theorem normalization_energy (c : ℝ) (a : TimeHilbert) :
    ‖isonormalEmbedding TimeHilbert (c • a)‖^2 = c^2 * ‖a‖^2 := by
  rw [LinearIsometry.norm_map, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem normalization_counterexample :
    ‖isonormalEmbedding TimeHilbert ((2 : ℝ) • timeVector 1)‖^2 = 4 ∧
      ‖isonormalEmbedding TimeHilbert (timeVector 1)‖^2 = 1 := by
  constructor
  · rw [normalization_energy, timeVector_norm_sq]; norm_num
  · rw [LinearIsometry.norm_map, timeVector_norm_sq]; norm_num

/-- Actual Gamma-normalized Riemann-Liouville noising, with the manuscript's
normalization, built from the existing verified fractional response. -/
def typeII (H : ℝ) (hH : 0 < H) (T : ℝ≥0) : GaussianL2 :=
  FractionalForcingKernel.stochasticResponse (H+1/2) (by linarith) T

theorem typeII_energy (H : ℝ) (hH : 0 < H) (T : ℝ≥0) :
    ‖typeII H hH T‖^2 = (T : ℝ)^(2*H) / ((Real.Gamma (H+1/2))^2 * (2*H)) := by
  rw [typeII, FractionalForcingKernel.stochasticResponse_norm_sq,
    show 2*(H+1/2)-1 = 2*H by ring]

theorem typeII_brownian (T : ℝ≥0) :
    typeII (1/2) (by norm_num) T = GaussianTimeProcess.wienerL2 T := by
  unfold typeII
  norm_num only [show (1/2+1/2 : ℝ) = 1 by norm_num]
  exact FractionalForcingKernel.stochasticResponse_order_one T

end OperatorDerivativeRewrite.Foundation.FractionalNoisingTransfer
